/*!
\file
\brief Routines for k-way refinement

\date Started 7/28/97
\author George
\author Copyright 1997-2009, Regents of the University of Minnesota
\version $Id: kwayfm.c 17513 2014-08-05 16:20:50Z dominique $
*/

#include "metislib.h"
#include <stdio.h>

/*************************************************************************/
/* Top-level routine for k-way partitioning refinement. This routine just
   calls the appropriate refinement routine based on the objectives and
   constraints. */
/*************************************************************************/
void Greedy_KWayOptimize(ctrl_t *ctrl, graph_t *graph, idx_t niter,
                         real_t ffactor, idx_t omode) {
  switch (ctrl->objtype) {
  case METIS_OBJTYPE_MOBJ:
    Greedy_MObjKWayCutOptimize(ctrl, graph, niter, ffactor, omode);
    break;

  case METIS_OBJTYPE_CUT:
    if (graph->ncon == 1)
      Greedy_KWayCutOptimize(ctrl, graph, niter, ffactor, omode);
    else
      Greedy_McKWayCutOptimize(ctrl, graph, niter, ffactor, omode);
    break;

  case METIS_OBJTYPE_VOL:
    if (graph->ncon == 1)
      Greedy_KWayVolOptimize(ctrl, graph, niter, ffactor, omode);
    else
      Greedy_McKWayVolOptimize(ctrl, graph, niter, ffactor, omode);
    break;

  default:
    gk_errexit(SIGERR, "Unknown objtype of %d\n", ctrl->objtype);
  }
}

/*************************************************************************/
/*! K-way partitioning optimization in which the vertices are visited in
    decreasing ed/sqrt(nnbrs)-id order. Note this is just an
    approximation, as the ed is often split across different subdomains
    and the sqrt(nnbrs) is just a crude approximation.

  \param graph is the graph that is being refined.
  \param niter is the number of refinement iterations.
  \param ffactor is the \em fudge-factor for allowing positive gain moves
         to violate the max-pwgt constraint.
  \param omode is the type of optimization that will performed among
         OMODE_REFINE and OMODE_BALANCE

*/
/**************************************************************************/
void Greedy_KWayCutOptimize(ctrl_t *ctrl, graph_t *graph, idx_t niter,
                            real_t ffactor, idx_t omode) {
  /* Common variables to all types of kway-refinement/balancing routines */
  idx_t i, ii, iii, j, k, l, pass, nvtxs, nparts, gain;
  idx_t from, me, to, oldcut, vwgt;
  idx_t *xadj, *adjncy, *adjwgt;
  idx_t *where, *pwgts, *perm, *bndptr, *bndind, *minpwgts, *maxpwgts;
  idx_t nmoved, nupd, *vstatus, *updptr, *updind;
  idx_t maxndoms, *safetos = NULL, *nads = NULL, *doms = NULL, **adids = NULL,
                  **adwgts = NULL;
  idx_t *bfslvl = NULL, *bfsind = NULL, *bfsmrk = NULL;
  idx_t bndtype = (omode == OMODE_REFINE ? BNDTYPE_REFINE : BNDTYPE_BALANCE);
  real_t *tpwgts, ubfactor;

  /* Edgecut-specific/different variables */
  idx_t nbnd, oldnnbrs;
  rpq_t *queue;
  real_t rgain;
  ckrinfo_t *myrinfo;
  cnbr_t *mynbrs;

  ffactor = 0.0;
  WCOREPUSH;

  /* Link the graph fields */
  nvtxs = graph->nvtxs;
  xadj = graph->xadj;
  adjncy = graph->adjncy;
  adjwgt = graph->adjwgt;

  bndind = graph->bndind;
  bndptr = graph->bndptr;

  where = graph->where;
  pwgts = graph->pwgts;

  nparts = ctrl->nparts;
  tpwgts = ctrl->tpwgts;

  /* Setup the weight intervals of the various subdomains */
  minpwgts = iwspacemalloc(ctrl, nparts);
  maxpwgts = iwspacemalloc(ctrl, nparts);

  if (omode == OMODE_BALANCE)
    ubfactor = ctrl->ubfactors[0];
  else
    ubfactor = gk_max(ctrl->ubfactors[0],
                      ComputeLoadImbalance(graph, nparts, ctrl->pijbm));

  for (i = 0; i < nparts; i++) {
    maxpwgts[i] = tpwgts[i] * graph->tvwgt[0] * ubfactor;
    minpwgts[i] = tpwgts[i] * graph->tvwgt[0] * (1.0 / ubfactor);
  }

  perm = iwspacemalloc(ctrl, nvtxs);

  /* This stores the valid target subdomains. It is used when ctrl->minconn to
     control the subdomains to which moves are allowed to be made.
     When ctrl->minconn is false, the default values of 2 allow all moves to
     go through and it does not interfere with the zero-gain move selection. */
  safetos = iset(nparts, 2, iwspacemalloc(ctrl, nparts));

  if (ctrl->minconn) {
    ComputeSubDomainGraph(ctrl, graph);

    nads = ctrl->nads;
    adids = ctrl->adids;
    adwgts = ctrl->adwgts;
    doms = iset(nparts, 0, ctrl->pvec1);
  }

  /* Setup updptr, updind like boundary info to keep track of the vertices whose
     vstatus's need to be reset at the end of the inner iteration */
  vstatus = iset(nvtxs, VPQSTATUS_NOTPRESENT, iwspacemalloc(ctrl, nvtxs));
  updptr = iset(nvtxs, -1, iwspacemalloc(ctrl, nvtxs));
  updind = iwspacemalloc(ctrl, nvtxs);

  if (ctrl->contig) {
    /* The arrays that will be used for limited check of articulation points */
    bfslvl = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));
    bfsind = iwspacemalloc(ctrl, nvtxs);
    bfsmrk = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));
  }

  if (ctrl->dbglvl & METIS_DBG_REFINE) {
    printf("%s: [%6" PRIDX " %6" PRIDX "]-[%6" PRIDX " %6" PRIDX
           "], Bal: %5.3" PRREAL ","
           " Nv-Nb[%6" PRIDX " %6" PRIDX "], Cut: %6" PRIDX,
           (omode == OMODE_REFINE ? "GRC" : "GBC"),
           pwgts[iargmin(nparts, pwgts, 1)], imax(nparts, pwgts, 1),
           minpwgts[0], maxpwgts[0],
           ComputeLoadImbalance(graph, nparts, ctrl->pijbm), graph->nvtxs,
           graph->nbnd, graph->mincut);
    if (ctrl->minconn)
      printf(", Doms: [%3" PRIDX " %4" PRIDX "]", imax(nparts, nads, 1),
             isum(nparts, nads, 1));
    printf("\n");
  }

  queue = rpqCreate(nvtxs);

  /*=====================================================================
   * The top-level refinement loop
   *======================================================================*/
  for (pass = 0; pass < niter; pass++) {
    ASSERT(ComputeCut(graph, where) == graph->mincut);
    if (omode == OMODE_REFINE)
      ASSERT(CheckBnd2(graph));

    if (omode == OMODE_BALANCE) {
      /* Check to see if things are out of balance, given the tolerance */
      for (i = 0; i < nparts; i++) {
        if (pwgts[i] > maxpwgts[i] || pwgts[i] < minpwgts[i])
          break;
      }
      if (i == nparts) /* Things are balanced. Return right away */
        break;
    }

    oldcut = graph->mincut;
    nbnd = graph->nbnd;
    nupd = 0;

    if (ctrl->minconn)
      maxndoms = imax(nparts, nads, 1);

    /* Insert the boundary vertices in the priority queue */
    irandArrayPermute(nbnd, perm, nbnd / 4, 1);
    for (ii = 0; ii < nbnd; ii++) {
      i = bndind[perm[ii]];
      rgain = (graph->ckrinfo[i].nnbrs > 0
                   ? 1.0 * graph->ckrinfo[i].ed / sqrt(graph->ckrinfo[i].nnbrs)
                   : 0.0) -
              graph->ckrinfo[i].id;
      rpqInsert(queue, i, rgain);
      vstatus[i] = VPQSTATUS_PRESENT;
      ListInsert(nupd, updind, updptr, i);
    }

    /* Start extracting vertices from the queue and try to move them */
    for (nmoved = 0, iii = 0;; iii++) {
      if ((i = rpqGetTop(queue)) == -1)
        break;
      vstatus[i] = VPQSTATUS_EXTRACTED;

      myrinfo = graph->ckrinfo + i;
      mynbrs = ctrl->cnbrpool + myrinfo->inbr;

      from = where[i];
      vwgt = graph->vwgt[i];

#ifdef XXX
      /* Prevent moves that make 'from' domain underbalanced */
      if (omode == OMODE_REFINE) {
        if (myrinfo->id > 0 && pwgts[from] - vwgt < minpwgts[from])
          continue;
      } else { /* OMODE_BALANCE */
        if (pwgts[from] - vwgt < minpwgts[from])
          continue;
      }
#endif

      if (ctrl->contig &&
          IsArticulationNode(i, xadj, adjncy, where, bfslvl, bfsind, bfsmrk))
        continue;

      if (ctrl->minconn)
        SelectSafeTargetSubdomains(myrinfo, mynbrs, nads, adids, maxndoms,
                                   safetos, doms);

      /* Find the most promising subdomain to move to */
      if (omode == OMODE_REFINE) {
        for (k = myrinfo->nnbrs - 1; k >= 0; k--) {
          if (!safetos[to = mynbrs[k].pid])
            continue;
          if (((mynbrs[k].ed > myrinfo->id) &&
               ((pwgts[from] - vwgt >= minpwgts[from]) ||
                (tpwgts[from] * pwgts[to] <
                 tpwgts[to] * (pwgts[from] - vwgt))) &&
               ((pwgts[to] + vwgt <= maxpwgts[to]) ||
                (tpwgts[from] * pwgts[to] <
                 tpwgts[to] * (pwgts[from] - vwgt)))) ||
              ((mynbrs[k].ed == myrinfo->id) &&
               (tpwgts[from] * pwgts[to] < tpwgts[to] * (pwgts[from] - vwgt))))
            break;
        }
        if (k < 0)
          continue; /* break out if you did not find a candidate */

        for (j = k - 1; j >= 0; j--) {
          if (!safetos[to = mynbrs[j].pid])
            continue;
          if (((mynbrs[j].ed > mynbrs[k].ed) &&
               ((pwgts[from] - vwgt >= minpwgts[from]) ||
                (tpwgts[from] * pwgts[to] <
                 tpwgts[to] * (pwgts[from] - vwgt))) &&
               ((pwgts[to] + vwgt <= maxpwgts[to]) ||
                (tpwgts[from] * pwgts[to] <
                 tpwgts[to] * (pwgts[from] - vwgt)))) ||
              ((mynbrs[j].ed == mynbrs[k].ed) &&
               (tpwgts[mynbrs[k].pid] * pwgts[to] <
                tpwgts[to] * pwgts[mynbrs[k].pid])))
            k = j;
        }

        to = mynbrs[k].pid;

        gain = mynbrs[k].ed - myrinfo->id;
        /*
        if (!(gain > 0
              || (gain == 0
                  && (pwgts[from] >= maxpwgts[from]
                      || tpwgts[to]*pwgts[from] > tpwgts[from]*(pwgts[to]+vwgt)
                      || (iii%2 == 0 && safetos[to] == 2)
                     )
                 )
             )
           )
          continue;
        */
      } else { /* OMODE_BALANCE */
        for (k = myrinfo->nnbrs - 1; k >= 0; k--) {
          if (!safetos[to = mynbrs[k].pid])
            continue;
          /* the correctness of the following test follows from the correctness
             of the similar test in the subsequent loop */
          if (from >= nparts ||
              tpwgts[from] * pwgts[to] < tpwgts[to] * (pwgts[from] - vwgt))
            break;
        }
        if (k < 0)
          continue; /* break out if you did not find a candidate */

        for (j = k - 1; j >= 0; j--) {
          if (!safetos[to = mynbrs[j].pid])
            continue;
          if (tpwgts[mynbrs[k].pid] * pwgts[to] <
              tpwgts[to] * pwgts[mynbrs[k].pid])
            k = j;
        }

        to = mynbrs[k].pid;

        // if (pwgts[from] < maxpwgts[from] && pwgts[to] > minpwgts[to] &&
        //     mynbrs[k].ed-myrinfo->id < 0)
        //   continue;
      }

      /*=====================================================================
       * If we got here, we can now move the vertex from 'from' to 'to'
       *======================================================================*/
      graph->mincut -= mynbrs[k].ed - myrinfo->id;
      nmoved++;

      IFSET(ctrl->dbglvl, METIS_DBG_MOVEINFO,
            printf("\t\tMoving %6" PRIDX " from %3" PRIDX "/%" PRIDX
                   " to %3" PRIDX "/%" PRIDX " [%6" PRIDX " %6" PRIDX
                   "]. Gain: %4" PRIDX ". Cut: %6" PRIDX "\n",
                   i, from, safetos[from], to, safetos[to], pwgts[from],
                   pwgts[to], mynbrs[k].ed - myrinfo->id, graph->mincut));

      /* Update the subdomain connectivity information */
      if (ctrl->minconn) {
        /* take care of i's move itself */
        UpdateEdgeSubDomainGraph(ctrl, from, to, myrinfo->id - mynbrs[k].ed,
                                 &maxndoms);

        /* take care of the adjacent vertices */
        for (j = xadj[i]; j < xadj[i + 1]; j++) {
          me = where[adjncy[j]];
          if (me != from && me != to) {
            UpdateEdgeSubDomainGraph(ctrl, from, me, -adjwgt[j], &maxndoms);
            UpdateEdgeSubDomainGraph(ctrl, to, me, adjwgt[j], &maxndoms);
          }
        }
      }

      /* Update ID/ED and BND related information for the moved vertex */
      INC_DEC(pwgts[to], pwgts[from], vwgt);
      UpdateMovedVertexInfoAndBND(i, from, k, to, myrinfo, mynbrs, where, nbnd,
                                  bndptr, bndind, bndtype);

      /* Update the degrees of adjacent vertices */
      for (j = xadj[i]; j < xadj[i + 1]; j++) {
        ii = adjncy[j];
        me = where[ii];
        myrinfo = graph->ckrinfo + ii;

        oldnnbrs = myrinfo->nnbrs;

        UpdateAdjacentVertexInfoAndBND(ctrl, ii, xadj[ii + 1] - xadj[ii], me,
                                       from, to, myrinfo, adjwgt[j], nbnd,
                                       bndptr, bndind, bndtype);

        UpdateQueueInfo(queue, vstatus, ii, me, from, to, myrinfo, oldnnbrs,
                        nupd, updptr, updind, bndtype);

        ASSERT(myrinfo->nnbrs <= xadj[ii + 1] - xadj[ii]);
      }
    }

    graph->nbnd = nbnd;

    /* Reset the vstatus and associated data structures */
    for (i = 0; i < nupd; i++) {
      ASSERT(updptr[updind[i]] != -1);
      ASSERT(vstatus[updind[i]] != VPQSTATUS_NOTPRESENT);
      vstatus[updind[i]] = VPQSTATUS_NOTPRESENT;
      updptr[updind[i]] = -1;
    }

    if (ctrl->dbglvl & METIS_DBG_REFINE) {
      printf("\t[%6" PRIDX " %6" PRIDX "], Bal: %5.3" PRREAL ", Nb: %6" PRIDX
             "."
             " Nmoves: %5" PRIDX ", Cut: %6" PRIDX ", Vol: %6" PRIDX,
             pwgts[iargmin(nparts, pwgts, 1)], imax(nparts, pwgts, 1),
             ComputeLoadImbalance(graph, nparts, ctrl->pijbm), graph->nbnd,
             nmoved, graph->mincut, ComputeVolume(graph, where));
      if (ctrl->minconn)
        printf(", Doms: [%3" PRIDX " %4" PRIDX "]", imax(nparts, nads, 1),
               isum(nparts, nads, 1));
      printf("\n");
    }

    if (nmoved == 0 || (omode == OMODE_REFINE && graph->mincut == oldcut))
      break;
  }

  rpqDestroy(queue);

  WCOREPOP;
}

/*************************************************************************/
/*! K-way refinement that minimizes the communication volume. This is a
    greedy routine and the vertices are visited in decreasing gv order.

  \param graph is the graph that is being refined.
  \param niter is the number of refinement iterations.
  \param ffactor is the \em fudge-factor for allowing positive gain moves
         to violate the max-pwgt constraint.

*/
/**************************************************************************/
void Greedy_KWayVolOptimize(ctrl_t *ctrl, graph_t *graph, idx_t niter,
                            real_t ffactor, idx_t omode) {
  /* Common variables to all types of kway-refinement/balancing routines */
  idx_t i, ii, iii, j, k, l, pass, nvtxs, nparts, gain;
  idx_t from, me, to, oldcut, vwgt;
  idx_t *xadj, *adjncy;
  idx_t *where, *pwgts, *perm, *bndptr, *bndind, *minpwgts, *maxpwgts;
  idx_t nmoved, nupd, *vstatus, *updptr, *updind;
  idx_t maxndoms, *safetos = NULL, *nads = NULL, *doms = NULL, **adids = NULL,
                  **adwgts = NULL;
  idx_t *bfslvl = NULL, *bfsind = NULL, *bfsmrk = NULL;
  idx_t bndtype = (omode == OMODE_REFINE ? BNDTYPE_REFINE : BNDTYPE_BALANCE);
  real_t *tpwgts;

  /* Volume-specific/different variables */
  ipq_t *queue;
  idx_t oldvol, xgain;
  idx_t *vmarker, *pmarker, *modind;
  vkrinfo_t *myrinfo;
  vnbr_t *mynbrs;

  WCOREPUSH;

  /* Link the graph fields */
  nvtxs = graph->nvtxs;
  xadj = graph->xadj;
  adjncy = graph->adjncy;
  bndptr = graph->bndptr;
  bndind = graph->bndind;
  where = graph->where;
  pwgts = graph->pwgts;

  nparts = ctrl->nparts;
  tpwgts = ctrl->tpwgts;

  /* Setup the weight intervals of the various subdomains */
  minpwgts = iwspacemalloc(ctrl, nparts);
  maxpwgts = iwspacemalloc(ctrl, nparts);

  for (i = 0; i < nparts; i++) {
    maxpwgts[i] = ctrl->tpwgts[i] * graph->tvwgt[0] * ctrl->ubfactors[0];
    minpwgts[i] =
        ctrl->tpwgts[i] * graph->tvwgt[0] * (1.0 / ctrl->ubfactors[0]);
  }

  perm = iwspacemalloc(ctrl, nvtxs);

  /* This stores the valid target subdomains. It is used when ctrl->minconn to
     control the subdomains to which moves are allowed to be made.
     When ctrl->minconn is false, the default values of 2 allow all moves to
     go through and it does not interfere with the zero-gain move selection. */
  safetos = iset(nparts, 2, iwspacemalloc(ctrl, nparts));

  if (ctrl->minconn) {
    ComputeSubDomainGraph(ctrl, graph);

    nads = ctrl->nads;
    adids = ctrl->adids;
    adwgts = ctrl->adwgts;
    doms = iset(nparts, 0, ctrl->pvec1);
  }

  /* Setup updptr, updind like boundary info to keep track of the vertices whose
     vstatus's need to be reset at the end of the inner iteration */
  vstatus = iset(nvtxs, VPQSTATUS_NOTPRESENT, iwspacemalloc(ctrl, nvtxs));
  updptr = iset(nvtxs, -1, iwspacemalloc(ctrl, nvtxs));
  updind = iwspacemalloc(ctrl, nvtxs);

  if (ctrl->contig) {
    /* The arrays that will be used for limited check of articulation points */
    bfslvl = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));
    bfsind = iwspacemalloc(ctrl, nvtxs);
    bfsmrk = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));
  }

  /* Vol-refinement specific working arrays */
  modind = iwspacemalloc(ctrl, nvtxs);
  vmarker = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));
  pmarker = iset(nparts, -1, iwspacemalloc(ctrl, nparts));

  if (ctrl->dbglvl & METIS_DBG_REFINE) {
    printf("%s: [%6" PRIDX " %6" PRIDX "]-[%6" PRIDX " %6" PRIDX
           "], Bal: %5.3" PRREAL ", Nv-Nb[%6" PRIDX " %6" PRIDX
           "], Cut: %5" PRIDX ", Vol: %5" PRIDX,
           (omode == OMODE_REFINE ? "GRV" : "GBV"),
           pwgts[iargmin(nparts, pwgts, 1)], imax(nparts, pwgts, 1),
           minpwgts[0], maxpwgts[0],
           ComputeLoadImbalance(graph, nparts, ctrl->pijbm), graph->nvtxs,
           graph->nbnd, graph->mincut, graph->minvol);
    if (ctrl->minconn)
      printf(", Doms: [%3" PRIDX " %4" PRIDX "]", imax(nparts, nads, 1),
             isum(nparts, nads, 1));
    printf("\n");
  }

  queue = ipqCreate(nvtxs);

  /*=====================================================================
   * The top-level refinement loop
   *======================================================================*/
  for (pass = 0; pass < niter; pass++) {
    ASSERT(ComputeVolume(graph, where) == graph->minvol);

    if (omode == OMODE_BALANCE) {
      /* Check to see if things are out of balance, given the tolerance */
      for (i = 0; i < nparts; i++) {
        if (pwgts[i] > maxpwgts[i])
          break;
      }
      if (i == nparts) /* Things are balanced. Return right away */
        break;
    }

    oldcut = graph->mincut;
    oldvol = graph->minvol;
    nupd = 0;

    if (ctrl->minconn)
      maxndoms = imax(nparts, nads, 1);

    /* Insert the boundary vertices in the priority queue */
    irandArrayPermute(graph->nbnd, perm, graph->nbnd / 4, 1);
    for (ii = 0; ii < graph->nbnd; ii++) {
      i = bndind[perm[ii]];
      ipqInsert(queue, i, graph->vkrinfo[i].gv);
      vstatus[i] = VPQSTATUS_PRESENT;
      ListInsert(nupd, updind, updptr, i);
    }

    /* Start extracting vertices from the queue and try to move them */
    for (nmoved = 0, iii = 0;; iii++) {
      if ((i = ipqGetTop(queue)) == -1)
        break;
      vstatus[i] = VPQSTATUS_EXTRACTED;

      myrinfo = graph->vkrinfo + i;
      mynbrs = ctrl->vnbrpool + myrinfo->inbr;

      from = where[i];
      vwgt = graph->vwgt[i];

      /* Prevent moves that make 'from' domain underbalanced */
      if (omode == OMODE_REFINE) {
        if (myrinfo->nid > 0 && pwgts[from] - vwgt < minpwgts[from])
          continue;
      } else { /* OMODE_BALANCE */
        if (pwgts[from] - vwgt < minpwgts[from])
          continue;
      }

      if (ctrl->contig &&
          IsArticulationNode(i, xadj, adjncy, where, bfslvl, bfsind, bfsmrk))
        continue;

      if (ctrl->minconn)
        SelectSafeTargetSubdomains(myrinfo, mynbrs, nads, adids, maxndoms,
                                   safetos, doms);

      xgain = (myrinfo->nid == 0 && myrinfo->ned > 0 ? graph->vsize[i] : 0);

      /* Find the most promising subdomain to move to */
      if (omode == OMODE_REFINE) {
        for (k = myrinfo->nnbrs - 1; k >= 0; k--) {
          if (!safetos[to = mynbrs[k].pid])
            continue;
          gain = mynbrs[k].gv + xgain;
          if (gain >= 0 && pwgts[to] + vwgt <= maxpwgts[to] + ffactor * gain)
            break;
        }
        if (k < 0)
          continue; /* break out if you did not find a candidate */

        for (j = k - 1; j >= 0; j--) {
          if (!safetos[to = mynbrs[j].pid])
            continue;
          gain = mynbrs[j].gv + xgain;
          if ((mynbrs[j].gv > mynbrs[k].gv &&
               pwgts[to] + vwgt <= maxpwgts[to] + ffactor * gain) ||
              (mynbrs[j].gv == mynbrs[k].gv && mynbrs[j].ned > mynbrs[k].ned &&
               pwgts[to] + vwgt <= maxpwgts[to]) ||
              (mynbrs[j].gv == mynbrs[k].gv && mynbrs[j].ned == mynbrs[k].ned &&
               tpwgts[mynbrs[k].pid] * pwgts[to] <
                   tpwgts[to] * pwgts[mynbrs[k].pid]))
            k = j;
        }
        to = mynbrs[k].pid;

        ASSERT(xgain + mynbrs[k].gv >= 0);

        j = 0;
        if (xgain + mynbrs[k].gv > 0 || mynbrs[k].ned - myrinfo->nid > 0)
          j = 1;
        else if (mynbrs[k].ned - myrinfo->nid == 0) {
          if ((iii % 2 == 0 && safetos[to] == 2) ||
              pwgts[from] >= maxpwgts[from] ||
              tpwgts[from] * (pwgts[to] + vwgt) < tpwgts[to] * pwgts[from])
            j = 1;
        }
        if (j == 0)
          continue;
      } else { /* OMODE_BALANCE */
        for (k = myrinfo->nnbrs - 1; k >= 0; k--) {
          if (!safetos[to = mynbrs[k].pid])
            continue;
          if (pwgts[to] + vwgt <= maxpwgts[to] ||
              tpwgts[from] * (pwgts[to] + vwgt) <= tpwgts[to] * pwgts[from])
            break;
        }
        if (k < 0)
          continue; /* break out if you did not find a candidate */

        for (j = k - 1; j >= 0; j--) {
          if (!safetos[to = mynbrs[j].pid])
            continue;
          if (tpwgts[mynbrs[k].pid] * pwgts[to] <
              tpwgts[to] * pwgts[mynbrs[k].pid])
            k = j;
        }
        to = mynbrs[k].pid;

        if (pwgts[from] < maxpwgts[from] && pwgts[to] > minpwgts[to] &&
            (xgain + mynbrs[k].gv < 0 ||
             (xgain + mynbrs[k].gv == 0 && mynbrs[k].ned - myrinfo->nid < 0)))
          continue;
      }

      /*=====================================================================
       * If we got here, we can now move the vertex from 'from' to 'to'
       *======================================================================*/
      INC_DEC(pwgts[to], pwgts[from], vwgt);
      graph->mincut -= mynbrs[k].ned - myrinfo->nid;
      graph->minvol -= (xgain + mynbrs[k].gv);
      where[i] = to;
      nmoved++;

      IFSET(ctrl->dbglvl, METIS_DBG_MOVEINFO,
            printf("\t\tMoving %6" PRIDX " from %3" PRIDX " to %3" PRIDX ". "
                   "Gain: [%4" PRIDX " %4" PRIDX "]. Cut: %6" PRIDX
                   ", Vol: %6" PRIDX "\n",
                   i, from, to, xgain + mynbrs[k].gv,
                   mynbrs[k].ned - myrinfo->nid, graph->mincut, graph->minvol));

      /* Update the subdomain connectivity information */
      if (ctrl->minconn) {
        /* take care of i's move itself */
        UpdateEdgeSubDomainGraph(ctrl, from, to, myrinfo->nid - mynbrs[k].ned,
                                 &maxndoms);

        /* take care of the adjacent vertices */
        for (j = xadj[i]; j < xadj[i + 1]; j++) {
          me = where[adjncy[j]];
          if (me != from && me != to) {
            UpdateEdgeSubDomainGraph(ctrl, from, me, -1, &maxndoms);
            UpdateEdgeSubDomainGraph(ctrl, to, me, 1, &maxndoms);
          }
        }
      }

      /* Update the id/ed/gains/bnd/queue of potentially affected nodes */
      KWayVolUpdate(ctrl, graph, i, from, to, queue, vstatus, &nupd, updptr,
                    updind, bndtype, vmarker, pmarker, modind);

      /*CheckKWayVolPartitionParams(ctrl, graph); */
    }

    /* Reset the vstatus and associated data structures */
    for (i = 0; i < nupd; i++) {
      ASSERT(updptr[updind[i]] != -1);
      ASSERT(vstatus[updind[i]] != VPQSTATUS_NOTPRESENT);
      vstatus[updind[i]] = VPQSTATUS_NOTPRESENT;
      updptr[updind[i]] = -1;
    }

    if (ctrl->dbglvl & METIS_DBG_REFINE) {
      printf("\t[%6" PRIDX " %6" PRIDX "], Bal: %5.3" PRREAL ", Nb: %6" PRIDX
             "."
             " Nmoves: %5" PRIDX ", Cut: %6" PRIDX ", Vol: %6" PRIDX,
             pwgts[iargmin(nparts, pwgts, 1)], imax(nparts, pwgts, 1),
             ComputeLoadImbalance(graph, nparts, ctrl->pijbm), graph->nbnd,
             nmoved, graph->mincut, graph->minvol);
      if (ctrl->minconn)
        printf(", Doms: [%3" PRIDX " %4" PRIDX "]", imax(nparts, nads, 1),
               isum(nparts, nads, 1));
      printf("\n");
    }

    if (nmoved == 0 || (omode == OMODE_REFINE && graph->minvol == oldvol &&
                        graph->mincut == oldcut))
      break;
  }

  ipqDestroy(queue);

  WCOREPOP;
}

/*************************************************************************/
/*! K-way partitioning optimization in which the vertices are visited in
    decreasing ed/sqrt(nnbrs)-id order. Note this is just an
    approximation, as the ed is often split across different subdomains
    and the sqrt(nnbrs) is just a crude approximation.

  \param graph is the graph that is being refined.
  \param niter is the number of refinement iterations.
  \param ffactor is the \em fudge-factor for allowing positive gain moves
         to violate the max-pwgt constraint.
  \param omode is the type of optimization that will performed among
         OMODE_REFINE and OMODE_BALANCE


*/
/**************************************************************************/
void Greedy_McKWayCutOptimize(ctrl_t *ctrl, graph_t *graph, idx_t niter,
                              real_t ffactor, idx_t omode) {
  /* Common variables to all types of kway-refinement/balancing routines */
  idx_t i, ii, iii, j, k, l, pass, nvtxs, ncon, nparts, gain;
  idx_t from, me, to, cto, oldcut;
  idx_t *xadj, *vwgt, *adjncy, *adjwgt;
  idx_t *where, *pwgts, *perm, *bndptr, *bndind, *minpwgts, *maxpwgts;
  idx_t nmoved, nupd, *vstatus, *updptr, *updind;
  idx_t maxndoms, *safetos = NULL, *nads = NULL, *doms = NULL, **adids = NULL,
                  **adwgts = NULL;
  idx_t *bfslvl = NULL, *bfsind = NULL, *bfsmrk = NULL;
  idx_t bndtype = (omode == OMODE_REFINE ? BNDTYPE_REFINE : BNDTYPE_BALANCE);
  real_t *ubfactors, *pijbm;
  real_t origbal;

  /* Edgecut-specific/different variables */
  idx_t nbnd, oldnnbrs;
  rpq_t *queue;
  real_t rgain;
  ckrinfo_t *myrinfo;
  cnbr_t *mynbrs;

  WCOREPUSH;

  /* Link the graph fields */
  nvtxs = graph->nvtxs;
  ncon = graph->ncon;
  xadj = graph->xadj;
  vwgt = graph->vwgt;
  adjncy = graph->adjncy;
  adjwgt = graph->adjwgt;

  bndind = graph->bndind;
  bndptr = graph->bndptr;

  where = graph->where;
  pwgts = graph->pwgts;

  nparts = ctrl->nparts;
  pijbm = ctrl->pijbm;

  /* Determine the ubfactors. The method used is different based on omode.
     When OMODE_BALANCE, the ubfactors are those supplied by the user.
     When OMODE_REFINE, the ubfactors are the max of the current partition
     and the user-specified ones. */
  ubfactors = rwspacemalloc(ctrl, ncon);
  ComputeLoadImbalanceVec(graph, nparts, pijbm, ubfactors);
  origbal = rvecmaxdiff(ncon, ubfactors, ctrl->ubfactors);
  if (omode == OMODE_BALANCE) {
    rcopy(ncon, ctrl->ubfactors, ubfactors);
  } else {
    for (i = 0; i < ncon; i++)
      ubfactors[i] = (ubfactors[i] > ctrl->ubfactors[i] ? ubfactors[i]
                                                        : ctrl->ubfactors[i]);
  }

  /* Setup the weight intervals of the various subdomains */
  minpwgts = iwspacemalloc(ctrl, nparts * ncon);
  maxpwgts = iwspacemalloc(ctrl, nparts * ncon);

  for (i = 0; i < nparts; i++) {
    for (j = 0; j < ncon; j++) {
      maxpwgts[i * ncon + j] =
          ctrl->tpwgts[i * ncon + j] * graph->tvwgt[j] * ubfactors[j];
      /*minpwgts[i*ncon+j]  =
       * ctrl->tpwgts[i*ncon+j]*graph->tvwgt[j]*(.9/ubfactors[j]);*/
      minpwgts[i * ncon + j] =
          ctrl->tpwgts[i * ncon + j] * graph->tvwgt[j] * .2;
    }
  }

  perm = iwspacemalloc(ctrl, nvtxs);

  /* This stores the valid target subdomains. It is used when ctrl->minconn to
     control the subdomains to which moves are allowed to be made.
     When ctrl->minconn is false, the default values of 2 allow all moves to
     go through and it does not interfere with the zero-gain move selection. */
  safetos = iset(nparts, 2, iwspacemalloc(ctrl, nparts));

  if (ctrl->minconn) {
    ComputeSubDomainGraph(ctrl, graph);

    nads = ctrl->nads;
    adids = ctrl->adids;
    adwgts = ctrl->adwgts;
    doms = iset(nparts, 0, ctrl->pvec1);
  }

  /* Setup updptr, updind like boundary info to keep track of the vertices whose
     vstatus's need to be reset at the end of the inner iteration */
  vstatus = iset(nvtxs, VPQSTATUS_NOTPRESENT, iwspacemalloc(ctrl, nvtxs));
  updptr = iset(nvtxs, -1, iwspacemalloc(ctrl, nvtxs));
  updind = iwspacemalloc(ctrl, nvtxs);

  if (ctrl->contig) {
    /* The arrays that will be used for limited check of articulation points */
    bfslvl = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));
    bfsind = iwspacemalloc(ctrl, nvtxs);
    bfsmrk = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));
  }

  if (ctrl->dbglvl & METIS_DBG_REFINE) {
    printf("%s: [%6" PRIDX " %6" PRIDX " %6" PRIDX "], Bal: %5.3" PRREAL
           "(%.3" PRREAL "),"
           " Nv-Nb[%6" PRIDX " %6" PRIDX "], Cut: %6" PRIDX ", (%" PRIDX ")",
           (omode == OMODE_REFINE ? "GRC" : "GBC"),
           imin(nparts * ncon, pwgts, 1), imax(nparts * ncon, pwgts, 1),
           imax(nparts * ncon, maxpwgts, 1),
           ComputeLoadImbalance(graph, nparts, pijbm), origbal, graph->nvtxs,
           graph->nbnd, graph->mincut, niter);
    if (ctrl->minconn)
      printf(", Doms: [%3" PRIDX " %4" PRIDX "]", imax(nparts, nads, 1),
             isum(nparts, nads, 1));
    printf("\n");
  }

  queue = rpqCreate(nvtxs);

  /*=====================================================================
   * The top-level refinement loop
   *======================================================================*/
  for (pass = 0; pass < niter; pass++) {
    ASSERT(ComputeCut(graph, where) == graph->mincut);
    if (omode == OMODE_REFINE)
      ASSERT(CheckBnd2(graph));

    /* In balancing mode, exit as soon as balance is reached */
    if (omode == OMODE_BALANCE && IsBalanced(ctrl, graph, 0))
      break;

    oldcut = graph->mincut;
    nbnd = graph->nbnd;
    nupd = 0;

    if (ctrl->minconn)
      maxndoms = imax(nparts, nads, 1);

    /* Insert the boundary vertices in the priority queue */
    irandArrayPermute(nbnd, perm, nbnd / 4, 1);
    for (ii = 0; ii < nbnd; ii++) {
      i = bndind[perm[ii]];
      rgain = (graph->ckrinfo[i].nnbrs > 0
                   ? 1.0 * graph->ckrinfo[i].ed / sqrt(graph->ckrinfo[i].nnbrs)
                   : 0.0) -
              graph->ckrinfo[i].id;
      rpqInsert(queue, i, rgain);
      vstatus[i] = VPQSTATUS_PRESENT;
      ListInsert(nupd, updind, updptr, i);
    }

    /* Start extracting vertices from the queue and try to move them */
    for (nmoved = 0, iii = 0;; iii++) {
      if ((i = rpqGetTop(queue)) == -1)
        break;
      vstatus[i] = VPQSTATUS_EXTRACTED;

      myrinfo = graph->ckrinfo + i;
      mynbrs = ctrl->cnbrpool + myrinfo->inbr;

      from = where[i];

      /* Prevent moves that make 'from' domain underbalanced */
      if (omode == OMODE_REFINE) {
        if (myrinfo->id > 0 &&
            !ivecaxpygez(ncon, -1, vwgt + i * ncon, pwgts + from * ncon,
                         minpwgts + from * ncon))
          continue;
      } else { /* OMODE_BALANCE */
        if (!ivecaxpygez(ncon, -1, vwgt + i * ncon, pwgts + from * ncon,
                         minpwgts + from * ncon))
          continue;
      }

      if (ctrl->contig &&
          IsArticulationNode(i, xadj, adjncy, where, bfslvl, bfsind, bfsmrk))
        continue;

      if (ctrl->minconn)
        SelectSafeTargetSubdomains(myrinfo, mynbrs, nads, adids, maxndoms,
                                   safetos, doms);

      /* Find the most promising subdomain to move to */
      if (omode == OMODE_REFINE) {
        for (k = myrinfo->nnbrs - 1; k >= 0; k--) {
          if (!safetos[to = mynbrs[k].pid])
            continue;
          gain = mynbrs[k].ed - myrinfo->id;
          if (gain >= 0 && ivecaxpylez(ncon, 1, vwgt + i * ncon,
                                       pwgts + to * ncon, maxpwgts + to * ncon))
            break;
        }
        if (k < 0)
          continue; /* break out if you did not find a candidate */

        cto = to;
        for (j = k - 1; j >= 0; j--) {
          if (!safetos[to = mynbrs[j].pid])
            continue;
          if ((mynbrs[j].ed > mynbrs[k].ed &&
               ivecaxpylez(ncon, 1, vwgt + i * ncon, pwgts + to * ncon,
                           maxpwgts + to * ncon)) ||
              (mynbrs[j].ed == mynbrs[k].ed &&
               BetterBalanceKWay(ncon, vwgt + i * ncon, ubfactors, 1,
                                 pwgts + cto * ncon, pijbm + cto * ncon, 1,
                                 pwgts + to * ncon, pijbm + to * ncon))) {
            k = j;
            cto = to;
          }
        }
        to = cto;

        gain = mynbrs[k].ed - myrinfo->id;
        if (!(gain > 0 ||
              (gain == 0 &&
               (BetterBalanceKWay(ncon, vwgt + i * ncon, ubfactors, -1,
                                  pwgts + from * ncon, pijbm + from * ncon, +1,
                                  pwgts + to * ncon, pijbm + to * ncon) ||
                (iii % 2 == 0 && safetos[to] == 2)))))
          continue;
      } else { /* OMODE_BALANCE */
        for (k = myrinfo->nnbrs - 1; k >= 0; k--) {
          if (!safetos[to = mynbrs[k].pid])
            continue;
          if (ivecaxpylez(ncon, 1, vwgt + i * ncon, pwgts + to * ncon,
                          maxpwgts + to * ncon) ||
              BetterBalanceKWay(ncon, vwgt + i * ncon, ubfactors, -1,
                                pwgts + from * ncon, pijbm + from * ncon, +1,
                                pwgts + to * ncon, pijbm + to * ncon))
            break;
        }
        if (k < 0)
          continue; /* break out if you did not find a candidate */

        cto = to;
        for (j = k - 1; j >= 0; j--) {
          if (!safetos[to = mynbrs[j].pid])
            continue;
          if (BetterBalanceKWay(ncon, vwgt + i * ncon, ubfactors, 1,
                                pwgts + cto * ncon, pijbm + cto * ncon, 1,
                                pwgts + to * ncon, pijbm + to * ncon)) {
            k = j;
            cto = to;
          }
        }
        to = cto;

        if (mynbrs[k].ed - myrinfo->id < 0 &&
            !BetterBalanceKWay(ncon, vwgt + i * ncon, ubfactors, -1,
                               pwgts + from * ncon, pijbm + from * ncon, +1,
                               pwgts + to * ncon, pijbm + to * ncon))
          continue;
      }

      /*=====================================================================
       * If we got here, we can now move the vertex from 'from' to 'to'
       *======================================================================*/
      graph->mincut -= mynbrs[k].ed - myrinfo->id;
      nmoved++;

      IFSET(ctrl->dbglvl, METIS_DBG_MOVEINFO,
            printf("\t\tMoving %6" PRIDX " to %3" PRIDX ". Gain: %4" PRIDX
                   ". Cut: %6" PRIDX "\n",
                   i, to, mynbrs[k].ed - myrinfo->id, graph->mincut));

      /* Update the subdomain connectivity information */
      if (ctrl->minconn) {
        /* take care of i's move itself */
        UpdateEdgeSubDomainGraph(ctrl, from, to, myrinfo->id - mynbrs[k].ed,
                                 &maxndoms);

        /* take care of the adjacent vertices */
        for (j = xadj[i]; j < xadj[i + 1]; j++) {
          me = where[adjncy[j]];
          if (me != from && me != to) {
            UpdateEdgeSubDomainGraph(ctrl, from, me, -adjwgt[j], &maxndoms);
            UpdateEdgeSubDomainGraph(ctrl, to, me, adjwgt[j], &maxndoms);
          }
        }
      }

      /* Update ID/ED and BND related information for the moved vertex */
      iaxpy(ncon, 1, vwgt + i * ncon, 1, pwgts + to * ncon, 1);
      iaxpy(ncon, -1, vwgt + i * ncon, 1, pwgts + from * ncon, 1);
      UpdateMovedVertexInfoAndBND(i, from, k, to, myrinfo, mynbrs, where, nbnd,
                                  bndptr, bndind, bndtype);

      /* Update the degrees of adjacent vertices */
      for (j = xadj[i]; j < xadj[i + 1]; j++) {
        ii = adjncy[j];
        me = where[ii];
        myrinfo = graph->ckrinfo + ii;

        oldnnbrs = myrinfo->nnbrs;

        UpdateAdjacentVertexInfoAndBND(ctrl, ii, xadj[ii + 1] - xadj[ii], me,
                                       from, to, myrinfo, adjwgt[j], nbnd,
                                       bndptr, bndind, bndtype);

        UpdateQueueInfo(queue, vstatus, ii, me, from, to, myrinfo, oldnnbrs,
                        nupd, updptr, updind, bndtype);

        ASSERT(myrinfo->nnbrs <= xadj[ii + 1] - xadj[ii]);
      }
    }

    graph->nbnd = nbnd;

    /* Reset the vstatus and associated data structures */
    for (i = 0; i < nupd; i++) {
      ASSERT(updptr[updind[i]] != -1);
      ASSERT(vstatus[updind[i]] != VPQSTATUS_NOTPRESENT);
      vstatus[updind[i]] = VPQSTATUS_NOTPRESENT;
      updptr[updind[i]] = -1;
    }

    if (ctrl->dbglvl & METIS_DBG_REFINE) {
      printf("\t[%6" PRIDX " %6" PRIDX "], Bal: %5.3" PRREAL ", Nb: %6" PRIDX
             "."
             " Nmoves: %5" PRIDX ", Cut: %6" PRIDX ", Vol: %6" PRIDX,
             imin(nparts * ncon, pwgts, 1), imax(nparts * ncon, pwgts, 1),
             ComputeLoadImbalance(graph, nparts, pijbm), graph->nbnd, nmoved,
             graph->mincut, ComputeVolume(graph, where));
      if (ctrl->minconn)
        printf(", Doms: [%3" PRIDX " %4" PRIDX "]", imax(nparts, nads, 1),
               isum(nparts, nads, 1));
      printf("\n");
    }

    if (nmoved == 0 || (omode == OMODE_REFINE && graph->mincut == oldcut))
      break;
  }

  rpqDestroy(queue);

  WCOREPOP;
}

/*************************************************************************/
/*! K-way refinement that minimizes the communication volume. This is a
    greedy routine and the vertices are visited in decreasing gv order.

  \param graph is the graph that is being refined.
  \param niter is the number of refinement iterations.
  \param ffactor is the \em fudge-factor for allowing positive gain moves
         to violate the max-pwgt constraint.

*/
/**************************************************************************/
void Greedy_McKWayVolOptimize(ctrl_t *ctrl, graph_t *graph, idx_t niter,
                              real_t ffactor, idx_t omode) {
  /* Common variables to all types of kway-refinement/balancing routines */
  idx_t i, ii, iii, j, k, l, pass, nvtxs, ncon, nparts, gain;
  idx_t from, me, to, cto, oldcut;
  idx_t *xadj, *vwgt, *adjncy;
  idx_t *where, *pwgts, *perm, *bndptr, *bndind, *minpwgts, *maxpwgts;
  idx_t nmoved, nupd, *vstatus, *updptr, *updind;
  idx_t maxndoms, *safetos = NULL, *nads = NULL, *doms = NULL, **adids = NULL,
                  **adwgts = NULL;
  idx_t *bfslvl = NULL, *bfsind = NULL, *bfsmrk = NULL;
  idx_t bndtype = (omode == OMODE_REFINE ? BNDTYPE_REFINE : BNDTYPE_BALANCE);
  real_t *ubfactors, *pijbm;
  real_t origbal;

  /* Volume-specific/different variables */
  ipq_t *queue;
  idx_t oldvol, xgain;
  idx_t *vmarker, *pmarker, *modind;
  vkrinfo_t *myrinfo;
  vnbr_t *mynbrs;

  WCOREPUSH;

  /* Link the graph fields */
  nvtxs = graph->nvtxs;
  ncon = graph->ncon;
  xadj = graph->xadj;
  vwgt = graph->vwgt;
  adjncy = graph->adjncy;
  bndptr = graph->bndptr;
  bndind = graph->bndind;
  where = graph->where;
  pwgts = graph->pwgts;

  nparts = ctrl->nparts;
  pijbm = ctrl->pijbm;

  /* Determine the ubfactors. The method used is different based on omode.
     When OMODE_BALANCE, the ubfactors are those supplied by the user.
     When OMODE_REFINE, the ubfactors are the max of the current partition
     and the user-specified ones. */
  ubfactors = rwspacemalloc(ctrl, ncon);
  ComputeLoadImbalanceVec(graph, nparts, pijbm, ubfactors);
  origbal = rvecmaxdiff(ncon, ubfactors, ctrl->ubfactors);
  if (omode == OMODE_BALANCE) {
    rcopy(ncon, ctrl->ubfactors, ubfactors);
  } else {
    for (i = 0; i < ncon; i++)
      ubfactors[i] = (ubfactors[i] > ctrl->ubfactors[i] ? ubfactors[i]
                                                        : ctrl->ubfactors[i]);
  }

  /* Setup the weight intervals of the various subdomains */
  minpwgts = iwspacemalloc(ctrl, nparts * ncon);
  maxpwgts = iwspacemalloc(ctrl, nparts * ncon);

  for (i = 0; i < nparts; i++) {
    for (j = 0; j < ncon; j++) {
      maxpwgts[i * ncon + j] =
          ctrl->tpwgts[i * ncon + j] * graph->tvwgt[j] * ubfactors[j];
      /*minpwgts[i*ncon+j]  =
       * ctrl->tpwgts[i*ncon+j]*graph->tvwgt[j]*(.9/ubfactors[j]); */
      minpwgts[i * ncon + j] =
          ctrl->tpwgts[i * ncon + j] * graph->tvwgt[j] * .2;
    }
  }

  perm = iwspacemalloc(ctrl, nvtxs);

  /* This stores the valid target subdomains. It is used when ctrl->minconn to
     control the subdomains to which moves are allowed to be made.
     When ctrl->minconn is false, the default values of 2 allow all moves to
     go through and it does not interfere with the zero-gain move selection. */
  safetos = iset(nparts, 2, iwspacemalloc(ctrl, nparts));

  if (ctrl->minconn) {
    ComputeSubDomainGraph(ctrl, graph);

    nads = ctrl->nads;
    adids = ctrl->adids;
    adwgts = ctrl->adwgts;
    doms = iset(nparts, 0, ctrl->pvec1);
  }

  /* Setup updptr, updind like boundary info to keep track of the vertices whose
     vstatus's need to be reset at the end of the inner iteration */
  vstatus = iset(nvtxs, VPQSTATUS_NOTPRESENT, iwspacemalloc(ctrl, nvtxs));
  updptr = iset(nvtxs, -1, iwspacemalloc(ctrl, nvtxs));
  updind = iwspacemalloc(ctrl, nvtxs);

  if (ctrl->contig) {
    /* The arrays that will be used for limited check of articulation points */
    bfslvl = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));
    bfsind = iwspacemalloc(ctrl, nvtxs);
    bfsmrk = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));
  }

  /* Vol-refinement specific working arrays */
  modind = iwspacemalloc(ctrl, nvtxs);
  vmarker = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));
  pmarker = iset(nparts, -1, iwspacemalloc(ctrl, nparts));

  if (ctrl->dbglvl & METIS_DBG_REFINE) {
    printf("%s: [%6" PRIDX " %6" PRIDX " %6" PRIDX "], Bal: %5.3" PRREAL
           "(%.3" PRREAL "),"
           ", Nv-Nb[%6" PRIDX " %6" PRIDX "], Cut: %5" PRIDX ", Vol: %5" PRIDX
           ", (%" PRIDX ")",
           (omode == OMODE_REFINE ? "GRV" : "GBV"),
           imin(nparts * ncon, pwgts, 1), imax(nparts * ncon, pwgts, 1),
           imax(nparts * ncon, maxpwgts, 1),
           ComputeLoadImbalance(graph, nparts, pijbm), origbal, graph->nvtxs,
           graph->nbnd, graph->mincut, graph->minvol, niter);
    if (ctrl->minconn)
      printf(", Doms: [%3" PRIDX " %4" PRIDX "]", imax(nparts, nads, 1),
             isum(nparts, nads, 1));
    printf("\n");
  }

  queue = ipqCreate(nvtxs);

  /*=====================================================================
   * The top-level refinement loop
   *======================================================================*/
  for (pass = 0; pass < niter; pass++) {
    ASSERT(ComputeVolume(graph, where) == graph->minvol);

    /* In balancing mode, exit as soon as balance is reached */
    if (omode == OMODE_BALANCE && IsBalanced(ctrl, graph, 0))
      break;

    oldcut = graph->mincut;
    oldvol = graph->minvol;
    nupd = 0;

    if (ctrl->minconn)
      maxndoms = imax(nparts, nads, 1);

    /* Insert the boundary vertices in the priority queue */
    irandArrayPermute(graph->nbnd, perm, graph->nbnd / 4, 1);
    for (ii = 0; ii < graph->nbnd; ii++) {
      i = bndind[perm[ii]];
      ipqInsert(queue, i, graph->vkrinfo[i].gv);
      vstatus[i] = VPQSTATUS_PRESENT;
      ListInsert(nupd, updind, updptr, i);
    }

    /* Start extracting vertices from the queue and try to move them */
    for (nmoved = 0, iii = 0;; iii++) {
      if ((i = ipqGetTop(queue)) == -1)
        break;
      vstatus[i] = VPQSTATUS_EXTRACTED;

      myrinfo = graph->vkrinfo + i;
      mynbrs = ctrl->vnbrpool + myrinfo->inbr;

      from = where[i];

      /* Prevent moves that make 'from' domain underbalanced */
      if (omode == OMODE_REFINE) {
        if (myrinfo->nid > 0 &&
            !ivecaxpygez(ncon, -1, vwgt + i * ncon, pwgts + from * ncon,
                         minpwgts + from * ncon))
          continue;
      } else { /* OMODE_BALANCE */
        if (!ivecaxpygez(ncon, -1, vwgt + i * ncon, pwgts + from * ncon,
                         minpwgts + from * ncon))
          continue;
      }

      if (ctrl->contig &&
          IsArticulationNode(i, xadj, adjncy, where, bfslvl, bfsind, bfsmrk))
        continue;

      if (ctrl->minconn)
        SelectSafeTargetSubdomains(myrinfo, mynbrs, nads, adids, maxndoms,
                                   safetos, doms);

      xgain = (myrinfo->nid == 0 && myrinfo->ned > 0 ? graph->vsize[i] : 0);

      /* Find the most promising subdomain to move to */
      if (omode == OMODE_REFINE) {
        for (k = myrinfo->nnbrs - 1; k >= 0; k--) {
          if (!safetos[to = mynbrs[k].pid])
            continue;
          gain = mynbrs[k].gv + xgain;
          if (gain >= 0 && ivecaxpylez(ncon, 1, vwgt + i * ncon,
                                       pwgts + to * ncon, maxpwgts + to * ncon))
            break;
        }
        if (k < 0)
          continue; /* break out if you did not find a candidate */

        cto = to;
        for (j = k - 1; j >= 0; j--) {
          if (!safetos[to = mynbrs[j].pid])
            continue;
          gain = mynbrs[j].gv + xgain;
          if ((mynbrs[j].gv > mynbrs[k].gv &&
               ivecaxpylez(ncon, 1, vwgt + i * ncon, pwgts + to * ncon,
                           maxpwgts + to * ncon)) ||
              (mynbrs[j].gv == mynbrs[k].gv && mynbrs[j].ned > mynbrs[k].ned &&
               ivecaxpylez(ncon, 1, vwgt + i * ncon, pwgts + to * ncon,
                           maxpwgts + to * ncon)) ||
              (mynbrs[j].gv == mynbrs[k].gv && mynbrs[j].ned == mynbrs[k].ned &&
               BetterBalanceKWay(ncon, vwgt + i * ncon, ubfactors, 1,
                                 pwgts + cto * ncon, pijbm + cto * ncon, 1,
                                 pwgts + to * ncon, pijbm + to * ncon))) {
            k = j;
            cto = to;
          }
        }
        to = cto;

        j = 0;
        if (xgain + mynbrs[k].gv > 0 || mynbrs[k].ned - myrinfo->nid > 0)
          j = 1;
        else if (mynbrs[k].ned - myrinfo->nid == 0) {
          if ((iii % 2 == 0 && safetos[to] == 2) ||
              BetterBalanceKWay(ncon, vwgt + i * ncon, ubfactors, -1,
                                pwgts + from * ncon, pijbm + from * ncon, +1,
                                pwgts + to * ncon, pijbm + to * ncon))
            j = 1;
        }
        if (j == 0)
          continue;
      } else { /* OMODE_BALANCE */
        for (k = myrinfo->nnbrs - 1; k >= 0; k--) {
          if (!safetos[to = mynbrs[k].pid])
            continue;
          if (ivecaxpylez(ncon, 1, vwgt + i * ncon, pwgts + to * ncon,
                          maxpwgts + to * ncon) ||
              BetterBalanceKWay(ncon, vwgt + i * ncon, ubfactors, -1,
                                pwgts + from * ncon, pijbm + from * ncon, +1,
                                pwgts + to * ncon, pijbm + to * ncon))
            break;
        }
        if (k < 0)
          continue; /* break out if you did not find a candidate */

        cto = to;
        for (j = k - 1; j >= 0; j--) {
          if (!safetos[to = mynbrs[j].pid])
            continue;
          if (BetterBalanceKWay(ncon, vwgt + i * ncon, ubfactors, 1,
                                pwgts + cto * ncon, pijbm + cto * ncon, 1,
                                pwgts + to * ncon, pijbm + to * ncon)) {
            k = j;
            cto = to;
          }
        }
        to = cto;

        if ((xgain + mynbrs[k].gv < 0 ||
             (xgain + mynbrs[k].gv == 0 && mynbrs[k].ned - myrinfo->nid < 0)) &&
            !BetterBalanceKWay(ncon, vwgt + i * ncon, ubfactors, -1,
                               pwgts + from * ncon, pijbm + from * ncon, +1,
                               pwgts + to * ncon, pijbm + to * ncon))
          continue;
      }

      /*=====================================================================
       * If we got here, we can now move the vertex from 'from' to 'to'
       *======================================================================*/
      graph->mincut -= mynbrs[k].ned - myrinfo->nid;
      graph->minvol -= (xgain + mynbrs[k].gv);
      where[i] = to;
      nmoved++;

      IFSET(ctrl->dbglvl, METIS_DBG_MOVEINFO,
            printf("\t\tMoving %6" PRIDX " from %3" PRIDX " to %3" PRIDX ". "
                   "Gain: [%4" PRIDX " %4" PRIDX "]. Cut: %6" PRIDX
                   ", Vol: %6" PRIDX "\n",
                   i, from, to, xgain + mynbrs[k].gv,
                   mynbrs[k].ned - myrinfo->nid, graph->mincut, graph->minvol));

      /* Update the subdomain connectivity information */
      if (ctrl->minconn) {
        /* take care of i's move itself */
        UpdateEdgeSubDomainGraph(ctrl, from, to, myrinfo->nid - mynbrs[k].ned,
                                 &maxndoms);

        /* take care of the adjacent vertices */
        for (j = xadj[i]; j < xadj[i + 1]; j++) {
          me = where[adjncy[j]];
          if (me != from && me != to) {
            UpdateEdgeSubDomainGraph(ctrl, from, me, -1, &maxndoms);
            UpdateEdgeSubDomainGraph(ctrl, to, me, 1, &maxndoms);
          }
        }
      }

      /* Update pwgts */
      iaxpy(ncon, 1, vwgt + i * ncon, 1, pwgts + to * ncon, 1);
      iaxpy(ncon, -1, vwgt + i * ncon, 1, pwgts + from * ncon, 1);

      /* Update the id/ed/gains/bnd/queue of potentially affected nodes */
      KWayVolUpdate(ctrl, graph, i, from, to, queue, vstatus, &nupd, updptr,
                    updind, bndtype, vmarker, pmarker, modind);

      /*CheckKWayVolPartitionParams(ctrl, graph); */
    }

    /* Reset the vstatus and associated data structures */
    for (i = 0; i < nupd; i++) {
      ASSERT(updptr[updind[i]] != -1);
      ASSERT(vstatus[updind[i]] != VPQSTATUS_NOTPRESENT);
      vstatus[updind[i]] = VPQSTATUS_NOTPRESENT;
      updptr[updind[i]] = -1;
    }

    if (ctrl->dbglvl & METIS_DBG_REFINE) {
      printf("\t[%6" PRIDX " %6" PRIDX "], Bal: %5.3" PRREAL ", Nb: %6" PRIDX
             "."
             " Nmoves: %5" PRIDX ", Cut: %6" PRIDX ", Vol: %6" PRIDX,
             imin(nparts * ncon, pwgts, 1), imax(nparts * ncon, pwgts, 1),
             ComputeLoadImbalance(graph, nparts, pijbm), graph->nbnd, nmoved,
             graph->mincut, graph->minvol);
      if (ctrl->minconn)
        printf(", Doms: [%3" PRIDX " %4" PRIDX "]", imax(nparts, nads, 1),
               isum(nparts, nads, 1));
      printf("\n");
    }

    if (nmoved == 0 || (omode == OMODE_REFINE && graph->minvol == oldvol &&
                        graph->mincut == oldcut))
      break;
  }

  ipqDestroy(queue);

  WCOREPOP;
}

/*************************************************************************/
/*! This function performs an approximate articulation vertex test.
    It assumes that the bfslvl, bfsind, and bfsmrk arrays are initialized
    appropriately. */
/*************************************************************************/
idx_t IsArticulationNode(idx_t i, idx_t *xadj, idx_t *adjncy, idx_t *where,
                         idx_t *bfslvl, idx_t *bfsind, idx_t *bfsmrk) {
  idx_t ii, j, k = 0, head, tail, nhits, tnhits, from, BFSDEPTH = 5;

  from = where[i];

  /* Determine if the vertex is safe to move from a contiguity standpoint */
  for (tnhits = 0, j = xadj[i]; j < xadj[i + 1]; j++) {
    if (where[adjncy[j]] == from) {
      ASSERT(bfsmrk[adjncy[j]] == 0);
      ASSERT(bfslvl[adjncy[j]] == 0);
      bfsmrk[k = adjncy[j]] = 1;
      tnhits++;
    }
  }

  /* Easy cases */
  if (tnhits == 0)
    return 0;
  if (tnhits == 1) {
    bfsmrk[k] = 0;
    return 0;
  }

  ASSERT(bfslvl[i] == 0);
  bfslvl[i] = 1;

  bfsind[0] = k; /* That was the last one from the previous loop */
  bfslvl[k] = 1;
  bfsmrk[k] = 0;
  head = 0;
  tail = 1;

  /* Do a limited BFS traversal to see if you can get to all the other nodes */
  for (nhits = 1; head < tail;) {
    ii = bfsind[head++];
    for (j = xadj[ii]; j < xadj[ii + 1]; j++) {
      if (where[k = adjncy[j]] == from) {
        if (bfsmrk[k]) {
          bfsmrk[k] = 0;
          if (++nhits == tnhits)
            break;
        }
        if (bfslvl[k] == 0 && bfslvl[ii] < BFSDEPTH) {
          bfsind[tail++] = k;
          bfslvl[k] = bfslvl[ii] + 1;
        }
      }
    }
    if (nhits == tnhits)
      break;
  }

  /* Reset the various BFS related arrays */
  bfslvl[i] = 0;
  for (j = 0; j < tail; j++)
    bfslvl[bfsind[j]] = 0;

  /* Reset the bfsmrk array for the next vertex when has not already being
   * cleared */
  if (nhits < tnhits) {
    for (j = xadj[i]; j < xadj[i + 1]; j++)
      if (where[adjncy[j]] == from)
        bfsmrk[adjncy[j]] = 0;
  }

  return (nhits != tnhits);
}

/*************************************************************************/
/*!
 This function updates the edge and volume gains due to a vertex movement.
 v from 'from' to 'to'.

 \param ctrl is the control structure.
 \param graph is the graph being partitioned.
 \param v is the vertex that is moving.
 \param from is the original partition of v.
 \param to is the new partition of v.
 \param queue is the priority queue. If the queue is NULL, no priority-queue
        related updates are performed.
 \param vstatus is an array that marks the status of the vertex in terms
        of the priority queue. If queue is NULL, this parameter is ignored.
 \param r_nqupd is the number of vertices that have been inserted/removed
        from the queue. If queue is NULL, this parameter is ignored.
 \param updptr stores the index of each vertex in updind. If queue is NULL,
        this parameter is ignored.
 \param updind is the list of vertices that have been inserted/removed from
        the queue. If queue is NULL, this parameter is ignored.
 \param vmarker is of size nvtxs and is used internally as a temporary array.
        On entry and return all of its entries are 0.
 \param pmarker is of size nparts and is used internally as a temporary marking
        array. On entry and return all of its entries are -1.
 \param modind is an array of size nvtxs and is used to keep track of the
        list of vertices whose gains need to be updated.
*/
/*************************************************************************/
void KWayVolUpdate(ctrl_t *ctrl, graph_t *graph, idx_t v, idx_t from, idx_t to,
                   ipq_t *queue, idx_t *vstatus, idx_t *r_nupd, idx_t *updptr,
                   idx_t *updind, idx_t bndtype, idx_t *vmarker, idx_t *pmarker,
                   idx_t *modind) {
  idx_t i, ii, iii, j, jj, k, kk, l, u, nmod, other, me, myidx;
  idx_t *xadj, *vsize, *adjncy, *where;
  vkrinfo_t *myrinfo, *orinfo;
  vnbr_t *mynbrs, *onbrs;

  xadj = graph->xadj;
  adjncy = graph->adjncy;
  vsize = graph->vsize;
  where = graph->where;

  myrinfo = graph->vkrinfo + v;
  mynbrs = ctrl->vnbrpool + myrinfo->inbr;

  /*======================================================================
   * Remove the contributions on the gain made by 'v'.
   *=====================================================================*/
  for (k = 0; k < myrinfo->nnbrs; k++)
    pmarker[mynbrs[k].pid] = k;
  pmarker[from] = k;

  myidx =
      pmarker[to]; /* Keep track of the index in mynbrs of the 'to' domain */

  for (j = xadj[v]; j < xadj[v + 1]; j++) {
    ii = adjncy[j];
    other = where[ii];
    orinfo = graph->vkrinfo + ii;
    onbrs = ctrl->vnbrpool + orinfo->inbr;

    if (other == from) {
      for (k = 0; k < orinfo->nnbrs; k++) {
        if (pmarker[onbrs[k].pid] == -1)
          onbrs[k].gv += vsize[v];
      }
    } else {
      ASSERT(pmarker[other] != -1);

      if (mynbrs[pmarker[other]].ned > 1) {
        for (k = 0; k < orinfo->nnbrs; k++) {
          if (pmarker[onbrs[k].pid] == -1)
            onbrs[k].gv += vsize[v];
        }
      } else { /* There is only one connection */
        for (k = 0; k < orinfo->nnbrs; k++) {
          if (pmarker[onbrs[k].pid] != -1)
            onbrs[k].gv -= vsize[v];
        }
      }
    }
  }

  for (k = 0; k < myrinfo->nnbrs; k++)
    pmarker[mynbrs[k].pid] = -1;
  pmarker[from] = -1;

  /*======================================================================
   * Update the id/ed of vertex 'v'
   *=====================================================================*/
  if (myidx == -1) {
    myidx = myrinfo->nnbrs++;
    ASSERT(myidx < xadj[v + 1] - xadj[v]);
    mynbrs[myidx].ned = 0;
  }
  myrinfo->ned += myrinfo->nid - mynbrs[myidx].ned;
  SWAP(myrinfo->nid, mynbrs[myidx].ned, j);
  if (mynbrs[myidx].ned == 0)
    mynbrs[myidx] = mynbrs[--myrinfo->nnbrs];
  else
    mynbrs[myidx].pid = from;

  /*======================================================================
   * Update the degrees of adjacent vertices and their volume gains
   *=====================================================================*/
  vmarker[v] = 1;
  modind[0] = v;
  nmod = 1;
  for (j = xadj[v]; j < xadj[v + 1]; j++) {
    ii = adjncy[j];
    me = where[ii];

    if (!vmarker[ii]) { /* The marking is done for boundary and max gv
                           calculations */
      vmarker[ii] = 2;
      modind[nmod++] = ii;
    }

    myrinfo = graph->vkrinfo + ii;
    if (myrinfo->inbr == -1)
      myrinfo->inbr = vnbrpoolGetNext(ctrl, xadj[ii + 1] - xadj[ii]);
    mynbrs = ctrl->vnbrpool + myrinfo->inbr;

    if (me == from) {
      INC_DEC(myrinfo->ned, myrinfo->nid, 1);
    } else if (me == to) {
      INC_DEC(myrinfo->nid, myrinfo->ned, 1);
    }

    /* Remove the edgeweight from the 'pid == from' entry of the vertex */
    if (me != from) {
      for (k = 0; k < myrinfo->nnbrs; k++) {
        if (mynbrs[k].pid == from) {
          if (mynbrs[k].ned == 1) {
            mynbrs[k] = mynbrs[--myrinfo->nnbrs];
            vmarker[ii] = 1; /* You do a complete .gv calculation */

            /* All vertices adjacent to 'ii' need to be updated */
            for (jj = xadj[ii]; jj < xadj[ii + 1]; jj++) {
              u = adjncy[jj];
              other = where[u];
              orinfo = graph->vkrinfo + u;
              onbrs = ctrl->vnbrpool + orinfo->inbr;

              for (kk = 0; kk < orinfo->nnbrs; kk++) {
                if (onbrs[kk].pid == from) {
                  onbrs[kk].gv -= vsize[ii];
                  if (!vmarker[u]) { /* Need to update boundary etc */
                    vmarker[u] = 2;
                    modind[nmod++] = u;
                  }
                  break;
                }
              }
            }
          } else {
            mynbrs[k].ned--;

            /* Update the gv due to single 'ii' connection to 'from' */
            if (mynbrs[k].ned == 1) {
              /* find the vertex 'u' that 'ii' was connected into 'from' */
              for (jj = xadj[ii]; jj < xadj[ii + 1]; jj++) {
                u = adjncy[jj];
                other = where[u];

                if (other == from) {
                  orinfo = graph->vkrinfo + u;
                  onbrs = ctrl->vnbrpool + orinfo->inbr;

                  /* The following is correct because domains in common
                     between ii and u will lead to a reduction over the
                     previous gain, whereas domains only in u but not in
                     ii, will lead to no change as opposed to the earlier
                     increase */
                  for (kk = 0; kk < orinfo->nnbrs; kk++)
                    onbrs[kk].gv += vsize[ii];

                  if (!vmarker[u]) { /* Need to update boundary etc */
                    vmarker[u] = 2;
                    modind[nmod++] = u;
                  }
                  break;
                }
              }
            }
          }
          break;
        }
      }
    }

    /* Add the edgeweight to the 'pid == to' entry of the vertex */
    if (me != to) {
      for (k = 0; k < myrinfo->nnbrs; k++) {
        if (mynbrs[k].pid == to) {
          mynbrs[k].ned++;

          /* Update the gv due to non-single 'ii' connection to 'to' */
          if (mynbrs[k].ned == 2) {
            /* find the vertex 'u' that 'ii' was connected into 'to' */
            for (jj = xadj[ii]; jj < xadj[ii + 1]; jj++) {
              u = adjncy[jj];
              other = where[u];

              if (u != v && other == to) {
                orinfo = graph->vkrinfo + u;
                onbrs = ctrl->vnbrpool + orinfo->inbr;
                for (kk = 0; kk < orinfo->nnbrs; kk++)
                  onbrs[kk].gv -= vsize[ii];

                if (!vmarker[u]) { /* Need to update boundary etc */
                  vmarker[u] = 2;
                  modind[nmod++] = u;
                }
                break;
              }
            }
          }
          break;
        }
      }

      if (k == myrinfo->nnbrs) {
        mynbrs[myrinfo->nnbrs].pid = to;
        mynbrs[myrinfo->nnbrs++].ned = 1;
        vmarker[ii] = 1; /* You do a complete .gv calculation */

        /* All vertices adjacent to 'ii' need to be updated */
        for (jj = xadj[ii]; jj < xadj[ii + 1]; jj++) {
          u = adjncy[jj];
          other = where[u];
          orinfo = graph->vkrinfo + u;
          onbrs = ctrl->vnbrpool + orinfo->inbr;

          for (kk = 0; kk < orinfo->nnbrs; kk++) {
            if (onbrs[kk].pid == to) {
              onbrs[kk].gv += vsize[ii];
              if (!vmarker[u]) { /* Need to update boundary etc */
                vmarker[u] = 2;
                modind[nmod++] = u;
              }
              break;
            }
          }
        }
      }
    }

    ASSERT(myrinfo->nnbrs <= xadj[ii + 1] - xadj[ii]);
  }

  /*======================================================================
   * Add the contributions on the volume gain due to 'v'
   *=====================================================================*/
  myrinfo = graph->vkrinfo + v;
  mynbrs = ctrl->vnbrpool + myrinfo->inbr;
  for (k = 0; k < myrinfo->nnbrs; k++)
    pmarker[mynbrs[k].pid] = k;
  pmarker[to] = k;

  for (j = xadj[v]; j < xadj[v + 1]; j++) {
    ii = adjncy[j];
    other = where[ii];
    orinfo = graph->vkrinfo + ii;
    onbrs = ctrl->vnbrpool + orinfo->inbr;

    if (other == to) {
      for (k = 0; k < orinfo->nnbrs; k++) {
        if (pmarker[onbrs[k].pid] == -1)
          onbrs[k].gv -= vsize[v];
      }
    } else {
      ASSERT(pmarker[other] != -1);

      if (mynbrs[pmarker[other]].ned > 1) {
        for (k = 0; k < orinfo->nnbrs; k++) {
          if (pmarker[onbrs[k].pid] == -1)
            onbrs[k].gv -= vsize[v];
        }
      } else { /* There is only one connection */
        for (k = 0; k < orinfo->nnbrs; k++) {
          if (pmarker[onbrs[k].pid] != -1)
            onbrs[k].gv += vsize[v];
        }
      }
    }
  }
  for (k = 0; k < myrinfo->nnbrs; k++)
    pmarker[mynbrs[k].pid] = -1;
  pmarker[to] = -1;

  /*======================================================================
   * Recompute the volume information of the 'hard' nodes, and update the
   * max volume gain for all the modified vertices and the priority queue
   *=====================================================================*/
  for (iii = 0; iii < nmod; iii++) {
    i = modind[iii];
    me = where[i];

    myrinfo = graph->vkrinfo + i;
    mynbrs = ctrl->vnbrpool + myrinfo->inbr;

    if (vmarker[i] == 1) { /* Only complete gain updates go through */
      for (k = 0; k < myrinfo->nnbrs; k++)
        mynbrs[k].gv = 0;

      for (j = xadj[i]; j < xadj[i + 1]; j++) {
        ii = adjncy[j];
        other = where[ii];
        orinfo = graph->vkrinfo + ii;
        onbrs = ctrl->vnbrpool + orinfo->inbr;

        for (kk = 0; kk < orinfo->nnbrs; kk++)
          pmarker[onbrs[kk].pid] = kk;
        pmarker[other] = 1;

        if (me == other) {
          /* Find which domains 'i' is connected and 'ii' is not and update
           * their gain */
          for (k = 0; k < myrinfo->nnbrs; k++) {
            if (pmarker[mynbrs[k].pid] == -1)
              mynbrs[k].gv -= vsize[ii];
          }
        } else {
          ASSERT(pmarker[me] != -1);

          /* I'm the only connection of 'ii' in 'me' */
          if (onbrs[pmarker[me]].ned == 1) {
            /* Increase the gains for all the common domains between 'i' and
             * 'ii' */
            for (k = 0; k < myrinfo->nnbrs; k++) {
              if (pmarker[mynbrs[k].pid] != -1)
                mynbrs[k].gv += vsize[ii];
            }
          } else {
            /* Find which domains 'i' is connected and 'ii' is not and update
             * their gain */
            for (k = 0; k < myrinfo->nnbrs; k++) {
              if (pmarker[mynbrs[k].pid] == -1)
                mynbrs[k].gv -= vsize[ii];
            }
          }
        }

        for (kk = 0; kk < orinfo->nnbrs; kk++)
          pmarker[onbrs[kk].pid] = -1;
        pmarker[other] = -1;
      }
    }

    /* Compute the overall gv for that node */
    myrinfo->gv = IDX_MIN;
    for (k = 0; k < myrinfo->nnbrs; k++) {
      if (mynbrs[k].gv > myrinfo->gv)
        myrinfo->gv = mynbrs[k].gv;
    }

    /* Add the xtra gain due to id == 0 */
    if (myrinfo->ned > 0 && myrinfo->nid == 0)
      myrinfo->gv += vsize[i];

    /*======================================================================
     * Maintain a consistent boundary
     *=====================================================================*/
    if (bndtype == BNDTYPE_REFINE) {
      if (myrinfo->gv >= 0 && graph->bndptr[i] == -1)
        BNDInsert(graph->nbnd, graph->bndind, graph->bndptr, i);

      if (myrinfo->gv < 0 && graph->bndptr[i] != -1)
        BNDDelete(graph->nbnd, graph->bndind, graph->bndptr, i);
    } else {
      if (myrinfo->ned > 0 && graph->bndptr[i] == -1)
        BNDInsert(graph->nbnd, graph->bndind, graph->bndptr, i);

      if (myrinfo->ned == 0 && graph->bndptr[i] != -1)
        BNDDelete(graph->nbnd, graph->bndind, graph->bndptr, i);
    }

    /*======================================================================
     * Update the priority queue appropriately (if allowed)
     *=====================================================================*/
    if (queue != NULL) {
      if (vstatus[i] != VPQSTATUS_EXTRACTED) {
        if (graph->bndptr[i] != -1) { /* In-boundary vertex */
          if (vstatus[i] == VPQSTATUS_PRESENT) {
            ipqUpdate(queue, i, myrinfo->gv);
          } else {
            ipqInsert(queue, i, myrinfo->gv);
            vstatus[i] = VPQSTATUS_PRESENT;
            ListInsert(*r_nupd, updind, updptr, i);
          }
        } else { /* Off-boundary vertex */
          if (vstatus[i] == VPQSTATUS_PRESENT) {
            ipqDelete(queue, i);
            vstatus[i] = VPQSTATUS_NOTPRESENT;
            ListDelete(*r_nupd, updind, updptr, i);
          }
        }
      }
    }

    vmarker[i] = 0;
  }
}

/*************************************************************************/
/*! K-way partitioning optimization in which the vertices are visited in
    decreasing ed/sqrt(nnbrs)-id order. Note this is just an
    approximation, as the ed is often split across different subdomains
    and the sqrt(nnbrs) is just a crude approximation.

  \param graph is the graph that is being refined.
  \param niter is the number of refinement iterations.
  \param ffactor is the \em fudge-factor for allowing positive gain moves
         to violate the max-pwgt constraint.
  \param omode is the type of optimization that will performed among
         OMODE_REFINE and OMODE_BALANCE


*/
/**************************************************************************/
void Greedy_KWayEdgeStats(ctrl_t *ctrl, graph_t *graph) {
  /* Common variables to all types of kway-refinement/balancing routines */
  idx_t i, ii, iii, j, k, l, nvtxs, nparts, gain, u, v, uw, vw;
  idx_t *xadj, *adjncy, *adjwgt, *vwgt;
  idx_t *where, *pwgts, *bndptr, *bndind, *minpwgts, *maxpwgts;
  idx_t nbnd;
  ckrinfo_t *urinfo, *vrinfo;
  cnbr_t *unbrs, *vnbrs;
  real_t *tpwgts, ubfactor;

  WCOREPUSH;

  /* Link the graph fields */
  nvtxs = graph->nvtxs;
  xadj = graph->xadj;
  adjncy = graph->adjncy;
  vwgt = graph->vwgt;
  adjwgt = graph->adjwgt;

  bndind = graph->bndind;
  bndptr = graph->bndptr;

  where = graph->where;
  pwgts = graph->pwgts;

  nparts = ctrl->nparts;
  tpwgts = ctrl->tpwgts;

  /* Setup the weight intervals of the various subdomains */
  minpwgts = iwspacemalloc(ctrl, nparts);
  maxpwgts = iwspacemalloc(ctrl, nparts);

  ubfactor = ctrl->ubfactors[0];
  for (i = 0; i < nparts; i++) {
    maxpwgts[i] = tpwgts[i] * graph->tvwgt[0] * ubfactor;
    minpwgts[i] = tpwgts[i] * graph->tvwgt[0] * (0.95 / ubfactor);
  }

  /* go and determine the positive gain valid swaps */
  nbnd = graph->nbnd;

  for (ii = 0; ii < nbnd; ii++) {
    u = bndind[ii];
    uw = where[u];

    urinfo = graph->ckrinfo + u;
    unbrs = ctrl->cnbrpool + urinfo->inbr;

    for (j = xadj[u]; j < xadj[u + 1]; j++) {
      v = adjncy[j];
      vw = where[v];

      vrinfo = graph->ckrinfo + v;
      vnbrs = ctrl->cnbrpool + vrinfo->inbr;

      if (uw == vw)
        continue;
      if (pwgts[uw] - vwgt[u] + vwgt[v] > maxpwgts[uw] ||
          pwgts[vw] - vwgt[v] + vwgt[u] > maxpwgts[vw])
        continue;

      for (k = urinfo->nnbrs - 1; k >= 0; k--) {
        if (unbrs[k].pid == vw)
          break;
      }
      if (k < 0)
        printf("Something went wrong!\n");
      gain = unbrs[k].ed - urinfo->id;

      for (k = vrinfo->nnbrs - 1; k >= 0; k--) {
        if (vnbrs[k].pid == uw)
          break;
      }
      if (k < 0)
        printf("Something went wrong!\n");
      gain += vnbrs[k].ed - vrinfo->id;

      gain -= 2 * adjwgt[j];

      if (gain > 0)
        printf("  Gain: %" PRIDX " for moving (%" PRIDX ", %" PRIDX
               ") between (%" PRIDX ", %" PRIDX ")\n",
               gain, u, v, uw, vw);
    }
  }

  WCOREPOP;
}

/*************************************************************************/
/*! K-way partitioning optimization in which the vertices are visited in
    random order and the best edge is selected to swap its incident vertices

  \param graph is the graph that is being refined.
  \param niter is the number of refinement iterations.

*/
/**************************************************************************/
void Greedy_KWayEdgeCutOptimize(ctrl_t *ctrl, graph_t *graph, idx_t niter) {
  /* Common variables to all types of kway-refinement/balancing routines */
  idx_t ii, j, k, pass, nvtxs, nparts, u, v, uw, vw, gain, bestgain, jbest;
  idx_t from, me, to, oldcut, nmoved;
  idx_t *xadj, *adjncy, *adjwgt, *vwgt;
  idx_t *where, *pwgts, *perm, *bndptr, *bndind, *minpwgts, *maxpwgts;
  idx_t bndtype = BNDTYPE_REFINE;
  real_t *tpwgts, ubfactor;

  /* Edgecut-specific/different variables */
  idx_t nbnd, oldnnbrs;
  ckrinfo_t *myrinfo, *urinfo, *vrinfo;
  cnbr_t *unbrs, *vnbrs;

  WCOREPUSH;

  /* Link the graph fields */
  nvtxs = graph->nvtxs;
  xadj = graph->xadj;
  adjncy = graph->adjncy;
  adjwgt = graph->adjwgt;
  vwgt = graph->vwgt;

  bndind = graph->bndind;
  bndptr = graph->bndptr;

  where = graph->where;
  pwgts = graph->pwgts;

  nparts = ctrl->nparts;
  tpwgts = ctrl->tpwgts;

  /* Setup the weight intervals of the various subdomains */
  minpwgts = iwspacemalloc(ctrl, nparts);
  maxpwgts = iwspacemalloc(ctrl, nparts);

  ubfactor = gk_max(ctrl->ubfactors[0],
                    ComputeLoadImbalance(graph, nparts, ctrl->pijbm));
  for (k = 0; k < nparts; k++) {
    maxpwgts[k] = tpwgts[k] * graph->tvwgt[0] * ubfactor;
    minpwgts[k] = tpwgts[k] * graph->tvwgt[0] * (1.0 / ubfactor);
  }

  perm = iwspacemalloc(ctrl, nvtxs);

  if (ctrl->dbglvl & METIS_DBG_REFINE) {
    printf("GRE: [%6" PRIDX " %6" PRIDX "]-[%6" PRIDX " %6" PRIDX
           "], Bal: %5.3" PRREAL ","
           " Nv-Nb[%6" PRIDX " %6" PRIDX "], Cut: %6" PRIDX "\n",
           pwgts[iargmin(nparts, pwgts, 1)], imax(nparts, pwgts, 1),
           minpwgts[0], maxpwgts[0],
           ComputeLoadImbalance(graph, nparts, ctrl->pijbm), graph->nvtxs,
           graph->nbnd, graph->mincut);
  }

  /*=====================================================================
   * The top-level refinement loop
   *======================================================================*/
  for (pass = 0; pass < niter; pass++) {
    GKASSERT(ComputeCut(graph, where) == graph->mincut);

    oldcut = graph->mincut;
    nbnd = graph->nbnd;
    nmoved = 0;

    /* Insert the boundary vertices in the priority queue */
    /* Visit the vertices in random order and see if you can swap them */
    irandArrayPermute(nvtxs, perm, nbnd, 1);
    for (ii = 0; ii < nvtxs; ii++) {
      if (bndptr[u = perm[ii]] == -1)
        continue;

      uw = where[u];

      urinfo = graph->ckrinfo + u;
      unbrs = ctrl->cnbrpool + urinfo->inbr;

      bestgain = 0;
      jbest = -1;
      for (j = xadj[u]; j < xadj[u + 1]; j++) {
        v = adjncy[j];
        vw = where[v];

        if (uw == vw)
          continue;
        if (pwgts[uw] - vwgt[u] + vwgt[v] > maxpwgts[uw] ||
            pwgts[vw] - vwgt[v] + vwgt[u] > maxpwgts[vw])
          continue;
        if (pwgts[uw] - vwgt[u] + vwgt[v] < minpwgts[uw] ||
            pwgts[vw] - vwgt[v] + vwgt[u] < minpwgts[vw])
          continue;

        vrinfo = graph->ckrinfo + v;
        vnbrs = ctrl->cnbrpool + vrinfo->inbr;

        gain = -2 * adjwgt[j];

        for (k = urinfo->nnbrs - 1; k >= 0; k--) {
          if (unbrs[k].pid == vw)
            break;
        }
        GKASSERT(k >= 0);
        gain += unbrs[k].ed - urinfo->id;

        for (k = vrinfo->nnbrs - 1; k >= 0; k--) {
          if (vnbrs[k].pid == uw)
            break;
        }
        GKASSERT(k >= 0);
        gain += vnbrs[k].ed - vrinfo->id;

        if (gain > bestgain && vnbrs[k].ed > adjwgt[j]) {
          bestgain = gain;
          jbest = j;
        }
      }

      if (jbest == -1)
        continue; /* no valid positive swap */

      /*=====================================================================
       * If we got here, we can now swap the vertices
       *======================================================================*/
      v = adjncy[jbest];
      vw = where[v];

      vrinfo = graph->ckrinfo + v;
      vnbrs = ctrl->cnbrpool + vrinfo->inbr;

      /* move u to v's partition */
      for (k = urinfo->nnbrs - 1; k >= 0; k--) {
        if (unbrs[k].pid == vw)
          break;
      }
      GKASSERT(k >= 0);

      from = uw;
      to = vw;

      graph->mincut -= unbrs[k].ed - urinfo->id;
      nmoved++;

      IFSET(ctrl->dbglvl, METIS_DBG_MOVEINFO,
            printf("\t\tMoving %6" PRIDX " from %3" PRIDX " to %3" PRIDX
                   " [%6" PRIDX " %6" PRIDX "]. Gain: %4" PRIDX
                   ". Cut: %6" PRIDX "\n",
                   u, from, to, pwgts[from], pwgts[to],
                   unbrs[k].ed - urinfo->id, graph->mincut));

      /* Update ID/ED and BND related information for the moved vertex */
      INC_DEC(pwgts[to], pwgts[from], vwgt[u]);
      UpdateMovedVertexInfoAndBND(u, from, k, to, urinfo, unbrs, where, nbnd,
                                  bndptr, bndind, bndtype);

      /* Update the degrees of adjacent vertices */
      for (j = xadj[u]; j < xadj[u + 1]; j++) {
        ii = adjncy[j];
        me = where[ii];
        myrinfo = graph->ckrinfo + ii;

        oldnnbrs = myrinfo->nnbrs;

        UpdateAdjacentVertexInfoAndBND(ctrl, ii, xadj[ii + 1] - xadj[ii], me,
                                       from, to, myrinfo, adjwgt[j], nbnd,
                                       bndptr, bndind, bndtype);

        ASSERT(myrinfo->nnbrs <= xadj[ii + 1] - xadj[ii]);
      }

      /* move v to u's partition */
      for (k = vrinfo->nnbrs - 1; k >= 0; k--) {
        if (vnbrs[k].pid == uw)
          break;
      }
      GKASSERT(k >= 0);
#ifdef XXX
      if (k < 0) { /* that was removed, go and re-insert it */
        k = vrinfo->nnbrs++;
        vnbrs[k].pid = uw;
        vnbrs[k].ed = 0;
      }
#endif

      from = vw;
      to = uw;

      graph->mincut -= vnbrs[k].ed - vrinfo->id;
      nmoved++;

      IFSET(ctrl->dbglvl, METIS_DBG_MOVEINFO,
            printf("\t\tMoving %6" PRIDX " from %3" PRIDX " to %3" PRIDX
                   " [%6" PRIDX " %6" PRIDX "]. Gain: %4" PRIDX
                   ". Cut: %6" PRIDX "\n",
                   v, from, to, pwgts[from], pwgts[to],
                   vnbrs[k].ed - vrinfo->id, graph->mincut));

      /* Update ID/ED and BND related information for the moved vertex */
      INC_DEC(pwgts[to], pwgts[from], vwgt[v]);
      UpdateMovedVertexInfoAndBND(v, from, k, to, vrinfo, vnbrs, where, nbnd,
                                  bndptr, bndind, bndtype);

      /* Update the degrees of adjacent vertices */
      for (j = xadj[v]; j < xadj[v + 1]; j++) {
        ii = adjncy[j];
        me = where[ii];
        myrinfo = graph->ckrinfo + ii;

        oldnnbrs = myrinfo->nnbrs;

        UpdateAdjacentVertexInfoAndBND(ctrl, ii, xadj[ii + 1] - xadj[ii], me,
                                       from, to, myrinfo, adjwgt[j], nbnd,
                                       bndptr, bndind, bndtype);

        ASSERT(myrinfo->nnbrs <= xadj[ii + 1] - xadj[ii]);
      }
    }

    graph->nbnd = nbnd;

    if (ctrl->dbglvl & METIS_DBG_REFINE) {
      printf("\t[%6" PRIDX " %6" PRIDX "], Bal: %5.3" PRREAL ", Nb: %6" PRIDX
             "."
             " Nmoves: %5" PRIDX ", Cut: %6" PRIDX ", Vol: %6" PRIDX "\n",
             pwgts[iargmin(nparts, pwgts, 1)], imax(nparts, pwgts, 1),
             ComputeLoadImbalance(graph, nparts, ctrl->pijbm), graph->nbnd,
             nmoved, graph->mincut, ComputeVolume(graph, where));
    }

    if (nmoved == 0 || graph->mincut == oldcut)
      break;
  }

  WCOREPOP;
}

/*************************************************************************/
/*! K-way FM refinement for multi-objective partitioning.
 *
 *  Decomposes the edge cut into ncon*(ncon+1)/2 pair objectives (one per
 *  physics-type pair).  A single combined FM pass is run over the union of
 *  all pair-objective boundary sets.  Vertex priority in the heap uses a
 *  sqrt-normalised gain: sum_j w_j * (ed_j/sqrt(nnbrs_j) - id_j).
 *
 *  Two target-selection modes (ctrl->mobj_lex):
 *    0 -- combined gain: pick target with maximum weighted sum gain.
 *    1 -- lexicographic: narrow candidate set from highest to lowest
 *         priority objective; use combined gain only as acceptance gate.
 *
 *  Priority weights come from ctrl->mobj_prio (hex nibble sequence, LSB-first).
 */
void Greedy_MObjKWayCutOptimize(ctrl_t *ctrl, graph_t *graph, idx_t niter,
                                real_t ffactor, idx_t omode) {
  /* Common variables */
  idx_t i, ii, iii, j, k, l, pass, nvtxs, nparts, ncon;
  idx_t from, me, to, oldcut, c;
  idx_t *xadj, *adjncy, *adjwgt;
  idx_t *where, *pwgts, *perm, *bndptr, *bndind, *minpwgts, *maxpwgts;
  idx_t nmoved, nupd, *vstatus, *updptr, *updind;
  idx_t maxndoms = 0, *safetos = NULL, *nads = NULL, *doms = NULL, **adids = NULL;
  idx_t *bfslvl = NULL, *bfsind = NULL, *bfsmrk = NULL;
  idx_t bndtype = (omode == OMODE_REFINE ? BNDTYPE_REFINE : BNDTYPE_BALANCE);
  real_t *tpwgts, ubfactor;

  /* Multi-objective specific */
  idx_t nbnd, oldnnbrs;
  rpq_t *queue;
  real_t rgain;
  ckrinfo_t *myrinfo;
  cnbr_t *mynbrs;

  /* Storage for all objectives */
  ckrinfo_t *all_ckrinfo, *orig_ckrinfo;
  idx_t *all_bndptr, *orig_bndptr;
  idx_t *all_bndind, *orig_bndind;
  idx_t *all_nbnd, orig_nbnd;
  idx_t *skipped;
  idx_t nskipped = 0;
  idx_t **adwgts = NULL;

  /* Interaction-pair objectives */
  idx_t nobj;
  idx_t *pair_a, *pair_b;

  WCOREPUSH;

  nvtxs = graph->nvtxs;
  ncon = graph->ncon;
  nparts = ctrl->nparts;
  xadj = graph->xadj;
  adjncy = graph->adjncy;
  adjwgt = graph->adjwgt;
  where = graph->where;
  pwgts = graph->pwgts;
  tpwgts = ctrl->tpwgts;

  /* B1: Compute interaction pairs */
  nobj = ncon * (ncon + 1) / 2;
  pair_a = iwspacemalloc(ctrl, nobj);
  pair_b = iwspacemalloc(ctrl, nobj);
  {
    idx_t obj = 0;
    for (idx_t a = 0; a < ncon; a++) {
      for (idx_t b = a; b < ncon; b++) {
        pair_a[obj] = a;
        pair_b[obj] = b;
        obj++;
      }
    }
  }

  /* B2: Compute per-objective weights from mobj_prio.
     mobj_prio encodes priority as a nibble sequence (LSB-first); later position
     in obj_order = higher influence = higher weight.  Weight for objective at
     position k in obj_order is (k+1), so the last-listed objective (most
     influential in sequential mode) gets the highest weight nobj.
     With mobj_prio=0 all objectives get equal weight 1. */
  real_t *obj_weight = (real_t *)wspacemalloc(ctrl, nobj * sizeof(real_t));
  idx_t *obj_order   = iwspacemalloc(ctrl, nobj);
  {
    idx_t *used      = iset(nobj, 0, iwspacemalloc(ctrl, nobj));
    idx_t  n_ordered = 0;
    idx_t  prio_val  = ctrl->mobj_prio;

    while (prio_val > 0 && n_ordered < nobj) {
      idx_t oid = prio_val & 0xF;
      prio_val >>= 4;
      if (oid < nobj && !used[oid]) {
        obj_order[n_ordered++] = oid;
        used[oid] = 1;
      }
    }
    for (idx_t x = 0; x < nobj; x++) {
      if (!used[x])
        obj_order[n_ordered++] = x;
    }

    if (ctrl->mobj_prio == 0) {
      /* No priority: equal weights */
      for (idx_t x = 0; x < nobj; x++)
        obj_weight[x] = 1.0;
    } else {
      /* Position k in obj_order -> weight (k+1); last = nobj (most important) */
      for (idx_t k = 0; k < nobj; k++)
        obj_weight[obj_order[k]] = (real_t)(k + 1);
    }
  }

  /* B3: Allocate storage for each objective (nobj instead of ncon) */
  all_ckrinfo = (ckrinfo_t *)wspacemalloc(ctrl, nobj * nvtxs * sizeof(ckrinfo_t));
  all_bndptr = iset(nobj * nvtxs, -1, iwspacemalloc(ctrl, nobj * nvtxs));
  all_bndind = iwspacemalloc(ctrl, nobj * nvtxs);
  all_nbnd = iset(nobj, 0, iwspacemalloc(ctrl, nobj));
  skipped = iwspacemalloc(ctrl, nvtxs);

  /* Save original pointers */
  orig_ckrinfo = graph->ckrinfo;
  orig_bndptr = graph->bndptr;
  orig_bndind = graph->bndind;
  orig_nbnd = graph->nbnd;

  /* Setup weight intervals (still based on ncon constraints) */
  minpwgts = iwspacemalloc(ctrl, nparts * ncon);
  maxpwgts = iwspacemalloc(ctrl, nparts * ncon);

  for (c = 0; c < ncon; c++) {
    if (omode == OMODE_BALANCE)
      ubfactor = ctrl->ubfactors[c];
    else
      ubfactor = gk_max(ctrl->ubfactors[c],
                        ComputeLoadImbalance(graph, nparts, ctrl->pijbm));

    for (i = 0; i < nparts; i++) {
      maxpwgts[i * ncon + c] = tpwgts[i * ncon + c] * graph->tvwgt[c] * ubfactor;
      minpwgts[i * ncon + c] = tpwgts[i * ncon + c] * graph->tvwgt[c] * (1.0 / ubfactor);
    }
  }

  perm = iwspacemalloc(ctrl, nvtxs);
  safetos = iset(nparts, 2, iwspacemalloc(ctrl, nparts));

  if (ctrl->minconn) {
    ComputeSubDomainGraph(ctrl, graph);
    nads = ctrl->nads;
    adids = ctrl->adids;
    adwgts = ctrl->adwgts;
    doms = iset(nparts, 0, ctrl->pvec1);
  }

  vstatus = iset(nvtxs, VPQSTATUS_NOTPRESENT, iwspacemalloc(ctrl, nvtxs));
  updptr = iset(nvtxs, -1, iwspacemalloc(ctrl, nvtxs));
  updind = iwspacemalloc(ctrl, nvtxs);

  if (ctrl->contig) {
    bfslvl = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));
    bfsind = iwspacemalloc(ctrl, nvtxs);
    bfsmrk = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));
  }

  queue = rpqCreate(nvtxs);

  /*=====================================================================
   * INITIALIZATION: Compute ckrinfo and boundary for each pair objective
   *======================================================================*/
  /* Reset the neighbor pool -- MOBJ rebuilds all ckrinfo from scratch,
     and without this, successive calls at the same level accumulate
     entries until the pool overflows. */
  cnbrpoolReset(ctrl);

  for (idx_t oi = 0; oi < nobj; oi++) {
    idx_t ca = pair_a[oi];
    idx_t cb = pair_b[oi];
    idx_t current_nbnd = 0;

    graph->ckrinfo = all_ckrinfo + oi * nvtxs;
    graph->bndptr = all_bndptr + oi * nvtxs;
    graph->bndind = all_bndind + oi * nvtxs;
    bndptr = graph->bndptr;
    bndind = graph->bndind;

    /* Initialize ckrinfo for each vertex */
    for (i = 0; i < nvtxs; i++) {
      myrinfo = graph->ckrinfo + i;
      myrinfo->inbr = -1;
      myrinfo->ed = 0;
      myrinfo->id = 0;
      myrinfo->nnbrs = 0;
    }

    /* Build neighbor info for this pair objective */
    for (i = 0; i < nvtxs; i++) {
      from = where[i];
      myrinfo = graph->ckrinfo + i;

      for (j = xadj[i]; j < xadj[i + 1]; j++) {
        ii = adjncy[j];
        to = where[ii];

        /* B4: Edge relevance filter for interaction pair (ca, cb) */
        idx_t vi_a = graph->vwgt[i * ncon + ca];
        idx_t vi_b = graph->vwgt[i * ncon + cb];
        idx_t vii_a = graph->vwgt[ii * ncon + ca];
        idx_t vii_b = graph->vwgt[ii * ncon + cb];

        int relevant;
        if (ca == cb)
          relevant = (vi_a > 0 && vii_a > 0);      /* both endpoints same type */
        else
          relevant = (vi_a > 0 && vii_b > 0) || (vi_b > 0 && vii_a > 0);  /* cross-type */

        if (!relevant)
          continue;

        idx_t ewgt = adjwgt[j];

        if (from == to) {
          myrinfo->id += ewgt;
        } else {
          myrinfo->ed += ewgt;

          /* Update neighbor info */
          if (myrinfo->inbr == -1) {
            myrinfo->inbr = cnbrpoolGetNext(ctrl, xadj[i + 1] - xadj[i]);
            myrinfo->nnbrs = 0;
          }

          mynbrs = ctrl->cnbrpool + myrinfo->inbr;

          /* Find or create neighbor entry */
          for (k = 0; k < myrinfo->nnbrs; k++) {
            if (mynbrs[k].pid == to) {
              mynbrs[k].ed += ewgt;
              break;
            }
          }

          if (k == myrinfo->nnbrs) {
            mynbrs[k].pid = to;
            mynbrs[k].ed = ewgt;
            myrinfo->nnbrs++;
          }
        }
      }

      /* Add to boundary if has external edges */
      if (myrinfo->ed > 0) {
        BNDInsert(current_nbnd, bndind, bndptr, i);
      }
    }

    all_nbnd[oi] = current_nbnd;
  }

  /*=====================================================================
   * Precompute per-vertex constraint index (one-hot assumption).
   * vtx_con[i] = constraint index for vertex i (-1 if none/multi).
   *======================================================================*/
  idx_t *vtx_con = iwspacemalloc(ctrl, nvtxs);
  for (i = 0; i < nvtxs; i++) {
    vtx_con[i] = -1;
    for (c = 0; c < ncon; c++) {
      if (graph->vwgt[i * ncon + c] > 0) {
        vtx_con[i] = c;
        break;
      }
    }
  }

  /*=====================================================================
   * Workspace for combined FM: per-partition gain accumulators and
   * combined boundary tracking.
   *======================================================================*/
  real_t *part_cgain   = (real_t *)wspacemalloc(ctrl, nparts * sizeof(real_t));
  /* Per-objective per-partition ed accumulator for lex mode */
  real_t *part_obj_ed  = (real_t *)wspacemalloc(ctrl, nobj * nparts * sizeof(real_t));
  idx_t  *part_seen    = iwspacemalloc(ctrl, nparts);
  idx_t  *valid_pids   = iwspacemalloc(ctrl, nparts);  /* balance-safe subset of part_seen */
  idx_t  *part_flag    = iset(nparts, 0, iwspacemalloc(ctrl, nparts));
  idx_t  *cbndind      = iwspacemalloc(ctrl, nvtxs);  /* combined boundary list */
  idx_t  *in_cbnd      = iset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));

/* Combined weighted gain for vertex v: sum_oj w_oj*(ed_oj/sqrt(nnbrs_oj) - id_oj).
   Only objectives involving vtx_con[v] contribute (one-hot assumption).
   Weights come from mobj_prio: later in priority order -> higher weight. */
#define MOBJ_CGAIN(v, g) do {                                               \
    idx_t _mc = vtx_con[(v)];                                               \
    (g) = 0.0;                                                              \
    for (idx_t _oj = 0; _oj < nobj; _oj++) {                               \
      if (_mc >= 0 && _mc != pair_a[_oj] && _mc != pair_b[_oj]) continue;  \
      ckrinfo_t *_ri = all_ckrinfo + _oj * nvtxs + (v);                    \
      (g) += obj_weight[_oj] * (((_ri->nnbrs > 0)                          \
               ? 1.0 * _ri->ed / sqrt(_ri->nnbrs) : 0.0) - _ri->id);      \
    }                                                                       \
  } while (0)

  /*=====================================================================
   * Combined single-pass FM refinement.
   * One priority queue over the union of all objectives' boundary sets.
   * Gain = weighted sum across all relevant objectives.
   * Move selection maximizes combined gain subject to balance constraints.
   *======================================================================*/
  for (pass = 0; pass < niter; pass++) {

    /* Build combined boundary: union of all per-objective boundary sets */
    idx_t n_cbnd = 0;
    iset(nvtxs, 0, in_cbnd);
    for (idx_t oi = 0; oi < nobj; oi++) {
      idx_t *bnd_oi = all_bndind + oi * nvtxs;
      for (idx_t bi = 0; bi < all_nbnd[oi]; bi++) {
        idx_t v = bnd_oi[bi];
        if (!in_cbnd[v]) {
          in_cbnd[v] = 1;
          cbndind[n_cbnd++] = v;
        }
      }
    }

    if (ctrl->minconn)
      maxndoms = imax(nparts, nads, 1);

    /* Reset priority queue */
    rpqReset(queue);
    iset(nvtxs, VPQSTATUS_NOTPRESENT, vstatus);
    nupd = 0;

    /* Insert combined boundary vertices with combined gain */
    if (n_cbnd > 0) {
      irandArrayPermute(n_cbnd, perm, n_cbnd / 4, 1);
      for (ii = 0; ii < n_cbnd; ii++) {
        i = cbndind[perm[ii]];
        MOBJ_CGAIN(i, rgain);
        rpqInsert(queue, i, rgain);
        vstatus[i] = VPQSTATUS_PRESENT;
        ListInsert(nupd, updind, updptr, i);
      }
    }

    nskipped = 0;

    /* FM loop */
    for (nmoved = 0, iii = 0;; iii++) {
      if ((i = rpqGetTop(queue)) == -1)
        break;

      vstatus[i] = VPQSTATUS_EXTRACTED;
      from = where[i];

      /* Articulation check */
      if (ctrl->contig &&
          IsArticulationNode(i, xadj, adjncy, where, bfslvl, bfsind, bfsmrk))
        continue;

      /* minconn: combined FM uses all safetos=2 (allow all moves); the
         per-subdomain-graph bookkeeping is not updated per-objective here. */
      if (ctrl->minconn)
        iset(nparts, 2, safetos);

      /* Collect candidate 'to' partitions from all objectives' neighbor lists.
         part_cgain[pid] = sum_oj ed_oj_to_pid(i) - sum_oj id_oj(i). */
      idx_t n_seen = 0;
      real_t sum_id = 0.0;
      idx_t mc = vtx_con[i];

      for (idx_t oj = 0; oj < nobj; oj++) {
        if (mc >= 0 && mc != pair_a[oj] && mc != pair_b[oj]) continue;
        ckrinfo_t *ri = all_ckrinfo + oj * nvtxs + i;
        real_t woj = obj_weight[oj];
        sum_id += woj * ri->id;
        if (ri->inbr == -1) continue;
        cnbr_t *nbrs = ctrl->cnbrpool + ri->inbr;
        for (k = 0; k < ri->nnbrs; k++) {
          idx_t pid = nbrs[k].pid;
          if (!part_flag[pid]) {
            part_flag[pid] = 1;
            part_cgain[pid] = 0.0;
            for (idx_t ox = 0; ox < nobj; ox++)
              part_obj_ed[ox * nparts + pid] = 0.0;
            part_seen[n_seen++] = pid;
          }
          part_cgain[pid] += woj * nbrs[k].ed;
          part_obj_ed[oj * nparts + pid] += nbrs[k].ed;
        }
      }
      /* Subtract weighted id sum (constant offset per candidate pid) */
      for (idx_t si = 0; si < n_seen; si++)
        part_cgain[part_seen[si]] -= sum_id;

      /* Find best valid 'to' */
      idx_t best_to = -1;

      if (!ctrl->mobj_lex) {
        /* Combined gain mode: pick target with max weighted combined gain */
        real_t best_gain = 0.0;
        for (idx_t si = 0; si < n_seen; si++) {
          idx_t pid = part_seen[si];
          part_flag[pid] = 0;  /* reset flag inline */

          if (!safetos[pid]) continue;

          idx_t safe = 1;
          for (c = 0; c < ncon; c++) {
            if (pwgts[pid * ncon + c] + graph->vwgt[i * ncon + c]
                > maxpwgts[pid * ncon + c]) {
              safe = 0; break;
            }
          }
          if (!safe) continue;

          if (part_cgain[pid] > best_gain) {
            best_gain = part_cgain[pid];
            best_to   = pid;
          }
        }
      } else {
        /* Lex mode: try objectives in priority order (most important first).
         * Pre-filter balance-safe pids once, then the priority loop is O(nobj*n_valid). */
        for (idx_t si = 0; si < n_seen; si++)
          part_flag[part_seen[si]] = 0;  /* reset flags */

        /* Build valid_pids: partitions that pass balance, safetos, and combined
         * gain > 0 checks. Requiring positive combined gain keeps acceptance
         * rate equal to combined FM (avoids oscillation / excess moves). */
        idx_t n_valid = 0;
        for (idx_t si = 0; si < n_seen; si++) {
          idx_t pid = part_seen[si];
          if (!safetos[pid]) continue;
          if (part_cgain[pid] <= 0.0) continue;  /* require net improvement */
          idx_t safe = 1;
          for (c = 0; c < ncon; c++) {
            if (pwgts[pid * ncon + c] + graph->vwgt[i * ncon + c]
                > maxpwgts[pid * ncon + c]) {
              safe = 0; break;
            }
          }
          if (safe) valid_pids[n_valid++] = pid;
        }

        /* True lexicographic selection: iterate priorities high->low, each
         * level narrows the candidate set to targets achieving the maximum
         * gain for this objective (strict lex when max>0, least-harm when
         * max<=0).  Lower-priority levels then break ties among survivors. */
        for (idx_t pi = nobj - 1; pi >= 0 && n_valid > 1; pi--) {
          idx_t pobj = obj_order[pi];
          real_t id_pobj = (real_t)(all_ckrinfo + pobj * nvtxs + i)->id;

          real_t max_gain = -1e30;
          for (idx_t vi = 0; vi < n_valid; vi++) {
            real_t gain = part_obj_ed[pobj * nparts + valid_pids[vi]] - id_pobj;
            if (gain > max_gain) max_gain = gain;
          }

          /* Always narrow to targets achieving max_gain for this objective.
           * When max_gain > 0: strict lex (maximise gain).
           * When max_gain <= 0: minimise harm (least-negative = max_gain). */
          real_t threshold = max_gain;
          idx_t n_new = 0;
          for (idx_t vi = 0; vi < n_valid; vi++) {
            real_t gain = part_obj_ed[pobj * nparts + valid_pids[vi]] - id_pobj;
            if (gain >= threshold) valid_pids[n_new++] = valid_pids[vi];
          }
          n_valid = n_new; /* always >= 1: at least one element achieves max_gain */
        }
        best_to = (n_valid > 0) ? valid_pids[0] : -1;
      }

      if (best_to < 0) {
        skipped[nskipped++] = i;
        continue;
      }

      to = best_to;
      nmoved++;
      where[i] = to;

      /* Update partition weights for ALL constraints */
      for (c = 0; c < ncon; c++) {
        idx_t vwgt = graph->vwgt[i * ncon + c];
        pwgts[to   * ncon + c] += vwgt;
        pwgts[from * ncon + c] -= vwgt;
      }

      /* Update ALL relevant objectives' ckrinfo for vertex i and its neighbors */
      for (idx_t oj = 0; oj < nobj; oj++) {
        idx_t oj_ca = pair_a[oj];
        idx_t oj_cb = pair_b[oj];

        if (mc >= 0 && mc != oj_ca && mc != oj_cb)
          continue;

        graph->ckrinfo = all_ckrinfo + oj * nvtxs;
        graph->bndptr  = all_bndptr  + oj * nvtxs;
        graph->bndind  = all_bndind  + oj * nvtxs;
        nbnd           = all_nbnd[oj];
        myrinfo        = graph->ckrinfo + i;
        mynbrs         = ctrl->cnbrpool + myrinfo->inbr;
        bndptr         = graph->bndptr;
        bndind         = graph->bndind;

        /* Ensure 'to' is in this objective's neighbor list */
        idx_t kc;
        for (kc = 0; kc < myrinfo->nnbrs; kc++)
          if (mynbrs[kc].pid == to) break;

        if (kc == myrinfo->nnbrs) {
          if (myrinfo->inbr == -1) {
            myrinfo->inbr  = cnbrpoolGetNext(ctrl, xadj[i + 1] - xadj[i]);
            myrinfo->nnbrs = 0;
            mynbrs         = ctrl->cnbrpool + myrinfo->inbr;
          }
          mynbrs[kc].pid = to;
          mynbrs[kc].ed  = 0;
          myrinfo->nnbrs++;
        }

        UpdateMovedVertexInfoAndBND(i, from, kc, to, myrinfo, mynbrs, where,
                                    nbnd, bndptr, bndind, bndtype);
        all_nbnd[oj] = nbnd;

        /* Update neighbors relevant to this objective */
        for (j = xadj[i]; j < xadj[i + 1]; j++) {
          ii = adjncy[j];

          /* Neighbor must carry the complementary constraint */
          idx_t needed_con;
          if (oj_ca == oj_cb)
            needed_con = oj_ca;
          else
            needed_con = (mc == oj_ca) ? oj_cb : oj_ca;
          if (mc >= 0 && vtx_con[ii] != needed_con)
            continue;

          idx_t ewgt    = adjwgt[j];
          idx_t me_ii   = where[ii];
          ckrinfo_t *ri_ii = graph->ckrinfo + ii;
          oldnnbrs      = ri_ii->nnbrs;

          UpdateAdjacentVertexInfoAndBND(ctrl, ii, xadj[ii + 1] - xadj[ii],
                                         me_ii, from, to, ri_ii, ewgt,
                                         nbnd, bndptr, bndind, bndtype);
          all_nbnd[oj] = nbnd;

          /* Recompute combined gain and update queue for affected neighbor */
          if (vstatus[ii] != VPQSTATUS_EXTRACTED) {
            int ii_in_bnd = 0;
            for (idx_t oj2 = 0; oj2 < nobj && !ii_in_bnd; oj2++)
              ii_in_bnd = (all_ckrinfo[oj2 * nvtxs + ii].ed > 0);

            real_t new_gain;
            MOBJ_CGAIN(ii, new_gain);

            if (ii_in_bnd) {
              if (vstatus[ii] == VPQSTATUS_PRESENT)
                rpqUpdate(queue, ii, new_gain);
              else {
                rpqInsert(queue, ii, new_gain);
                vstatus[ii] = VPQSTATUS_PRESENT;
                ListInsert(nupd, updind, updptr, ii);
              }
            } else if (vstatus[ii] == VPQSTATUS_PRESENT) {
              rpqDelete(queue, ii);
              vstatus[ii] = VPQSTATUS_NOTPRESENT;
            }
          }
        }
      }

      /* Re-insert skipped nodes */
      if (nskipped > 0) {
        for (k = 0; k < nskipped; k++) {
          idx_t u = skipped[k];
          if (vstatus[u] != VPQSTATUS_PRESENT) {
            int u_in_bnd = 0;
            for (idx_t oj = 0; oj < nobj && !u_in_bnd; oj++)
              u_in_bnd = (all_ckrinfo[oj * nvtxs + u].ed > 0);
            if (u_in_bnd) {
              MOBJ_CGAIN(u, rgain);
              rpqInsert(queue, u, rgain);
              vstatus[u] = VPQSTATUS_PRESENT;
              if (updptr[u] == -1)
                ListInsert(nupd, updind, updptr, u);
            }
          }
        }
        nskipped = 0;
      }
    } /* end FM loop */

    /* Reset vstatus */
    for (i = 0; i < nupd; i++) {
      vstatus[updind[i]] = VPQSTATUS_NOTPRESENT;
      updptr[updind[i]] = -1;
    }
  } /* end pass loop */

#undef MOBJ_CGAIN

  /* Restore original pointers */
  graph->ckrinfo = orig_ckrinfo;
  graph->bndptr = orig_bndptr;
  graph->bndind = orig_bndind;
  graph->nbnd = orig_nbnd;

  rpqDestroy(queue);
  WCOREPOP;
}
