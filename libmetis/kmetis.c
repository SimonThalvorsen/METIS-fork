/*!
\file
\brief The top-level routines for  multilevel k-way partitioning that minimizes
       the edge cut.

\date   Started 7/28/1997
\author George
\author Copyright 1997-2011, Regents of the University of Minnesota
\version\verbatim $Id: kmetis.c 20398 2016-11-22 17:17:12Z karypis $
\endverbatim
*/

#include "metislib.h"

/*************************************************************************/
/*! This function is the entry point for MCKMETIS */
/*************************************************************************/
int METIS_PartGraphKway(idx_t *nvtxs, idx_t *ncon, idx_t *xadj, idx_t *adjncy,
                        idx_t *vwgt, idx_t *vsize, idx_t *adjwgt, idx_t *nparts,
                        real_t *tpwgts, real_t *ubvec, idx_t *options,
                        idx_t *objval, idx_t *part) {

  int sigrval = 0, renumber = 0;
  graph_t *graph;
  ctrl_t *ctrl;

  /* set up malloc cleaning code and signal catchers */
  if (!gk_malloc_init())
    return METIS_ERROR_MEMORY;

  gk_sigtrap();

  if ((sigrval = gk_sigcatch()) != 0)
    goto SIGTHROW;

  ctrl = SetupCtrl(METIS_OP_KMETIS, options, *ncon, *nparts, tpwgts, ubvec);
  if (!ctrl) {
    //  fhere mess up check input
    gk_siguntrap();
    return METIS_ERROR_INPUT;
  }

  /* if required, change the numbering to 0 */
  if (ctrl->numflag == 1) {
    Change2CNumbering(*nvtxs, xadj, adjncy);
    renumber = 1;
  }

  /* set up the graph */
  graph = SetupGraph(ctrl, *nvtxs, *ncon, xadj, adjncy, vwgt, vsize, adjwgt);
  /* set up multipliers for making balance computations easier */
  SetupKWayBalMultipliers(ctrl, graph);

  ctrl->CoarsenTo = gk_max((*nvtxs) / (40 * gk_log2(*nparts)), 30 * (*nparts));
  ctrl->nIparts =
      (ctrl->nIparts != -1 ? ctrl->nIparts
                           : (ctrl->CoarsenTo == 30 * (*nparts) ? 4 : 5));

  /* take care contiguity requests for disconnected graphs */
  if (ctrl->contig && !IsConnected(graph, 0))
    gk_errexit(SIGERR, "METIS Error: A contiguous partition is requested for a "
                       "non-contiguous input graph.\n");

  /* allocate workspace memory */
  AllocateWorkSpace(ctrl, graph);

  /* start the partitioning */
  IFSET(ctrl->dbglvl, METIS_DBG_TIME, InitTimers(ctrl));
  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->TotalTmr));

  iset(*nvtxs, 0, part);
  if (ctrl->dbglvl & 512)
    *objval = (*nparts == 1 ? 0 : BlockKWayPartitioning(ctrl, graph, part));
  else
    *objval = (*nparts == 1 ? 0 : MlevelKWayPartitioning(ctrl, graph, part));

  IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->TotalTmr));
  IFSET(ctrl->dbglvl, METIS_DBG_TIME, PrintTimers(ctrl));

  /* clean up */
  FreeCtrl(&ctrl);

SIGTHROW:
  /* if required, change the numbering back to 1 */
  if (renumber)
    Change2FNumbering(*nvtxs, xadj, adjncy, part);

  gk_siguntrap();
  gk_malloc_cleanup(0);

  return metis_rcode(sigrval);
}

/*************************************************************************/
/*! This function computes a k-way partitioning of a graph that minimizes
    the specified objective function.

    \param ctrl is the control structure
    \param graph is the graph to be partitioned
    \param part is the vector that on return will store the partitioning

    \returns the objective value of the partitioning. The partitioning
             itself is stored in the part vector.
*/
/*************************************************************************/
idx_t MlevelKWayPartitioning(ctrl_t *ctrl, graph_t *graph, idx_t *part) {
  idx_t i, j, objval = 0, curobj = 0, bestobj = 0;
  real_t curbal = 0.0, bestbal = 0.0;
  graph_t *cgraph;
  int status;

  for (i = 0; i < ctrl->ncuts; i++) {
    cgraph = CoarsenGraph(ctrl, graph);

    IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_startcputimer(ctrl->InitPartTmr));
    AllocateKWayPartitionMemory(ctrl, cgraph);

    /* Release the work space */
    FreeWorkSpace(ctrl);

    /* Compute the initial partitioning */
    InitKWayPartitioning(ctrl, cgraph);

    /* Re-allocate the work space */
    AllocateWorkSpace(ctrl, graph);

    /* MOBJ uses nobj separate ckrinfo arrays sharing one cnbrpool,
       so scale the pool size by the number of pair-objectives. */
    {
      idx_t pool_scale = 1;
      if (ctrl->objtype == METIS_OBJTYPE_MOBJ) {
        idx_t nobj = graph->ncon * (graph->ncon + 1) / 2;
        pool_scale = nobj;
      }
      AllocateRefinementWorkSpace(ctrl, pool_scale * graph->nedges,
                                  pool_scale * 2 * cgraph->nedges);
    }

    IFSET(ctrl->dbglvl, METIS_DBG_TIME, gk_stopcputimer(ctrl->InitPartTmr));
    IFSET(ctrl->dbglvl, METIS_DBG_IPART,
          printf("Initial %" PRIDX "-way partitioning cut: %" PRIDX "\n",
                 ctrl->nparts, objval));

    RefineKWay(ctrl, graph, cgraph);

    switch (ctrl->objtype) {
    case METIS_OBJTYPE_CUT:
      curobj = graph->mincut;
      break;

    case METIS_OBJTYPE_VOL:
      curobj = graph->minvol;
      break;

    case METIS_OBJTYPE_MOBJ:
      break;

    default:
      gk_errexit(SIGERR, "Unknown2 objtype: %d\n", ctrl->objtype);
    }

    curbal = ComputeLoadImbalanceDiff(graph, ctrl->nparts, ctrl->pijbm,
                                      ctrl->ubfactors);

    if (i == 0 || (curbal <= 0.0005 && bestobj > curobj) ||
        (bestbal > 0.0005 && curbal < bestbal)) {
      icopy(graph->nvtxs, graph->where, part);
      bestobj = curobj;
      bestbal = curbal;
    }

    FreeRData(graph);

    if (bestobj == 0)
      break;
  }

  FreeGraph(&graph);

  return bestobj;
}

/*! Boost cross-physics edge weights for priority-aware initial partitioning.
 *  Returns the original adjwgt pointer; caller must restore graph->adjwgt
 *  and free the modified array after partitioning. */
static idx_t *mobj_prio_apply_reweight(ctrl_t *ctrl, graph_t *graph) {
  idx_t ncon = graph->ncon;
  idx_t nobj = ncon * (ncon + 1) / 2;
  idx_t nedges = graph->xadj[graph->nvtxs];
  idx_t *pair_a = imalloc(nobj, "reweight: pair_a");
  idx_t *pair_b = imalloc(nobj, "reweight: pair_b");
  idx_t *obj_order = imalloc(nobj, "reweight: obj_order");
  idx_t *adjwgt_mod = imalloc(nedges, "reweight: adjwgt_mod");
  idx_t *adjwgt_orig = graph->adjwgt;

  {
    idx_t obj = 0;
    for (idx_t a = 0; a < ncon; a++)
      for (idx_t b = a; b < ncon; b++) {
        pair_a[obj] = a;
        pair_b[obj] = b;
        obj++;
      }
  }
  {
    idx_t *used = ismalloc(nobj, 0, "reweight: used");
    idx_t n = 0;
    idx_t pv = ctrl->mobj_prio;
    while (pv > 0 && n < nobj) {
      idx_t oid = pv & 0xF;
      pv >>= 4;
      if (oid < nobj && !used[oid]) {
        obj_order[n++] = oid;
        used[oid] = 1;
      }
    }
    for (idx_t x = 0; x < nobj; x++)
      if (!used[x])
        obj_order[n++] = x;
    gk_free((void **)&used, LTERM);
  }

  icopy(nedges, adjwgt_orig, adjwgt_mod);
  for (idx_t u = 0; u < graph->nvtxs; u++) {
    for (idx_t j = graph->xadj[u]; j < graph->xadj[u + 1]; j++) {
      idx_t v = graph->adjncy[j];
      idx_t best = 1;
      for (idx_t oi = 0; oi < nobj; oi++) {
        idx_t oid = obj_order[oi];
        idx_t ca = pair_a[oid], cb = pair_b[oid];
        int ua = (graph->vwgt[u * ncon + ca] > 0);
        int ub = (graph->vwgt[u * ncon + cb] > 0);
        int va = (graph->vwgt[v * ncon + ca] > 0);
        int vb = (graph->vwgt[v * ncon + cb] > 0);
        if ((ua && vb) || (ub && va) || (ca == cb && ua && va)) {
          idx_t boost = nobj - oi;
          if (boost > best)
            best = boost;
        }
      }
      adjwgt_mod[j] *= best;
    }
  }
  gk_free((void **)&pair_a, &pair_b, &obj_order, LTERM);
  graph->adjwgt = adjwgt_mod;
  return adjwgt_orig;
}

/*************************************************************************/
/*! This function computes the initial k-way partitioning using PMETIS
 */
/*************************************************************************/
void InitKWayPartitioning(ctrl_t *ctrl, graph_t *graph) {
  idx_t i, ntrials, options[METIS_NOPTIONS], curobj = 0, bestobj = 0;
  idx_t *bestwhere = NULL;
  real_t *ubvec = NULL;
  int status;

  METIS_SetDefaultOptions(options);
  // options[METIS_OPTION_NITER]     = 10;
  options[METIS_OPTION_NITER] = ctrl->niter;
  options[METIS_OPTION_OBJTYPE] = METIS_OBJTYPE_CUT;
  options[METIS_OPTION_NO2HOP] = ctrl->no2hop;
  options[METIS_OPTION_ONDISK] = ctrl->ondisk;
  options[METIS_OPTION_DROPEDGES] = ctrl->dropedges;
  // options[METIS_OPTION_DBGLVL]    = ctrl->dbglvl;

  ubvec = rmalloc(graph->ncon, "InitKWayPartitioning: ubvec");
  for (i = 0; i < graph->ncon; i++)
    ubvec[i] = (real_t)pow(ctrl->ubfactors[i], 1.0 / log(ctrl->nparts));

  switch (ctrl->objtype) {
  case METIS_OBJTYPE_CUT:
  case METIS_OBJTYPE_VOL:
    options[METIS_OPTION_NCUTS] = ctrl->nIparts;
    {
      idx_t *saved_adjwgt = NULL;
      if (ctrl->mobj_ipart == METIS_MOBJ_IPART_REWEIGHT && ctrl->mobj_prio != 0)
        saved_adjwgt = mobj_prio_apply_reweight(ctrl, graph);

      status = METIS_PartGraphRecursive(
          &graph->nvtxs, &graph->ncon, graph->xadj, graph->adjncy, graph->vwgt,
          graph->vsize, graph->adjwgt, &ctrl->nparts, ctrl->tpwgts, ubvec,
          options, &curobj, graph->where);

      if (saved_adjwgt) {
        gk_free((void **)&graph->adjwgt, LTERM);
        graph->adjwgt = saved_adjwgt;
      }
      if (status != METIS_OK)
        gk_errexit(SIGERR, "Failed during initial partitioning\n");
    }
    break;

  case METIS_OBJTYPE_MOBJ:
    options[METIS_OPTION_NCUTS] = ctrl->nIparts;

    if (ctrl->mobj_ipart == METIS_MOBJ_IPART_REWEIGHT && ctrl->mobj_prio != 0) {
      /* --- Edge Reweighting approach --- */
      idx_t ncon_r = graph->ncon;
      idx_t nobj_r = ncon_r * (ncon_r + 1) / 2;
      idx_t nedges_r = graph->xadj[graph->nvtxs];
      idx_t *pair_a_r = imalloc(nobj_r, "InitKWay: pair_a_r");
      idx_t *pair_b_r = imalloc(nobj_r, "InitKWay: pair_b_r");
      idx_t *obj_order_r = imalloc(nobj_r, "InitKWay: obj_order_r");
      idx_t *adjwgt_mod = imalloc(nedges_r, "InitKWay: adjwgt_mod");
      idx_t *adjwgt_orig = graph->adjwgt;

      /* Compute interaction pairs */
      {
        idx_t obj = 0;
        for (idx_t a = 0; a < ncon_r; a++)
          for (idx_t b = a; b < ncon_r; b++) {
            pair_a_r[obj] = a;
            pair_b_r[obj] = b;
            obj++;
          }
      }

      /* Compute priority order from mobj_prio */
      {
        idx_t *used = ismalloc(nobj_r, 0, "InitKWay: used");
        idx_t n_ordered = 0;
        idx_t prio_val = ctrl->mobj_prio;
        while (prio_val > 0 && n_ordered < nobj_r) {
          idx_t oid = prio_val & 0xF;
          prio_val >>= 4;
          if (oid < nobj_r && !used[oid]) {
            obj_order_r[n_ordered++] = oid;
            used[oid] = 1;
          }
        }
        for (idx_t x = 0; x < nobj_r; x++)
          if (!used[x])
            obj_order_r[n_ordered++] = x;
        gk_free((void **)&used, LTERM);
      }

      /* Copy original weights */
      icopy(nedges_r, adjwgt_orig, adjwgt_mod);

      /* Boost edge weights based on priority */
      for (idx_t u = 0; u < graph->nvtxs; u++) {
        for (idx_t j = graph->xadj[u]; j < graph->xadj[u + 1]; j++) {
          idx_t v = graph->adjncy[j];
          idx_t best_boost = 1;
          for (idx_t oi = 0; oi < nobj_r; oi++) {
            idx_t obj_id = obj_order_r[oi];
            idx_t ca = pair_a_r[obj_id];
            idx_t cb = pair_b_r[obj_id];
            /* Check if edge is relevant: both endpoints have nonzero vwgt for
             * the pair's constraints */
            int u_has_a = (graph->vwgt[u * ncon_r + ca] > 0);
            int u_has_b = (graph->vwgt[u * ncon_r + cb] > 0);
            int v_has_a = (graph->vwgt[v * ncon_r + ca] > 0);
            int v_has_b = (graph->vwgt[v * ncon_r + cb] > 0);
            if ((u_has_a && v_has_b) || (u_has_b && v_has_a) ||
                (ca == cb && u_has_a && v_has_a)) {
              idx_t boost = nobj_r - oi;
              if (boost > best_boost)
                best_boost = boost;
            }
          }
          adjwgt_mod[j] *= best_boost;
        }
      }

      /* Swap in modified weights */
      graph->adjwgt = adjwgt_mod;

      status = METIS_PartGraphRecursive(
          &graph->nvtxs, &graph->ncon, graph->xadj, graph->adjncy, graph->vwgt,
          graph->vsize, graph->adjwgt, &ctrl->nparts, ctrl->tpwgts, ubvec,
          options, &curobj, graph->where);

      /* Restore original weights */
      graph->adjwgt = adjwgt_orig;
      gk_free((void **)&adjwgt_mod, &pair_a_r, &pair_b_r, &obj_order_r, LTERM);

      if (status != METIS_OK)
        gk_errexit(SIGERR,
                   "Failed during initial partitioning (mobj reweight)\n");

    } else if (ctrl->mobj_ipart == METIS_MOBJ_IPART_CONORDER &&
               ctrl->mobj_prio != 0) {
      /* --- Constraint Reordering approach --- */
      idx_t ncon_c = graph->ncon;
      idx_t nobj_c = ncon_c * (ncon_c + 1) / 2;
      idx_t nvtxs_c = graph->nvtxs;
      idx_t *pair_a_c = imalloc(nobj_c, "InitKWay: pair_a_c");
      idx_t *pair_b_c = imalloc(nobj_c, "InitKWay: pair_b_c");
      idx_t *obj_order_c = imalloc(nobj_c, "InitKWay: obj_order_c");

      /* Compute interaction pairs */
      {
        idx_t obj = 0;
        for (idx_t a = 0; a < ncon_c; a++)
          for (idx_t b = a; b < ncon_c; b++) {
            pair_a_c[obj] = a;
            pair_b_c[obj] = b;
            obj++;
          }
      }

      /* Compute priority order from mobj_prio */
      {
        idx_t *used = ismalloc(nobj_c, 0, "InitKWay: used_c");
        idx_t n_ordered = 0;
        idx_t prio_val = ctrl->mobj_prio;
        while (prio_val > 0 && n_ordered < nobj_c) {
          idx_t oid = prio_val & 0xF;
          prio_val >>= 4;
          if (oid < nobj_c && !used[oid]) {
            obj_order_c[n_ordered++] = oid;
            used[oid] = 1;
          }
        }
        for (idx_t x = 0; x < nobj_c; x++)
          if (!used[x])
            obj_order_c[n_ordered++] = x;
        gk_free((void **)&used, LTERM);
      }

      /* Derive per-constraint priority scores */
      idx_t *con_scores = ismalloc(ncon_c, 0, "InitKWay: con_scores");
      for (idx_t oi = 0; oi < nobj_c; oi++) {
        idx_t obj_id = obj_order_c[oi];
        idx_t score = nobj_c - oi;
        con_scores[pair_a_c[obj_id]] += score;
        con_scores[pair_b_c[obj_id]] += score;
      }

      /* Build sorted constraint order (descending score) — simple selection
       * sort */
      idx_t *con_order = imalloc(ncon_c, "InitKWay: con_order");
      {
        idx_t *scores_tmp = imalloc(ncon_c, "InitKWay: scores_tmp");
        icopy(ncon_c, con_scores, scores_tmp);
        for (idx_t ci = 0; ci < ncon_c; ci++) {
          idx_t best = -1, best_idx = 0;
          for (idx_t cj = 0; cj < ncon_c; cj++) {
            if (scores_tmp[cj] > best) {
              best = scores_tmp[cj];
              best_idx = cj;
            }
          }
          con_order[ci] = best_idx;
          scores_tmp[best_idx] = -1;
        }
        gk_free((void **)&scores_tmp, LTERM);
      }

      /* Compute priority-weighted ubvec: tighten balance for high-priority
         constraints, relax for low-priority ones.
         Scale linearly: highest-scored constraint gets ubvec * tighten_factor,
         lowest-scored gets ubvec * relax_factor. */
      real_t *ubvec_prio = rmalloc(ncon_c, "InitKWay: ubvec_prio");
      {
        idx_t max_score = 0, min_score = IDX_MAX;
        for (idx_t ci = 0; ci < ncon_c; ci++) {
          if (con_scores[ci] > max_score)
            max_score = con_scores[ci];
          if (con_scores[ci] < min_score)
            min_score = con_scores[ci];
        }

        for (idx_t ci = 0; ci < ncon_c; ci++) {
          /* Map score to [0,1] range: 1 = highest priority, 0 = lowest */
          real_t t = (max_score > min_score)
                         ? (real_t)(con_scores[ci] - min_score) /
                               (max_score - min_score)
                         : 0.5;
          /* Tighten high-priority (t=1): multiply ubvec by 0.5
             Relax low-priority (t=0): multiply ubvec by 1.5
             Linear interpolation: factor = 1.5 - 1.0*t */
          real_t factor = 1.5 - 1.0 * t;
          /* ubvec values are (1 + imbalance_fraction), e.g. 1.03.
             Scale only the imbalance part: new = 1 + (old-1)*factor */
          ubvec_prio[ci] = 1.0 + (ubvec[ci] - 1.0) * factor;
          /* Clamp: must be > 1.0 */
          if (ubvec_prio[ci] <= 1.0)
            ubvec_prio[ci] = 1.001;
        }
      }

      status = METIS_PartGraphRecursive(
          &graph->nvtxs, &graph->ncon, graph->xadj, graph->adjncy, graph->vwgt,
          graph->vsize, graph->adjwgt, &ctrl->nparts, ctrl->tpwgts, ubvec_prio,
          options, &curobj, graph->where);

      gk_free((void **)&ubvec_prio, &con_order, &con_scores, &pair_a_c,
              &pair_b_c, &obj_order_c, LTERM);

      if (status != METIS_OK)
        gk_errexit(SIGERR,
                   "Failed during initial partitioning (mobj conorder)\n");

    } else {
      /* Default MOBJ initial partitioning (standard CUT) */
      status = METIS_PartGraphRecursive(
          &graph->nvtxs, &graph->ncon, graph->xadj, graph->adjncy, graph->vwgt,
          graph->vsize, graph->adjwgt, &ctrl->nparts, ctrl->tpwgts, ubvec,
          options, &curobj, graph->where);

      if (status != METIS_OK)
        gk_errexit(SIGERR, "Failed during initial partitioning\n");
    }
    break;

#ifdef XXX /* This does not seem to help */
  case METIS_OBJTYPE_VOL:
    bestwhere = imalloc(graph->nvtxs, "InitKWayPartitioning: bestwhere");
    options[METIS_OPTION_NCUTS] = 2;

    ntrials = (ctrl->nIparts + 1) / 2;
    for (i = 0; i < ntrials; i++) {
      status = METIS_PartGraphRecursive(
          &graph->nvtxs, &graph->ncon, graph->xadj, graph->adjncy, graph->vwgt,
          graph->vsize, graph->adjwgt, &ctrl->nparts, ctrl->tpwgts, ubvec,
          options, &curobj, graph->where);
      if (status != METIS_OK)
        gk_errexit(SIGERR, "Failed during initial partitioning\n");

      curobj = ComputeVolume(graph, graph->where);

      if (i == 0 || bestobj > curobj) {
        bestobj = curobj;
        if (i < ntrials - 1)
          icopy(graph->nvtxs, graph->where, bestwhere);
      }

      if (bestobj == 0)
        break;
    }
    if (bestobj != curobj)
      icopy(graph->nvtxs, bestwhere, graph->where);

    break;
#endif

  default:
    gk_errexit(SIGERR, "Unknown1 objtype: %d\n", ctrl->objtype);
  }

  gk_free((void **)&ubvec, &bestwhere, LTERM);
}

/*************************************************************************/
/*! This function computes a k-way partitioning of a graph that minimizes
    the specified objective function.

    \param ctrl is the control structure
    \param graph is the graph to be partitioned
    \param part is the vector that on return will store the partitioning

    \returns the objective value of the partitioning. The partitioning
             itself is stored in the part vector.
*/
/*************************************************************************/
idx_t BlockKWayPartitioning(ctrl_t *ctrl, graph_t *graph, idx_t *part) {
  idx_t i, ii, j, nvtxs, objval = 0;
  idx_t *vwgt;
  idx_t nparts, mynparts;
  idx_t *fpwgts, *cpwgts, *fpart, *perm;
  ipq_t *queue;

  WCOREPUSH;

  nvtxs = graph->nvtxs;
  vwgt = graph->vwgt;

  nparts = ctrl->nparts;

  mynparts = gk_min(100 * nparts, sqrt(nvtxs));

  for (i = 0; i < nvtxs; i++)
    part[i] = i % nparts;
  irandArrayPermute(nvtxs, part, 4 * nvtxs, 0);

  /* create the initial multi-section */
  mynparts = GrowMultisection(ctrl, graph, mynparts, part);

  /* balance using label-propagation and refine using a randomized greedy
   * strategy */
  BalanceAndRefineLP(ctrl, graph, mynparts, part);

  /* determine the size of the fine partitions */
  fpwgts = iset(mynparts, 0, iwspacemalloc(ctrl, mynparts));
  for (i = 0; i < nvtxs; i++)
    fpwgts[part[i]] += vwgt[i];

  /* create and initialize the queue that will determine
     where to put the next one */
  cpwgts = iset(nparts, 0, iwspacemalloc(ctrl, nparts));
  queue = ipqCreate(nparts);
  for (i = 0; i < nparts; i++)
    ipqInsert(queue, i, 0);

  /* assign the fine partitions into the coarse partitions */
  fpart = iwspacemalloc(ctrl, mynparts);
  perm = iwspacemalloc(ctrl, mynparts);
  irandArrayPermute(mynparts, perm, mynparts, 1);
  for (ii = 0; ii < mynparts; ii++) {
    i = perm[ii];
    j = ipqSeeTopVal(queue);
    fpart[i] = j;
    cpwgts[j] += fpwgts[i];
    ipqUpdate(queue, j, -cpwgts[j]);
  }
  ipqDestroy(queue);

  for (i = 0; i < nvtxs; i++)
    part[i] = fpart[part[i]];

  WCOREPOP;

  return ComputeCut(graph, part);
}

/*************************************************************************/
/*! This function takes a graph and produces a bisection by using a region
    growing algorithm. The resulting bisection is refined using FM.
    The resulting partition is returned in graph->where.
*/
/*************************************************************************/
idx_t GrowMultisection(ctrl_t *ctrl, graph_t *graph, idx_t nparts,
                       idx_t *where) {
  idx_t i, j, k, l, nvtxs, nleft, first, last;
  idx_t *xadj, *vwgt, *adjncy;
  idx_t *queue;
  idx_t tvwgt, maxpwgt, *pwgts;

  WCOREPUSH;

  nvtxs = graph->nvtxs;
  xadj = graph->xadj;
  vwgt = graph->xadj;
  adjncy = graph->adjncy;

  queue = iwspacemalloc(ctrl, nvtxs);

  /* Select the seeds for the nparts-way BFS */
  for (nleft = 0, i = 0; i < nvtxs; i++) {
    if (xadj[i + 1] - xadj[i] > 1) /* a seed's degree should be > 1 */
      where[nleft++] = i;
  }
  nparts = gk_min(nparts, nleft);
  for (i = 0; i < nparts; i++) {
    j = irandInRange(nleft);
    queue[i] = where[j];
    where[j] = --nleft;
  }

  pwgts = iset(nparts, 0, iwspacemalloc(ctrl, nparts));
  tvwgt = isum(nvtxs, vwgt, 1);
  maxpwgt = (1.5 * tvwgt) / nparts;

  iset(nvtxs, -1, where);
  for (i = 0; i < nparts; i++) {
    where[queue[i]] = i;
    pwgts[i] = vwgt[queue[i]];
  }

  first = 0;
  last = nparts;
  nleft = nvtxs - nparts;

  /* Start the BFS from queue to get a partition */
  while (first < last) {
    i = queue[first++];
    l = where[i];
    if (pwgts[l] > maxpwgt)
      continue;

    for (j = xadj[i]; j < xadj[i + 1]; j++) {
      k = adjncy[j];
      if (where[k] == -1) {
        if (pwgts[l] + vwgt[k] > maxpwgt)
          break;
        pwgts[l] += vwgt[k];
        where[k] = l;
        queue[last++] = k;
        nleft--;
      }
    }
  }

  /* Assign the unassigned vertices randomly to the nparts partitions */
  if (nleft > 0) {
    for (i = 0; i < nvtxs; i++) {
      if (where[i] == -1)
        where[i] = irandInRange(nparts);
    }
  }

  WCOREPOP;

  return nparts;
}

/*************************************************************************/
/*! This function balances the partitioning using label propagation.
 */
/*************************************************************************/
void BalanceAndRefineLP(ctrl_t *ctrl, graph_t *graph, idx_t nparts,
                        idx_t *where) {
  idx_t ii, i, j, k, u, v, nvtxs, iter;
  idx_t *xadj, *vwgt, *adjncy, *adjwgt;
  idx_t tvwgt, *pwgts, maxpwgt, minpwgt;
  idx_t *perm;
  idx_t from, to, nmoves, nnbrs, *nbrids, *nbrwgts, *nbrmrks;
  real_t ubfactor;

  WCOREPUSH;

  nvtxs = graph->nvtxs;
  xadj = graph->xadj;
  vwgt = graph->vwgt;
  adjncy = graph->adjncy;
  adjwgt = graph->adjwgt;

  pwgts = iset(nparts, 0, iwspacemalloc(ctrl, nparts));

  ubfactor = I2RUBFACTOR(ctrl->ufactor);
  tvwgt = isum(nvtxs, vwgt, 1);
  maxpwgt = (ubfactor * tvwgt) / nparts;
  minpwgt = (1.0 * tvwgt) / (ubfactor * nparts);

  for (i = 0; i < nvtxs; i++)
    pwgts[where[i]] += vwgt[i];

  /* for randomly visiting the vertices */
  perm = iincset(nvtxs, 0, iwspacemalloc(ctrl, nvtxs));

  /* for keeping track of adjacent partitions */
  nbrids = iwspacemalloc(ctrl, nparts);
  nbrwgts = iset(nparts, 0, iwspacemalloc(ctrl, nparts));
  nbrmrks = iset(nparts, -1, iwspacemalloc(ctrl, nparts));

  /* perform a fixed number of balancing LP iterations */
  if (ctrl->dbglvl & METIS_DBG_REFINE)
    printf("BLP: nparts: %" PRIDX ", min-max: [%" PRIDX ", %" PRIDX
           "], bal: %7.4" PRREAL ", cut: %9" PRIDX "\n",
           nparts, minpwgt, maxpwgt,
           1.0 * imax(nparts, pwgts, 1) * nparts / tvwgt,
           ComputeCut(graph, where));
  for (iter = 0; iter < ctrl->niter; iter++) {
    if (imax(nparts, pwgts, 1) * nparts < ubfactor * tvwgt)
      break;

    irandArrayPermute(nvtxs, perm, nvtxs / 8, 1);
    nmoves = 0;

    for (ii = 0; ii < nvtxs; ii++) {
      u = perm[ii];

      from = where[u];
      if (pwgts[from] - vwgt[u] < minpwgt)
        continue;

      nnbrs = 0;
      for (j = xadj[u]; j < xadj[u + 1]; j++) {
        v = adjncy[j];
        to = where[v];

        if (pwgts[to] + vwgt[u] > maxpwgt)
          continue; /* skip if 'to' is overweight */

        if ((k = nbrmrks[to]) == -1) {
          nbrmrks[to] = k = nnbrs++;
          nbrids[k] = to;
        }
        nbrwgts[k] += xadj[v + 1] - xadj[v];
      }
      if (nnbrs == 0)
        continue;

      to = nbrids[iargmax(nnbrs, nbrwgts, 1)];
      if (from != to) {
        where[u] = to;
        INC_DEC(pwgts[to], pwgts[from], vwgt[u]);
        nmoves++;
      }

      for (k = 0; k < nnbrs; k++) {
        nbrmrks[nbrids[k]] = -1;
        nbrwgts[k] = 0;
      }
    }

    if (ctrl->dbglvl & METIS_DBG_REFINE)
      printf("     nmoves: %8" PRIDX ", bal: %7.4" PRREAL ", cut: %9" PRIDX
             "\n",
             nmoves, 1.0 * imax(nparts, pwgts, 1) * nparts / tvwgt,
             ComputeCut(graph, where));

    if (nmoves == 0)
      break;
  }

  /* perform a fixed number of refinement LP iterations */
  if (ctrl->dbglvl & METIS_DBG_REFINE)
    printf("RLP: nparts: %" PRIDX ", min-max: [%" PRIDX ", %" PRIDX
           "], bal: %7.4" PRREAL ", cut: %9" PRIDX "\n",
           nparts, minpwgt, maxpwgt,
           1.0 * imax(nparts, pwgts, 1) * nparts / tvwgt,
           ComputeCut(graph, where));
  for (iter = 0; iter < ctrl->niter; iter++) {
    irandArrayPermute(nvtxs, perm, nvtxs / 8, 1);
    nmoves = 0;

    for (ii = 0; ii < nvtxs; ii++) {
      u = perm[ii];

      from = where[u];
      if (pwgts[from] - vwgt[u] < minpwgt)
        continue;

      nnbrs = 0;
      for (j = xadj[u]; j < xadj[u + 1]; j++) {
        v = adjncy[j];
        to = where[v];

        if (to != from && pwgts[to] + vwgt[u] > maxpwgt)
          continue; /* skip if 'to' is overweight */

        if ((k = nbrmrks[to]) == -1) {
          nbrmrks[to] = k = nnbrs++;
          nbrids[k] = to;
        }
        nbrwgts[k] += adjwgt[j];
      }
      if (nnbrs == 0)
        continue;

      to = nbrids[iargmax(nnbrs, nbrwgts, 1)];
      if (from != to) {
        where[u] = to;
        INC_DEC(pwgts[to], pwgts[from], vwgt[u]);
        nmoves++;
      }

      for (k = 0; k < nnbrs; k++) {
        nbrmrks[nbrids[k]] = -1;
        nbrwgts[k] = 0;
      }
    }

    if (ctrl->dbglvl & METIS_DBG_REFINE)
      printf("     nmoves: %8" PRIDX ", bal: %7.4" PRREAL ", cut: %9" PRIDX
             "\n",
             nmoves, 1.0 * imax(nparts, pwgts, 1) * nparts / tvwgt,
             ComputeCut(graph, where));

    if (nmoves == 0)
      break;
  }

  WCOREPOP;
}
