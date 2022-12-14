theory ProcLemma
  imports ProcSendCase
begin

    (* ##### 3. process reduction validity for thread case ##### *)

definition dsub_env :: "'a state_env \<Rightarrow> 'b state_env \<Rightarrow> bool" where
  "dsub_env s env = (\<forall> x. env x \<noteq> None \<longrightarrow> s x \<noteq> None)"    
  
lemma id_dsub_env: "dsub_env s s"
  apply (simp add: dsub_env_def)
  done
  
lemma add_dsub_env: "\<lbrakk> dsub_env s env \<rbrakk> \<Longrightarrow> dsub_env (add_env s x v) env"   
  apply (simp add: dsub_env_def)
  apply (simp add: add_env_def)
  done      
    
lemma super_sub_use_env: "\<lbrakk> dsub_env s' s; sub_use_env s r_s \<rbrakk> \<Longrightarrow> sub_use_env s' r_s"    
  apply (simp add: dsub_env_def)
  apply (simp add: sub_use_env_def)
  apply (auto)
  done  
  
lemma app_red_exp_dsub_env: "\<lbrakk> app_red_exp are (s1, e1) ax (s2, e2) \<rbrakk> \<Longrightarrow> dsub_env s2 s1"
  apply (case_tac are)
        apply (auto)
        apply (rule_tac id_dsub_env)
       apply (rule_tac id_dsub_env)
      apply (case_tac c)
                  apply (auto)
        apply (rule_tac add_dsub_env)
        apply (rule_tac id_dsub_env)
       apply (rule_tac id_dsub_env)
      apply (rule_tac add_dsub_env)
      apply (rule_tac add_dsub_env)
      apply (rule_tac id_dsub_env)
     apply (rule_tac id_dsub_env)
    apply (rule_tac id_dsub_env)
   apply (rule_tac id_dsub_env)
  apply (case_tac c)
              apply (auto)
    apply (rule_tac id_dsub_env)  
   apply (rule_tac add_dsub_env)
   apply (rule_tac id_dsub_env)
  done
    
  
    (* MAIN PROCESS REDUCTION LEMMA *)
   
lemma srps_thread_case: "\<lbrakk>well_typed_system env delta p_map s1 ps1; valid_reduct app_red_exp; r_ax = ThreadAct; ps1 u = Some (app_hole h e1); wf_hole h;
        ps2 = add_env ps1 u (app_hole h e2); app_red_exp are (s1, e1) ax (s2, e2)\<rbrakk>
       \<Longrightarrow> \<exists>r_s g_ax. (\<exists>p_map'. well_typed_system (red_env env g_ax) (red_delta delta g_ax) p_map' s2 (add_env ps1 u (app_hole h e2))) \<and> safe_act s1 r_s g_ax"
    (* prelim: well_formed_delta / mem_val_env *)
  apply (cut_tac delta="delta" in wts_well_formed_delta)
   apply (simp add: well_typed_system_def)
   apply (auto)
  apply (cut_tac env="env" in wts_mem_val_env)
   apply (simp add: well_typed_system_def)
   apply (auto)
    (* case where action is performed on single thread 'u'. *)
  apply (case_tac "\<not> (well_typed_state s1 env delta \<and> well_typed_proc_set env delta p_map ps1 \<and> sub_nres_map s1 p_map)")
   apply (simp add: well_typed_system_def)
  apply (auto)
    (* we start by obtaining the well-typedness and validity for thread 'u' *)
  apply (simp add: well_typed_proc_set_def)
  apply (auto)
  apply (erule_tac x="u" in allE)
  apply (auto)
  apply (case_tac "p_map u")
   apply (auto)
    (* using the gsre lemma, we know that the resulting expression will be well-typed. *)
  apply (cut_tac env="env" and ?r_s1.0="a" and ?e1.0="app_hole h e1" and tau="UnitTy" and ?r_s2.0="r_s2" and rx="rx" and ?s1.0="s1" and
        delta="delta" and ?e2.0="app_hole h e2" and ax="ax" and ?s2.0="s2" and r_f="a" in safe_full_red_exp)
         apply (auto)
    apply (simp add: sub_nres_map_def)
    apply (simp add: nres_lookup_def)
    apply (erule_tac x="u" in allE)
    apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="g_ax" in exI)  
  apply (auto)
  apply (rule_tac x="add_env p_map u (exp_red_use_env a g_ax)" in exI)
    (* prove that the resulting system is well-typed overall *)
  apply (simp add: well_typed_system_def)
    (* prove that the process set in particular remains well-typed *)
  apply (simp add: well_typed_proc_set_def)
  apply (auto)
    (* prove that the new map still covers the state *)(*
       apply (rule_tac add_full_nres_map)
       apply (simp)*)
    (* prove that it is still disjoint *)
     apply (rule_tac disj_add_nres_map)
      apply (simp)
     apply (rule_tac ?s1.0="s1" in red_sep_nres_map)
         apply (auto)
      apply (rule_tac r_x="infl_use_env a r_s2" in leq_safe_act)
       apply (simp)
      apply (rule_tac lhs_infl_leq_use_env)
      apply (rule_tac id_leq_use_env)
     apply (simp add: sub_nres_map_def)
     apply (erule_tac x="u" in allE)
     apply (erule_tac x="u" in allE)
     apply (simp add: nres_lookup_def)
    (* prove that everything is still well-typed. we start with the original expressions from ps1 *)
    apply (case_tac "u \<noteq> ua")
     apply (case_tac "add_env ps1 u (app_hole h e2) ua")
      apply (auto)
     apply (erule_tac x="ua" in allE)
     apply (simp add: add_env_def)
     apply (case_tac "p_map ua")
      apply (auto)
     apply (rule_tac x="rxa" in exI)
     apply (rule_tac x="r_s2a" in exI)
     apply (rule_tac env'="env" in well_typed_contain_env)
      apply (rule_tac s="s1" in red_contain_env)
       apply (simp_all)
      apply (simp add: well_typed_state_def)
     apply (rule_tac s="s1" and r_f="a" in well_typed_red_deltax)
         apply (auto)
      apply (simp add: disj_nres_map_def)
      apply (erule_tac x="u" in allE)
      apply (erule_tac x="ua" in allE)
      apply (auto)
      apply (simp add: nres_lookup_def)
     apply (simp add: well_typed_state_def)
    (* - proving that it's still proper as well *)(*
      apply (rule_tac s="s1" in red_proper_exp)
        apply (auto)
      apply (simp add: well_typed_state_def)*)
    (* - it's true for the modified res map by valid_reduct's def *)
    apply (simp add: add_env_def)
    apply (erule_tac x="u" in allE)
    apply (auto)
    (* prove that each res map in p_map is still contained in s2. this is true for the original
        res maps since s1 <: s2 *)
   apply (simp add: sub_nres_map_def)
   apply (auto)
   apply (case_tac "u \<noteq> x")
    apply (rule_tac s="s1" in super_sub_use_env)
     apply (simp add: nres_lookup_def)
     apply (simp add: add_env_def)
     apply (rule_tac are="are" in app_red_exp_dsub_env)
     apply (auto)
    (* - it's true for the modified res map by valid_exp *) 
    apply (simp add: nres_lookup_def)
    apply (simp add: add_env_def)
   apply (simp add: nres_lookup_def)
   apply (simp add: add_env_def)
    (* prove that each res map in p_map is disjoint from the new rs_map. this is true for the original
        res maps by lemma *)(*
   apply (case_tac "u \<noteq> ua")
    apply (simp add: add_env_def)
    apply (auto)
    apply (erule_tac x="ua" in allE)
    apply (erule_tac x="ua" in allE)
    apply (case_tac "p_map ua")
     apply (auto)
    apply (simp add: valid_exp_use_env_def)
     apply (rule_tac p_map="p_map" and u="u" and v="ua" and r_p="aa" and r_s="a" and ?s1.0="s1" in red_sep_nres_map2)
           apply (auto)
      apply (rule_tac r_x="infl_use_env a r_s2" in leq_safe_act)
       apply (simp)
      apply (rule_tac lhs_infl_leq_use_env)
      apply (rule_tac id_leq_use_env)
    (* - it's true for the modified res map by valid_reduct's def *)
   apply (simp add: add_env_def)
   apply (simp add: valid_exp_use_env_def)*)
    (* - action safety *)
  apply (rule_tac r_x="infl_use_env a r_s2" in leq_safe_act)
   apply (simp)
  apply (rule_tac lhs_infl_leq_use_env)
  apply (rule_tac id_leq_use_env)
  done      
      
    (* ##### 4a. fork lemma: proves well-typedness of new thread ##### *)
    
definition unit_app_abbrev where
  "unit_app_abbrev e = (AppExp e (ConstExp UnitConst))"
    
    (* this lemma allows us to type the expression passed into a fork so that it can be moved into another thread. since it will be
        stored in another thread, the requirements must be contained by r_s1, yet completely removable from it.
        from the previous lemma, we know that this can be taken from just the non-prim vars in e *)

lemma safe_fork_lam: "\<lbrakk> well_typed env delta r_s1 (app_hole h (AppExp (ConstExp ForkConst) e)) tau r_s2 rx; well_formed_delta env delta; is_value e; is_own r \<rbrakk> \<Longrightarrow>
  well_typed env delta (np_dom_use_env env delta e) (unit_app_abbrev e) UnitTy empty_use_env empty_use_env"
  apply (induct h arbitrary: env r_s1 r_s2 tau rx)
    apply (auto)
  apply (simp add: unit_app_abbrev_def)
    (* base case *)
  apply (cut_tac env="env" and delta="delta" and ?r_s1.0="r_s2a" and e="e" and tau="FunTy UnitTy UnitTy UsePerm a" and ?r_s2.0="r_s3" and rx="rx2" in infl_sexp_wp)
     apply (simp_all)
   apply (rule_tac value_is_sexp)
   apply (auto)
  apply (rule_tac x="UsePerm" in exI)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="np_dom_use_env env delta e" in exI)
  apply (rule_tac x="np_dom_use_env env delta e" in exI)
  apply (auto)
    (* the idea is that the infl_sexp_wp requirements are strictly greater than np_dom, and since np_dom is strong, there is an exact way of
        subtracting to get to np_dom. (we do cheat a little by lifting rx2). *)
   apply (rule_tac t="np_dom_use_env env delta e" and s="diff_use_env (comp_use_env (lift_use_env rx2 ra) (infl_use_env r_s2a r_s3))
    (diff_use_env (lift_use_env (comp_use_env (lift_use_env rx2 ra) (infl_use_env r_s2a r_s3)) r) (np_dom_use_env env delta e))" in subst)
    apply (rule_tac sfl_diff_use_env)
      apply (simp add: np_dom_use_env_def)
      apply (rule_tac strong_dom_use_env)
     apply (simp add: leq_use_env_def)
     apply (auto)
    (* to prove that the infl_sexp_wp reqs are greater than np_dom, we use the fact that any npv must have a permission *)
    apply (simp add: np_dom_use_env_def)
    apply (simp add: dom_use_env_def)
    apply (auto)
    apply (case_tac "comp_use_env (lift_use_env rx2 ra) (infl_use_env r_s2a r_s3) x \<noteq> OwnPerm")
     apply (case_tac "comp_use_env rx2 (infl_use_env r_s2a r_s3) x = NoPerm")
      apply (cut_tac x="x" and env="env" and e="e" and ?r_s1.0="comp_use_env rx2 (infl_use_env r_s2a r_s3)" in well_typed_no_npv_use)
        apply (auto)
    apply (cut_tac r_sa="lift_use_env rx2 ra" and r_sb="infl_use_env r_s2a r_s3" and x="x" in comp_use_no_own_both)
     apply (auto)
    apply (case_tac "rx2 x \<noteq> NoPerm")
     apply (simp add: is_own_def)
    apply (case_tac "rx2 x")
      apply (auto)
    apply (case_tac "infl_use_env r_s2a r_s3 x \<noteq> NoPerm")
     apply (simp add: infl_use_env_def)
     apply (case_tac "r_s2a x = OwnPerm \<and> r_s3 x = NoPerm")
      apply (auto)
    apply (cut_tac r_sa="rx2" and r_sb="infl_use_env r_s2a r_s3" and x="x" in comp_use_none)
      apply (auto)
    (* with that in mind, we manipulate until we match the infl sexp lemma *)
   apply (rule_tac well_typed_diff_perms)
    apply (rule_tac rx="comp_use_env rx2 (infl_use_env r_s2a r_s3)" in well_typed_incr_req)
      apply (rule_tac r_s="comp_use_env rx2 (infl_use_env r_s2a r_s3)" in well_typed_incr_simul_perm)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac comp_leq_use_env1)
        apply (rule_tac self_lift_leq_use_env)
       apply (rule_tac self_comp_leq_use_env2)
      apply (simp)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac comp_leq_use_env1)
      apply (rule_tac self_lift_leq_use_env)
     apply (rule_tac self_comp_leq_use_env2)
    apply (rule_tac id_leq_use_env)
    (* next, we must show that the differential is actually subtractible, which is true since it removes all non-prim vars *)
  apply (auto)
   apply (case_tac "np_dom_use_env env delta e x \<noteq> OwnPerm")
    apply (simp add: np_dom_use_env_def)
    apply (simp add: dom_use_env_def)
   apply (cut_tac r_s="lift_use_env (comp_use_env (lift_use_env rx2 ra) (infl_use_env r_s2a r_s3)) r" and
       r_ex="np_dom_use_env env delta e" and x="x" in diff_use_none_ex)
    apply (simp)
   apply (simp add: own_env_vars_def)
    (* lastly, we prove the various inequalities for application to a unit const *)
  apply (rule_tac x="empty_use_env" in exI)
  apply (rule_tac x="np_dom_use_env env delta e" in exI)
  apply (auto)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac leq_empty_use_env)
  apply (rule_tac x="empty_use_env" in exI)
  apply (auto)
         apply (rule_tac leq_empty_use_env)(*
        apply (simp add: empty_use_env_def)
       apply (simp add: unlim_def)*)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac leq_empty_use_env)
     apply (rule_tac disj_empty_use_env1)
    apply (rule_tac leq_empty_use_env)
   apply (rule_tac leq_empty_use_env)
  apply (simp add: app_req_def)
  apply (rule_tac leq_empty_use_env)
  done      
    
    (* ##### 4b. fork lemma: if x is an npv in 'e', then we have ownership permissions for 'h (fork e)' ##### *)
 
lemma safe_fork_own_npv_use: "\<lbrakk> well_typed env delta r_s1 (app_hole h (AppExp (ConstExp ForkConst) e)) tau r_s2 rx; well_formed_delta env delta;
 is_value e; x \<in> non_prim_vars env delta e \<rbrakk> \<Longrightarrow> r_s1 x = OwnPerm"
  apply (induct h arbitrary: env r_s1 r_s2 tau rx)
        apply (auto)
    (* base case *)
     apply (cut_tac env="env" and ?r_s1.0="r_s2a" and e="e" and ?r_s2.0="r_s3" and rx="rx2" in infl_sexp_wp)
       apply (auto)
      apply (rule_tac value_is_sexp)
      apply (simp)
     apply (case_tac "comp_use_env rx2 (infl_use_env r_s2a r_s3) x = NoPerm")
      apply (cut_tac env="env" and x="x" and e="e" and ?r_s1.0="comp_use_env rx2 (infl_use_env r_s2a r_s3)" in well_typed_no_npv_use)
        apply (auto)
     apply (case_tac "rx2 x \<noteq> NoPerm")
      apply (cut_tac r_x="lift_use_env rx2 r" and r_s="r_s1" and x="x" in leq_use_own)
        apply (simp add: is_own_def)
       apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
        apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
         apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
          apply (auto)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (rule_tac self_comp_leq_use_env2)
     apply (case_tac "infl_use_env r_s2a r_s3 x \<noteq> NoPerm")
      apply (simp add: infl_use_env_def)
      apply (case_tac "r_s2a x = OwnPerm \<and> r_s3 x = NoPerm")
       apply (auto)
      apply (rule_tac r_x="r_s2a" in leq_use_own)
       apply (auto)
     apply (cut_tac r_sa="rx2" and r_sb="infl_use_env r_s2a r_s3" and x="x" in comp_use_none)
       apply (auto)
    (* rhs induct *)
    apply (rule_tac r_x="r_s2a" in leq_use_own)
     apply (simp)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
    (* rhs pair *)
    apply (rule_tac r_x="r_s2a" in leq_use_own)
    apply (simp)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  done    
    
    (* ##### 4c. fork lemma: proves well-typedness of original thread post-fork ##### *)

    (* this lemma proves that e should be removable from the fork. combined with the previous lemmas, we can also remove the
      permissions of e, and type the two resultant expressions disjointly. *)
    
lemma safe_fork_exp_ih: "\<lbrakk> well_typed env delta r_s1 (app_hole h (AppExp (ConstExp ForkConst) e)) tau r_s2 rx; well_formed_delta env delta; is_value e \<rbrakk> \<Longrightarrow>
  well_typed env delta r_s1 (app_hole h (ConstExp UnitConst)) tau r_s2 rx"
  apply (induct h arbitrary: env r_s1 e tau r_s2 rx)
        apply (auto)
    (* base case *)
        apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
         apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
          apply (simp)
         apply (rule_tac diff_leq_use_env)
         apply (rule_tac well_typed_perm_leq)
         apply (auto)
    (* lhs induct *)
       apply (rule_tac x="t1" in exI)
       apply (rule_tac x="r" in exI)
       apply (rule_tac x="a" in exI)
       apply (rule_tac x="r_s2a" in exI)
       apply (rule_tac x="rx1" in exI)
       apply (auto)
    (* rhs induct *)
      apply (rule_tac x="t1" in exI)
      apply (rule_tac x="r" in exI)
      apply (rule_tac x="a" in exI)
      apply (rule_tac x="r_s2a" in exI)
      apply (rule_tac x="rx1" in exI)
      apply (auto)
      apply (rule_tac x="rx2" in exI)
      apply (rule_tac x="r_s3" in exI)
      apply (auto)
    (* if case *)
     apply (rule_tac x="rx'" in exI)
     apply (rule_tac x="r_s2a" in exI)
     apply (auto)
    (* lhs pair case *)
    apply (rule_tac x="r_s2a" in exI)
    apply (rule_tac x="r_s3" in exI)
    apply (rule_tac x="rx1" in exI)
    apply (auto)
    (* rhs pair case *)
   apply (rule_tac x="r_s2a" in exI)
   apply (rule_tac x="r_s3" in exI)
   apply (rule_tac x="rx1" in exI)
   apply (auto)
   apply (rule_tac x="rx2" in exI)
   apply (auto)
  done
    
    (* uses:
        - safe_fork_hole_npv_use: to determine that if x is an np-var, it is not in h
        - 4b (safe_fork_own_npv_use) to determine that if x is an np-var, we own it
    *)
  
lemma safe_fork_exp: "\<lbrakk> well_typed env delta r_s1 (app_hole h (AppExp (ConstExp ForkConst) e)) tau r_s2 rx;
  well_formed_delta env delta; sub_use_env s r_s1; wf_hole h; is_value e \<rbrakk> \<Longrightarrow>
  well_typed env delta (diff_use_env r_s1 (np_dom_use_env env delta e)) (app_hole h (ConstExp UnitConst)) tau
  (diff_use_env r_s2 (np_dom_use_env env delta e)) (diff_use_env rx (np_dom_use_env env delta e))"
  apply (rule_tac well_typed_diff_perms)
   apply (rule_tac safe_fork_exp_ih)
    apply (auto)
  apply (simp add: non_prim_vars_def)
  apply (auto)
    (* we want to show that if x is in the dominator, it is not an np-var in h.
        > if x is an np-var itself, it cannot be in e by lemma *)
  apply (case_tac "x \<in> non_prim_vars env delta e")
   apply (cut_tac h="h" and x="x" and e="ConstExp UnitConst" in app_hole_res_vars_rev)
    apply (auto)
   apply (cut_tac h="h" and x="x" and env="env" and ?r_s1.0="r_s1" and e="e" in safe_fork_hole_npv_use)
        apply (auto)
  apply (simp add: own_env_vars_def)
  apply (simp add: np_dom_use_env_def)
  apply (simp add: dom_use_env_def)(*
    (* otherwise, x is in the completion. we identify its ancestor z. *)
  apply (case_tac "\<exists>xa. x = Loc xa \<and> (\<exists>l z. Loc z \<in> non_prim_vars env e \<and> path_lookup rs_map z l xa)")
   apply (auto)
    (* we note that z is a np-var of e therefore r_s1 z = Own *)
  apply (cut_tac x="Loc z" and env="env" in safe_fork_own_npv_use)
     apply (auto)
    (* x then is in the lookup map of some parent y. *)
  apply (cut_tac rs_map="rs_map" and z="z" and x="xa" in path_lookup_parent)
     apply (auto)
    (* with that in mind, by separation, x is disjoint from r_s1. *)
  apply (case_tac "r_s1 (Loc xa) \<noteq> NoPerm")
   apply (simp add: valid_exp_use_env_def)
   apply (simp add: sep_nres_map_def)
   apply (auto)
   apply (erule_tac x="y" in allE)
   apply (simp add: nres_lookup_def)
   apply (simp add: strong_disj_use_env_def)
   apply (erule_tac x="Loc xa" in allE)
   apply (auto)
    (* by extension, x is not in 'h (fork e)' *)
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and x="Loc xa" in well_typed_no_npv_use)
    apply (auto)
  apply (simp add: non_prim_vars_def)
    (* the very last part is showing that x not in 'h (fork e)' implies x not in 'h ()'. *)
  apply (cut_tac x="Loc xa" and h="h" and e="ConstExp UnitConst" in app_hole_res_vars_rev)
   apply (auto)
  apply (cut_tac x="Loc xa" and h="h" and e="AppExp (ConstExp ForkConst) e" in app_hole_res_vars2)
   apply (auto)*)
  done

    (* ##### 4d. fork lemma: structural lemma for thread-disjointness in fork case ###### *)
    
lemma alift_strong_disj_use_env1: "\<lbrakk> strong_disj_use_env r_x r_s \<rbrakk> \<Longrightarrow> strong_disj_use_env (lift_use_env r_x r) r_s"    
  apply (simp add: strong_disj_use_env_def)
  apply (auto)
  apply (case_tac r)
    apply (auto)
  done
  
    (* a special lemma that makes it easier to comprehend our strategy for proving the disjointness of the fork *)
lemma fork_disj_nres_map: "\<lbrakk> disj_nres_map p_map; p_map u = Some r_s; is_own r;
  leq_use_env r_xa (lift_use_env r_s r); leq_use_env r_xb (lift_use_env r_s r);
  strong_disj_use_env r_xa r_xb \<rbrakk> \<Longrightarrow> disj_nres_map (add_env (add_env p_map u r_xa) v r_xb)"
  apply (rule_tac disj_add_nres_map)
   apply (rule_tac disj_add_nres_map)
    apply (simp)
    (* first we must prove the disjointness of the new assignment to u *)
   apply (simp add: sep_nres_map_def)
   apply (auto)
   apply (case_tac "u = x")
    apply (cut_tac rs_map="p_map" and x="u" in nres_rem_same)
    apply (auto)
    apply (rule_tac empty_strong_disj_use_env2)
   apply (cut_tac rs_map="p_map" and x="u" and y="x" in nres_rem_diff)
    apply (auto)
   apply (simp add: disj_nres_map_def)
   apply (erule_tac x="u" in allE)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (rule_tac r_s="lift_use_env r_s r" in strong_disj_leq_use_env1)
    apply (rule_tac alift_strong_disj_use_env1)
    apply (simp add: nres_lookup_def)
   apply (simp)
    (* next we prove the disjointness of v, starting with its disjointness to u *)
  apply (simp add: sep_nres_map_def)
  apply (auto)
  apply (case_tac "x = v")
   apply (cut_tac rs_map="add_env p_map u r_xa" and x="v" in nres_rem_same)
   apply (auto)
   apply (rule_tac empty_strong_disj_use_env2)
  apply (case_tac "x = u")
   apply (auto)
   apply (case_tac "\<not> nres_lookup (add_env p_map u r_xa) u = r_xa")
    apply (simp add: nres_lookup_def)
    apply (simp add: add_env_def)
   apply (cut_tac rs_map="add_env p_map u r_xa" and x="v" and y="u" in nres_rem_diff)
    apply (auto)
   apply (rule_tac comm_strong_disj_use_env)
   apply (simp)
    (* next we prove its disjointess to the rest of the map *)
  apply (cut_tac rs_map="add_env p_map u r_xa" and x="v" and y="x" in nres_rem_diff)
   apply (auto)
  apply (cut_tac rs_map="p_map" and x="u" and y="x" and r_s="r_xa" in nres_add_diff)
   apply (auto)
  apply (simp add: disj_nres_map_def)
  apply (erule_tac x="u" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (rule_tac r_s="lift_use_env r_s r" in strong_disj_leq_use_env1)
   apply (rule_tac alift_strong_disj_use_env1)
   apply (simp add: nres_lookup_def)
  apply (simp)
  done

    (* ##### 4_X. process reduction validity for fork case ##### *)    
  
lemma lift_sep_nres_map: "\<lbrakk> sep_nres_map r_s rs_map \<rbrakk> \<Longrightarrow> sep_nres_map (lift_use_env r_s r) rs_map"  
  apply (simp add: sep_nres_map_def)
  apply (auto)
  apply (rule_tac alift_strong_disj_use_env1)
  apply (auto)
  done
  
lemma srps_fork_case: "\<lbrakk>well_typed_system env delta p_map s2 ps1; r_ax = ForkAct; ps1 u = Some (app_hole h (AppExp (ConstExp ForkConst) e));
                wf_hole h; is_value e; ps2 = add_env (add_env ps1 u (app_hole h (ConstExp UnitConst))) v (AppExp e (ConstExp UnitConst)); fresh_var ps1 v;
                s1 = s2\<rbrakk>
               \<Longrightarrow> \<exists>r_s g_ax. (\<exists>p_map'. well_typed_system (red_env env g_ax) (red_delta delta g_ax) p_map' s2
                                     (add_env (add_env ps1 u (app_hole h (ConstExp UnitConst))) v (AppExp e (ConstExp UnitConst)))) \<and>
                          safe_act s2 r_s g_ax"
    (* prelim: well_formed_delta / mem_val_env *)
  apply (cut_tac delta="delta" in wts_well_formed_delta)
   apply (simp add: well_typed_system_def)
   apply (auto)
  apply (cut_tac env="env" in wts_mem_val_env)
   apply (simp add: well_typed_system_def)
   apply (auto)
    (* fork case. no resources are generated in this step *)
  apply (rule_tac x="empty_use_env" in exI)
  apply (rule_tac x="NoResAct" in exI)
  apply (auto)
  apply (simp add: well_typed_system_def)
  apply (auto)
    (* before we can give the new process map types, we have to get the well-typedness statement for h (fork e) *)
  (*apply (case_tac "\<not> (case ps1 u of None \<Rightarrow> True
                     | Some e \<Rightarrow> (case lookup_mem p_map u of None \<Rightarrow> False
                                 | Some (r_c, s') \<Rightarrow> \<exists>rx r_s r_s2. well_typed env r_s e UnitTy r_s2 rx \<and> valid_use_env s2 rs_map r_c r_s))")*)
  apply (case_tac "\<not> (
     disj_nres_map p_map \<and> (\<forall>u. case ps1 u of None \<Rightarrow> True | Some e \<Rightarrow>
      (case p_map u of None \<Rightarrow> False | Some r_s \<Rightarrow> \<exists>rx r_s2. well_typed env delta r_s e UnitTy r_s2 rx)))")
   apply (simp add: well_typed_proc_set_def)
  apply (auto)
  apply (case_tac "\<not> (case ps1 u of None \<Rightarrow> True | Some e \<Rightarrow> (case p_map u of None \<Rightarrow> False | Some r_s \<Rightarrow> \<exists>rx r_s2. well_typed env delta r_s e UnitTy r_s2 rx))")
   apply (erule_tac x="u" in allE)
   apply (auto)
  apply (case_tac "p_map u")
   apply (auto)
    (* using the fork lemmas, we can generate a type for e + a type for h () *)
  apply (cut_tac eq_own)
  apply (auto)
  apply (cut_tac env="env" and e="e" and ?r_s1.0="a" and tau="UnitTy" and h="h" and ?r_s2.0="r_s2" and rx="rx" and r="r" in safe_fork_lam)
     apply (auto)
  apply (cut_tac env="env" and e="e" and ?r_s1.0="a" and tau="UnitTy" and h="h" and ?r_s2.0="r_s2" and rx="rx" and s="s2" in safe_fork_exp)
       apply (auto)
    apply (simp add: well_typed_state_def)
    (* - complete proof that a is still valid *)
   apply (simp add: well_typed_proc_set_def)
   apply (simp add: sub_nres_map_def)
   apply (erule_tac x="u" in allE)
   apply (erule_tac x="u" in allE)
   apply (simp add: nres_lookup_def)
    (* - prelim: prove that (full_dom_use_env env rs_map e) \<le> a (old complete map) *)(*
  apply (cut_tac rs_map="rs_map" and e="e" and r_c="a" and h="h" and env="env" in valid_full_dom_leq_use_env)
      apply (auto)
   apply (simp add: well_typed_state_def)*)
    (* - prelim: np_dom_use_env env e \<le> lift_use_env a r *)
  apply (cut_tac r_sc="np_dom_use_env env delta e" and r_sb="np_dom_use_env env delta (app_hole h (AppExp (ConstExp ForkConst) e))" 
      and r_sa="lift_use_env a r" in trans_leq_use_env)
    apply (rule_tac wt_np_leq_use_env)
     apply (auto)
   apply (simp add: np_dom_use_env_def)
   apply (rule_tac dist_dom_leq_use_env)
   apply (auto)
   apply (simp add: non_prim_vars_def)
   apply (cut_tac x="x" and e="AppExp (ConstExp ForkConst) e" in app_hole_res_vars)
    apply (auto)
    (* we fill in the  new process map, by taking perms from 'u' [[ h () ]] and giving them to 'v' [[ e () ]] *)
  apply (rule_tac x="add_env (add_env p_map u (diff_use_env a (np_dom_use_env env delta e))) v (np_dom_use_env env delta e)" in exI)
  apply (simp add: well_typed_proc_set_def)
  apply (auto)
    (* completeness of the new process map *)(*
      apply (rule_tac add_full_nres_map)
      apply (rule_tac add_full_nres_map)
      apply (simp)*)
    (* disjointness of the new process map *)
     apply (rule_tac r_s="a" and r="r" in fork_disj_nres_map)
          apply (auto)
      apply (rule_tac lift_leq_use_env)
      apply (rule_tac self_diff_leq_use_env)
     apply (rule_tac r_s="np_dom_use_env env delta e" in strong_disj_leq_use_env2)
      apply (rule_tac reduce_strong_disj_use_env)
       apply (simp add: disj_use_env_def)
       apply (auto)
        apply (rule_tac r_s="a" in mini_disj_strong_use_env)
         apply (rule_tac id_leq_use_env)
        apply (simp add: np_dom_use_env_def)
        apply (rule_tac strong_dom_use_env)
       apply (rule_tac mini_disj_diff_use_env)
      apply (simp add: np_dom_use_env_def)
      apply (rule_tac strong_dom_use_env)
     apply (rule_tac id_leq_use_env)
    (* proving everything is still well-typed. we start with ua = v, ie the 'e ()' thread. *)
    apply (case_tac "ua = v")
     apply (case_tac "\<not> add_env (add_env ps1 u (app_hole h (ConstExp UnitConst))) v (AppExp e (ConstExp UnitConst)) ua =
      Some (unit_app_abbrev e)")
      apply (simp add: add_env_def)
      apply (simp add: unit_app_abbrev_def)
     apply (auto)
     apply (case_tac "\<not> (add_env (add_env p_map u (diff_use_env a (np_dom_use_env env delta e))) v (np_dom_use_env env delta e)) v =
      Some (np_dom_use_env env delta e)")
      apply (simp add: add_env_def)
     apply (auto)
    (* - properness *)(*
     apply (cut_tac rs_map="rs_map" and h="h" and e="AppExp (ConstExp ForkConst) e" in proper_app_hole_split2)
      apply (simp)
     apply (simp add: unit_app_abbrev_def)
     apply (simp add: proper_exp_def)*)
    (* - well-typedness for ua = u, the 'h ()' thread*)
    apply (case_tac "ua = u")
     apply (case_tac "\<not> add_env (add_env ps1 u (app_hole h (ConstExp UnitConst))) v (AppExp e (ConstExp UnitConst)) ua =
        Some (app_hole h (ConstExp UnitConst))")
      apply (simp add: add_env_def)
     apply (auto)
     apply (case_tac "\<not> (add_env (add_env p_map u (diff_use_env a (np_dom_use_env env delta e))) v (np_dom_use_env env delta e)) u =
        Some (diff_use_env a (np_dom_use_env env delta e))")
      apply (simp add: add_env_def)
     apply (auto)
    (* - properness *)(*
     apply (cut_tac rs_map="rs_map" and h="h" in proper_app_hole_split1)
      apply (simp)
     apply (rule_tac proper_app_hole_recon)
      apply (simp)
     apply (simp add: proper_exp_def)*)
    (* - well-typedness for unaltered threads *)
    apply (erule_tac x="ua" in allE)
    apply (case_tac "\<not> add_env (add_env ps1 u (app_hole h (ConstExp UnitConst))) v (AppExp e (ConstExp UnitConst)) ua = ps1 ua")
     apply (simp add: add_env_def)
    apply (case_tac "ps1 ua")
     apply (auto)
    apply (case_tac "\<not> (add_env (add_env p_map u (diff_use_env a (np_dom_use_env env delta e))) v (np_dom_use_env env delta e)) ua =
      p_map ua")
     apply (simp add: add_env_def)
    apply (auto)(*
    apply (erule_tac x="ua" in allE)
    apply (auto)*)
    (* proving the new process map is contained in the state *)
   apply (rule_tac add_sub_nres_map1)
    apply (rule_tac add_sub_nres_map1)
     apply (simp)
    apply (rule_tac r_s="a" in trans_sub_use_env)
     apply (simp add: sub_nres_map_def)
     apply (erule_tac x="u" in allE)
     apply (erule_tac x="u" in allE)
     apply (simp add: nres_lookup_def)
    apply (rule_tac self_diff_leq_use_env)
   apply (rule_tac r_s="lift_use_env a r" in trans_sub_use_env)
    apply (rule_tac lift_sub_use_env)
    apply (simp add: sub_nres_map_def)
    apply (erule_tac x="u" in allE)
    apply (erule_tac x="u" in allE)
    apply (simp add: nres_lookup_def)
   apply (simp)
    (* proving that separation still holds. we again start with ua = v, the 'e ()' thread *)(*
  apply (case_tac "ua = v")
   apply (simp add: add_env_def)
   apply (rule_tac r_s="lift_use_env a r" in leq_sep_nres_map)
    apply (simp)
   apply (rule_tac lift_sep_nres_map)
   apply (erule_tac x="u" in allE)
   apply (simp)
    (* - same for ua = u, ie the 'h ()' thread *)
  apply (case_tac "ua = u")
   apply (simp add: add_env_def)
   apply (rule_tac r_s="a" in leq_sep_nres_map)
    apply (rule_tac self_diff_leq_use_env)
   apply (erule_tac x="u" in allE)
   apply (simp)
    (* - lastly prove separation for original threads *)
  apply (simp add: add_env_def)*)
  done
    
    (* ##### 5. final proof composition ##### *)  
    
lemma safe_red_proc_set: "\<lbrakk> well_typed_system env delta p_map s1 ps1; red_proc_set (s1, ps1) r_ax (s2, ps2); valid_reduct app_red_exp \<rbrakk> \<Longrightarrow>
  (\<exists> r_s g_ax p_map'. well_typed_system (red_env env g_ax) (red_delta delta g_ax) p_map' s2 ps2 \<and> safe_act s1 r_s g_ax)"
    (* split over process reduction type. *)
  apply (case_tac "r_ax")
    apply (auto)
    (* single thread action case. *)
    apply (rule_tac srps_thread_case)
          apply (auto)
    (* fork case. *)
   apply (rule_tac srps_fork_case)
          apply (auto)
    (* send case. *)
  apply (rule_tac srps_send_case)
                apply (auto)
done
  
end