theory RedSafeCase
  imports WTLemma RedSafeUnpack
begin 
  
  (* ###### case lemmas *)    

lemma safe_app_op_case: "\<lbrakk> app_red_exp OpApp (s1, AppExp (OpExp xop) v) ax (s2, e2); FunTy tx tau r a = op_type xop \<rbrakk> \<Longrightarrow> well_typed env delta r_s1 e2 tau r_s1 empty_use_env"
  apply (case_tac v)
       apply (auto)
  apply (case_tac ax)
   apply (auto)
    (* given xop: op, x1: const, assuming tau matches the return type of xop, we want to show that e2 is well-typed.
        now e2 can either be an op or a const.
    *)
  apply (case_tac "\<not> (\<exists> rop. e2 = OpExp rop)")
   apply (case_tac "\<not> (\<exists> c. e2 = ConstExp c)")
    apply (auto)
        apply (case_tac xop)
             apply (auto)
    (* the hard part is proving that e2 will have the right type. *)
       apply (case_tac xop)
            apply (auto)
         apply (simp add: pure_fun_def)
        apply (simp add: pure_fun_def)
       apply (simp add: pure_fun_def)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac leq_empty_use_env)
    (* op case, same thing *)
    apply (case_tac xop)
         apply (auto)
      apply (simp add: pure_fun_def)
     apply (simp add: pure_fun_def)
    apply (simp add: pure_fun_def)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac leq_empty_use_env)
  done  
        
    
lemma add_proper_delta: "\<lbrakk> proper_delta s delta; fresh_var s x \<rbrakk> \<Longrightarrow> proper_delta (add_env s x v) (add_delta delta x x)"    
  apply (simp add: proper_delta_def)
  apply (auto)
  apply (case_tac "xa \<noteq> x")
   apply (auto)
   apply (simp add: add_env_def)
   apply (case_tac "s xa")
    apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (auto)
   apply (simp add: add_delta_def)
   apply (simp add: add_env_def)
  apply (simp add: add_env_def)
  apply (simp add: add_delta_def)
  done
    
lemma well_typed_list_incr_perm: "\<lbrakk> well_typed_list env delta r_x l tau; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> well_typed_list env delta r_s l tau"        
  apply (induct l arbitrary: r_x)
   apply (auto)
  apply (rule_tac rx="r_x" in well_typed_incr_req)
    apply (auto)
   apply (rule_tac r_s="r_x" in well_typed_incr_simul_perm)
    apply (auto)
  apply (rule_tac id_leq_use_env)
  done
  
lemma well_typed_mv_incr_perm: "\<lbrakk> well_typed_mem_value env delta r_x tau v; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> well_typed_mem_value env delta r_s tau v"    
  apply (case_tac v)
    apply (auto)
  apply (rule_tac well_typed_list_incr_perm)
   apply (auto)
  done
    
    (* the point of this lemma is to state that new values can be added *)
lemma well_typed_state_add_vars: "\<lbrakk> well_typed_state s1 env delta; fresh_var s1 x; well_typed_mem_value env delta empty_use_env tau v \<rbrakk> \<Longrightarrow>
  well_typed_state (add_env s1 x v) (add_env env (Loc x) tau) (add_delta delta x x)"
    (* starts by proving the validity of the env + res map *)
  apply (simp add: well_typed_state_def)
  apply (auto)
    apply (rule_tac dist_add_sub_env)
    apply (simp)(*
    (* the state is still fully covered by the map *)
      apply (simp add: full_nres_map_def)
      apply (auto)
       apply (simp add: add_env_def)
       apply (auto)
      apply (simp add: add_env_def)
      apply (auto)
    (* prove disjointness remains *)
     apply (rule_tac disj_add_nres_map)
      apply (auto)
    (* prove containment remains *)
    apply (rule_tac add_sub_nres_map2)
     apply (rule_tac add_sub_nres_map1)
      apply (simp_all)
    apply (simp add: fresh_var_def)*)
    (* prove properness of delta *)
   apply (rule_tac add_proper_delta)
     apply (auto)
    (* now it remains to prove that all the values are still well-typed. we do the x = xa case first *)
  apply (erule_tac x="xa" in allE)
  apply (case_tac "x = xa")
   apply (case_tac "add_env s1 x v x")
    apply (simp add: add_env_def)
   apply (auto)
   apply (case_tac "add_env env (Loc x) tau (Loc x)")
    apply (simp add: add_env_def)
   apply (auto)
(*
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" in nres_add_same)
   apply (simp)*)
   apply (case_tac "env (Loc x) \<noteq> None")
    apply (simp add: fresh_var_def)
    apply (simp add: sub_env_def)
    apply (erule_tac x="Loc x" in allE)
    apply (auto)
   apply (rule_tac r_x="empty_use_env" in well_typed_mv_incr_perm)
    apply (rule_tac well_typed_mv_add_vars)
     apply (rule_tac well_typed_mv_add_delta)
      apply (simp add: add_env_def)
     apply (auto)
   apply (rule_tac leq_empty_use_env)
    (* now we do that x \<noteq> xa case *)
  apply (simp add: add_env_def)
  apply (case_tac "s1 xa")
   apply (auto)
  apply (simp add: add_env_def)
  apply (case_tac "env (Loc xa)")
   apply (auto)
  apply (case_tac "add_delta delta x x xa \<noteq> delta xa")
   apply (simp add: add_delta_def)
  apply (rule_tac well_typed_mv_add_vars)
   apply (rule_tac well_typed_mv_add_delta)
    apply (auto)
   apply (simp add: fresh_var_def)
   apply (simp add: sub_env_def)
   apply (erule_tac x="Loc x" in allE)
   apply (auto)
  apply (simp add: fresh_var_def)
  apply (simp add: sub_env_def)
  apply (erule_tac x="Loc x" in allE)
  apply (auto)
  done    

lemma sacc_make_act_case: "
        \<lbrakk>well_typed_state s1 env delta; app_red_exp ConstApp (s1, AppExp (ConstExp c) v) (MakeAct x) (s2, e2); sub_use_env s1 r_f;
                well_typed env delta r_s1 v t1 r_s2 rx2; leq_use_env r_s3 (diff_use_env r_s2 (comp_use_env rx1 (lift_use_env rx2 r))); leq_use_env rx r_s3;
                FunTy t1 t2 r a \<in> const_type c; c \<noteq> FixConst; ax = MakeAct x; leq_use_env r_s1 r_f\<rbrakk>
               \<Longrightarrow> well_typed (add_env env (Loc x) t2) (add_delta delta x x) (add_use_env r_s1 (Loc x) OwnPerm) e2 t2 r_s3 rx"
    (* e2 will always be the generated variable *)
  apply (case_tac "e2 \<noteq> VarExp (LocType x)")
   apply (case_tac c)
                apply (auto)
  apply (simp add: add_env_def)
    (* remove simple addition based reqs *)
  apply (case_tac "add_delta delta x x x \<noteq> x")
   apply (simp add: add_delta_def)
  apply (simp add: add_env_def)
  apply (auto)
   apply (case_tac c)
               apply (auto)
   apply (rule_tac ereq_leq_use_envx)
   apply (simp add: add_use_env_def)
    (* prelim: x is fresh *)
  apply (case_tac "\<not> fresh_var s1 x")
   apply (case_tac c)
                apply (auto)
    (* prelim: r_s3 \<le> r_s1 *)
  apply (cut_tac r_sc="r_s3" and r_sb="diff_use_env r_s2 (comp_use_env rx1 (lift_use_env rx2 r))" and r_sa="r_s1" in trans_leq_use_env)
    apply (rule_tac diff_leq_use_env)
    apply (simp_all)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
    (* we can achieve the desired permissions by removing x from the end perms + reqs (which is okay since they dont appear anywhere else yet). *)
  apply (rule_tac x="one_use_env (Loc x) OwnPerm" in exI)
  apply (auto)
    (* - the end perm bound is possible since we assume r_s3 didnt already contain x2 *)
    apply (rule_tac t=" leq_use_env r_s3 (diff_use_env (add_use_env r_s1 (Loc x) OwnPerm) (comp_use_env (ereq_use_env (Loc x) t2) (one_use_env (Loc x) OwnPerm)))" and
        s=" leq_use_env (rem_use_env r_s3 (Loc x)) (diff_use_env (add_use_env r_s1 (Loc x) OwnPerm) (comp_use_env (ereq_use_env (Loc x) t2) (one_use_env (Loc x) OwnPerm)))" in subst)
     apply (cut_tac r_s="r_s3" and x="Loc x" in ignore_rem_use_env)
      apply (rule_tac r_s="r_s1" in leq_use_none)
       apply (auto)
     apply (simp add: sub_use_env_def)
     apply (simp add: fresh_var_def)
     apply (cut_tac r_x="r_s1" and r_s="r_f" and x="Loc x" in leq_use_none)
       apply (auto)
    (* - given this, we can finish proving the bound *)
    apply (rule_tac rhs_unroll_dcl_use_env)
    apply (rule_tac rhs_unroll_rem_use_env)
    apply (rule_tac dist_rem_leq_use_env)
    apply (rule_tac rhs_weak_leq_use_env)
     apply (rule_tac weak_ereq_use_env)
     apply (case_tac c)
                   apply (auto)
     apply (simp add: pure_fun_def)
     apply (simp add: unlim_def)
    apply (rule_tac rhs_add_leq_use_env)
     apply (auto)
    (* - unrolling definitions to prove the subtracter bound *)
   apply (simp add: leq_use_env_def)
   apply (simp add: one_use_env_def)
   apply (simp add: add_use_env_def)
    (* - proving the requirement bound *)
  apply (rule_tac r_sb="diff_use_env (ereq_use_env (Loc x) t2) (one_use_env (Loc x) OwnPerm)" in trans_leq_use_env)
   apply (simp add: ereq_use_env_def)
   apply (rule_tac diff_one_leq_use_env)
  apply (rule_tac lhs_unroll_dcl_use_env)
  apply (rule_tac dist_diff_leq_use_env)
  apply (rule_tac self_diff_leq_use_env)
  done    
    
lemma add_env_force_ex: "\<lbrakk> \<forall> z. add_env s x v z = add_env s x w z \<rbrakk> \<Longrightarrow> v = w"    
  apply (erule_tac x="x" in allE)
  apply (simp add: add_env_def)
  done
    
lemma add_env_force: "\<lbrakk> add_env s x v = add_env s x w \<rbrakk> \<Longrightarrow> v = w"    
  apply (rule_tac s="s" and x="x" and v="v" and w="w" in add_env_force_ex)
  apply (auto)
  done
    
lemma disj_add_use_env: "\<lbrakk> disj_use_env r_s r_x; r_s x = NoPerm \<rbrakk> \<Longrightarrow> disj_use_env r_s (add_use_env r_x x r)"    
  apply (simp add: disj_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  done
    
lemma strong_disj_add_use_env: "\<lbrakk> strong_disj_use_env r_s r_x; r_s x = NoPerm \<rbrakk> \<Longrightarrow> strong_disj_use_env r_s (add_use_env r_x x r)"    
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: add_use_env_def)
  done    

lemma add_valid_exp_use_env: "\<lbrakk> valid_nres_map s rs_map; valid_exp_use_env s rs_map r_s; fresh_var s x \<rbrakk> \<Longrightarrow>
  valid_exp_use_env (add_env s x v) (add_env rs_map x empty_use_env) (add_use_env r_s (Loc x) OwnPerm)"  
  apply (simp add: valid_exp_use_env_def)  
  apply (auto)
    (* domain preservation *)
   apply (rule_tac rhs_add_sub_use_env)
   apply (rule_tac add_sub_use_env)
    apply (simp)
   apply (simp add: add_env_def)
    (* separation *)
  apply (simp add: sep_nres_map_def)
  apply (auto)
  apply (case_tac "x = xa")
   apply (auto)
   apply (simp add: nres_add_same)
   apply (rule_tac empty_strong_disj_use_env2)
  apply (simp add: nres_add_diff)
  apply (erule_tac x="xa" in allE)
  apply (rule_tac comm_strong_disj_use_env)
  apply (rule_tac strong_disj_add_use_env)
  apply (rule_tac comm_strong_disj_use_env)
   apply (simp)
  apply (simp add: valid_nres_map_def)
  apply (simp add: sub_nres_map_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (simp add: sub_use_env_def)
  apply (simp add: fresh_var_def)
  apply (auto)
  done


  
    (*
      the hard part that we're dealing with right now is that at the end using pairs does NOT work for the WRITE constants,
        since we want "use" permission for the array, but "own" permission for the value being written.

      what this suggests is that we have to allow for constant + application to be a value.
      even if we do this, we need to give them all their own unique cases, just like for unpacking.
      - this is more complicated than it is with constants, since the contents of the first arg will generally be somewhat complex.

    *)
    

lemma saccmk2_var_type: "\<lbrakk> env (Loc x) = Some (ChanTy t c_end); delta x = x \<rbrakk> \<Longrightarrow>
  well_typed env delta (one_use_env (Loc x) OwnPerm) (VarExp (LocType x)) (ChanTy t c_end) (one_use_env (Loc x) OwnPerm) (one_use_env (Loc x) OwnPerm)"    
  apply (auto)
   apply (rule_tac ereq_leq_use_envx)
   apply (simp add: one_use_env_def)
  apply (rule_tac x="empty_use_env" in exI)
  apply (auto)
     apply (rule_tac rhs_weak_leq_use_env)
      apply (rule_tac dist_weak_comp_use_env)
       apply (rule_tac weak_ereq_use_env)
       apply (simp add: unlim_def)
      apply (simp add: weak_use_env_def)
      apply (simp add: empty_use_env_def)
     apply (rule_tac id_leq_use_env)
     apply (rule_tac id_leq_use_env)
   apply (rule_tac leq_empty_use_env)
  apply (rule_tac diff_leq_use_env)
  apply (rule_tac ereq_leq_use_envx)
  apply (simp add: one_use_env_def)
  done
  
lemma saccmk2_pair_type: "\<lbrakk> well_typed env delta (one_use_env x1 OwnPerm) v1 t1 (one_use_env x1 OwnPerm) (one_use_env x1 OwnPerm);
  well_typed env delta (one_use_env x2 OwnPerm) v2 t2 (one_use_env x2 OwnPerm) (one_use_env x2 OwnPerm);
  r_s1 x1 = OwnPerm; r_s1 x2 = OwnPerm; r_s2 x1 = NoPerm; r_s2 x2 = NoPerm;
  leq_use_env r_s2 r_s1; leq_use_env rx r_s2; is_own r; x1 \<noteq> x2 \<rbrakk> \<Longrightarrow>
  well_typed env delta r_s1 (PairExp v1 v2) (PairTy t1 t2 r) r_s2 rx"
  apply (auto)
  apply (rule_tac x="r_s1" in exI)
  apply (rule_tac x="r_s1" in exI)
  apply (rule_tac x="one_use_env x1 OwnPerm" in exI)
  apply (auto)
   apply (rule_tac r_s="one_use_env x1 OwnPerm" in well_typed_incr_simul_perm)
    apply (simp add: leq_use_env_def)
    apply (simp add: one_use_env_def)
   apply (simp)
  apply (rule_tac x="one_use_env x2 OwnPerm" in exI)
  apply (auto)
       apply (rule_tac r_s="one_use_env x2 OwnPerm" in well_typed_incr_simul_perm)
        apply (simp add: leq_use_env_def)
        apply (simp add: one_use_env_def)
       apply (simp)
      apply (simp add: is_own_def)
      apply (simp add: leq_use_env_def)
      apply (simp add: one_use_env_def)
     apply (simp add: is_own_def)
     apply (simp add: leq_use_env_def)
     apply (simp add: one_use_env_def)
    apply (simp add: is_own_def)
    apply (case_tac "max_aff (req_type t1) (req_type t2)")
      apply (auto)
   apply (simp add: is_own_def)
   apply (simp add: one_use_env_def)
   apply (simp add: disj_use_env_def)
   apply (simp add: mini_disj_use_env_def)
  apply (rule_tac x="add_use_env (one_use_env x1 OwnPerm) x2 OwnPerm" in exI)
  apply (auto)
    apply (rule_tac mini_disj_diff_leq_use_env2)
     apply (simp)
    apply (simp add: mini_disj_use_env_def)
    apply (simp add: one_use_env_def)
    apply (simp add: add_use_env_def)
    apply (auto)
   apply (rule_tac add_leq_use_env)
    apply (simp add: leq_use_env_def)
    apply (simp add: one_use_env_def)
   apply (auto)
  apply (simp add: pair_req_def)
  apply (auto)
   apply (rule_tac leq_empty_use_env)
  apply (simp add: leq_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: is_own_def)
  done
    
lemma sacc_mk2_act_case: "
  \<lbrakk>well_typed_state s1 env delta; sub_use_env s1 r_f; well_typed env delta r_s1 v t1 r_s2 rx2;
                leq_use_env r_s3 (diff_use_env r_s2 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex));
                leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s2; leq_use_env r_ex r_s1; leq_use_env rx r_s3;
                leq_use_env (app_req rx1 rx2 r t2 r_ex) rx; leq_use_env r_s1 r_f; FunTy t1 t2 r a \<in> const_type c; c \<noteq> FixConst; ax = Mk2Act x31 x32;
                is_value v; app_con s1 c v (Mk2Act x31 x32) (s2, e2)\<rbrakk>
               \<Longrightarrow> \<exists>g_ax. well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) e2 t2 (end_red_use_env r_s3 g_ax) (end_red_use_env rx g_ax) \<and>
                          well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
                          sub_use_env s2 (exp_red_use_env r_f g_ax) \<and>
                          safe_act s1 (infl_use_env r_f r_s3) g_ax \<and> corr_act (Mk2Act x31 x32) g_ax"
  apply (case_tac c)
              apply (auto)
  apply (cut_tac eq_own)
  apply (auto)
  apply (rule_tac x="Add2ResAct x31 x32 tau" in exI)
  apply (auto)
       apply (cut_tac env="add_env (add_env env (Loc x31) (ChanTy tau SEnd)) (Loc x32) (ChanTy tau REnd)" and delta="add_delta (add_delta delta x31 x31) x32 x32" and
        ?r_s1.0="add_use_env (add_use_env r_s1 (Loc x31) OwnPerm) (Loc x32) OwnPerm" and
        ?r_s2.0="r_s3" and ?v1.0="VarExp (LocType x31)" and ?v2.0="VarExp (LocType x32)" and ?t1.0="ChanTy tau SEnd" and ?t2.0="ChanTy tau REnd"
        and ?x1.0="Loc x31" and ?x2.0="Loc x32" in saccmk2_pair_type)
                apply (rule_tac saccmk2_var_type)
                 apply (simp add: add_env_def)
                apply (simp add: add_delta_def)
               apply (rule_tac saccmk2_var_type)
                apply (simp add: add_env_def)
               apply (simp add: add_delta_def)
              apply (auto)
           apply (simp add: add_use_env_def)
          apply (simp add: add_use_env_def)
         apply (rule_tac r_s="r_f" in leq_use_none)
          apply (rule_tac r_sb="r_s1" in trans_leq_use_env)
           apply (simp)
          apply (rule_tac r_sb="diff_use_env r_s2 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
           apply (rule_tac diff_leq_use_env)
           apply (simp_all)
         apply (simp add: fresh_var_def)
         apply (simp add: sub_use_env_def)
         apply (auto)
        apply (rule_tac r_s="r_f" in leq_use_none)
         apply (rule_tac r_sb="r_s1" in trans_leq_use_env)
          apply (simp)
         apply (rule_tac r_sb="diff_use_env r_s2 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
          apply (rule_tac diff_leq_use_env)
          apply (simp_all)
        apply (simp add: fresh_var_def)
        apply (simp add: sub_use_env_def)
        apply (auto)
       apply (rule_tac rhs_add_leq_use_env)
        apply (rule_tac rhs_add_leq_use_env)
         apply (rule_tac r_sb="diff_use_env r_s2 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
          apply (rule_tac diff_leq_use_env)
          apply (simp_all)
      apply (rule_tac x="ChanTy tau REnd" in exI)
      apply (rule_tac x="ra" in exI)
      apply (auto)
       apply (simp add: pure_fun_def)
       apply (simp add: is_own_def)
      apply (rule_tac x="r_s2a" in exI)
      apply (rule_tac x="r_s3a" in exI)
      apply (rule_tac x="rx1a" in exI)
      apply (auto)
      apply (rule_tac x="rx2a" in exI)
      apply (auto)
      apply (rule_tac x="r_exb" in exI)
      apply (auto)
      apply (simp add: pure_fun_def)
      apply (simp add: is_own_def)
    (* proving the state remains well-typed: environment containment *)
     apply (simp add: well_typed_state_def)
     apply (auto)
       apply (rule_tac dist_add_sub_env)
       apply (rule_tac dist_add_sub_env)
       apply (simp)
    (* res_map validity: completeness *)(*
      apply (simp add: valid_nres_map_def)
      apply (auto)
        apply (rule_tac add_full_nres_map)
        apply (rule_tac add_full_nres_map)
        apply (simp)
    (* - disjointness *)
       apply (rule_tac disj_add_nres_map)
        apply (rule_tac disj_add_nres_map)
         apply (simp)
        apply (simp add: sep_nres_map_def)
        apply (simp add: empty_strong_disj_use_env1)
       apply (simp add: sep_nres_map_def)
       apply (simp add: empty_strong_disj_use_env1)
    (* - element containment *)
      apply (rule_tac dist_add_sub_nres_map)
       apply (rule_tac dist_add_sub_nres_map)
        apply (simp)
        apply (rule_tac empty_sub_use_env)
       apply (rule_tac empty_sub_use_env)*)
    (* proving delta remains proper *)
      apply (rule_tac add_proper_delta)
        apply (rule_tac add_proper_delta)
          apply (auto)(*
       apply (simp add: valid_nres_map_def)
       apply (auto)
         apply (rule_tac add_full_nres_map)
         apply (simp)
        apply (rule_tac disj_add_nres_map)
         apply (simp)
        apply (simp add: sep_nres_map_def)
        apply (simp add: empty_strong_disj_use_env1)
       apply (rule_tac dist_add_sub_nres_map)
        apply (simp)
       apply (rule_tac empty_sub_use_env)*)
      apply (simp add: add_env_def)
      apply (simp add: fresh_var_def)
    (* proving that the memory is still well-typed. starting with x = x31 / x = x32 *)
     apply (case_tac "x = x31")
      apply (simp add: add_env_def)
     apply (case_tac "x = x32")
      apply (simp add: add_env_def)
    (* - otherwise compare with the originals *)
     apply (simp add: add_env_def)
     apply (erule_tac x="x" in allE)
     apply (case_tac "s1 x")
      apply (auto)
     apply (simp add: add_env_def)
     apply (case_tac "env (Loc x)")
      apply (auto)
     apply (case_tac "add_delta (add_delta delta x31 x31) x32 x32 x \<noteq> delta x")
      apply (simp add: add_delta_def)
     apply (rule_tac well_typed_mv_add_vars)
      apply (rule_tac well_typed_mv_add_vars)
       apply (rule_tac well_typed_mv_add_delta)
        apply (rule_tac well_typed_mv_add_delta)
         apply (auto)
(*
         apply (simp add: nres_lookup_def)
         apply (simp add: add_env_def)*)
        apply (simp add: fresh_var_def)
        apply (simp add: sub_env_def)
        apply (auto)
       apply (simp add: fresh_var_def)
       apply (simp add: sub_env_def)
       apply (auto)
      apply (simp add: fresh_var_def)
      apply (simp add: sub_env_def)
      apply (auto)
     apply (simp add: add_env_def)
     apply (simp add: fresh_var_def)
     apply (simp add: sub_env_def)
     apply (auto)
    (* proving the new res_map is still valid: expression map containment *)(*
    apply (simp add: valid_exp_use_env_def)
    apply (auto)*)
    apply (rule_tac rhs_add_sub_use_env)
     apply (rule_tac rhs_add_sub_use_env)
      apply (rule_tac add_sub_use_env)
      apply (rule_tac add_sub_use_env)
      apply (simp)
     apply (simp add: add_env_def)
    apply (simp add: add_env_def)
   apply (simp add: fresh_var_def)
   apply (simp add: fresh_var_def)
  apply (simp add: corr_act_def)
  done

lemma max_aff_leq: "\<lbrakk> aff_leq a1 a3; aff_leq a2 a3 \<rbrakk> \<Longrightarrow> aff_leq (max_aff a1 a2) a3"    
  apply (case_tac a1)
    apply (auto)
   apply (case_tac a2)
     apply (auto)
  apply (case_tac a2)
    apply (auto)
  done
    
lemma well_typed_new_list: "well_typed_list env delta empty_use_env (new_arr_value n) tau"    
  apply (induct n)
   apply (auto)
  apply (rule_tac id_leq_use_env)
  done

    (* the idea is that if we added a permission, we required it to be a variable not already in the env, ie a variable free in e2.
      so then we can remove x by default. *)
    (* in general, this statement says that given a constant-application, the result can be typed with a certain env + perm set,
      so that the state remains well-typed relative to the env + global perm_map, and the env + perm set remains valid *)
lemma safe_app_con_case: "\<lbrakk> well_typed_state s1 env delta;
    app_red_exp ConstApp (s1, AppExp (ConstExp c) v) ax (s2, e2); sub_use_env s1 r_f;
    well_typed env delta r_s1 v t1 r_s2 rx2;
    leq_use_env r_s3 (diff_use_env r_s2 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex));
    leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s2; leq_use_env r_ex r_s1; disj_use_env rx1 (lift_use_env rx2 r);
    leq_use_env rx r_s3; leq_use_env (app_req rx1 rx2 r t2 r_ex) rx; leq_use_env r_s1 r_f;
    FunTy t1 t2 r a \<in> const_type c; c \<noteq> FixConst\<rbrakk>
       \<Longrightarrow> \<exists>g_ax . well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) e2 t2 (end_red_use_env r_s3 g_ax) (end_red_use_env rx g_ax) \<and>
                  well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
                  sub_use_env s2 (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s3) g_ax \<and> corr_act ax g_ax"
  apply (case_tac ax)
     apply (auto)
    (* no action cases *)
     apply (cut_tac ?r_s2.0="r_s2" and ?r_s1.0="r_s1" and env="env" in well_typed_perm_leq)
      apply (auto)
     apply (case_tac c)
                 apply (auto)
     apply (rule_tac sares_unpack_case)
                apply (auto)
     apply (simp add: upc_init_abbrev_def)
     apply (rule_tac x="r_s1" in exI)
     apply (auto)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac x="rx1" in exI)
     apply (auto)
      apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac self_comp_leq_use_env1)
     apply (rule_tac x="rx2" in exI)
     apply (rule_tac x="r_s2" in exI)
     apply (auto)
     apply (rule_tac x="r_s2a" in exI)
     apply (rule_tac x="r_s3a" in exI)
     apply (rule_tac x="rx1a" in exI)
     apply (auto)
    (* new resource cases. in all cases t2 should be the correct type to add *)
    apply (rule_tac x="AddResAct x2 t2" in exI)
    apply (auto)
    (* - lemma for main well-typedness statement *)
        apply (rule_tac ?s2.0="s2" and ?rx1.0="rx1" in sacc_make_act_case)
                 apply (auto)
        apply (rule_tac r_sb="diff_use_env r_s2 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
         apply (rule_tac lhs_unroll_dcl_use_env)
         apply (rule_tac self_diff_leq_use_env)
        apply (simp)
    (* - well typed state. *)
       apply (case_tac "\<not> (\<exists> v. s2 = add_env s1 x2 v)")
        apply (case_tac c)
                    apply (auto)
       apply (rule_tac well_typed_state_add_vars)
           apply (auto)
          apply (case_tac c)
                      apply (auto)
    (* - wt mem val: array case *)
         apply (case_tac c)
                     apply (auto)
         apply (cut_tac s="s1" and x="x2" and v="va" and w="ArrValue (new_arr_value (nat i))" in add_env_force)
        apply (auto)
       apply (rule_tac x="tau" in exI)
       apply (simp add: pure_fun_def)
       apply (rule_tac well_typed_new_list)
(*
    (* - valid res list *)
         apply (rule_tac x="\<lambda> x. None" in exI)
          apply (simp add: valid_res_list_def)
    (* - properness *)
         apply (case_tac c)
                     apply (auto)
         apply (cut_tac s="s1" and x="x2" and v="va" and w="ArrValue []" in add_env_force)
          apply (simp)
         apply (auto)*)
    (* - x22 is contained in rs_map (true because x22 is the empty set)
        apply (simp add: sub_use_env_def)
        apply (simp add: empty_use_env_def)
    (* - map separation + strength *)
       apply (simp add: sep_nres_map_def)
       apply (auto)
       apply (rule_tac empty_strong_disj_use_env1) *)
    (* - valid use env. *)
      apply (case_tac "\<not> (\<exists> v. s2 = add_env s1 x2 v)")
       apply (case_tac c)
                   apply (auto)
      apply (rule_tac rhs_add_sub_use_env)
       apply (rule_tac add_sub_use_env)
       apply (simp)
      apply (simp add: add_env_def)
      apply (case_tac c)
                 apply (auto)
     apply (simp add: fresh_var_def)
  apply (simp add: corr_act_def)
    (* dual new resource case. (basically only channel creation) *)
   apply (rule_tac sacc_mk2_act_case)
                apply (auto)
    (* resource usage case. (currently empty) *)
  apply (case_tac c)
              apply (auto)
(*
   apply (case_tac c)
                apply (auto)
  apply (case_tac c)
               apply (auto)*)
  done    

  
lemma well_typed_empty_state: "well_typed_state empty_env empty_env id"
  apply (simp add: well_typed_state_def)
  apply (auto)
    apply (simp add: sub_env_def)
    apply (simp add: empty_env_def)
   apply (simp add: proper_delta_def)
   apply (simp add: empty_env_def)
  apply (simp add: empty_env_def)
  done

  
fun state_vars where
  "state_vars s = { x | x. s x \<noteq> None }"
  
definition fv_restr_env where
  "fv_restr_env e s = (\<lambda> x. if x \<in> free_vars e then s x else None)"
  
lemma fv_restr_env_use: "\<lbrakk> x \<in> free_vars e \<rbrakk> \<Longrightarrow> fv_restr_env e s x = s x"  
  apply (simp add: fv_restr_env_def)
  done
    
lemma dist_rem_contain_env: "\<lbrakk> contain_env s s' \<rbrakk> \<Longrightarrow> contain_env (rem_env s x) (rem_env s' x)"    
  apply (simp add: contain_env_def)
  apply (simp add: rem_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (case_tac "s' xa")
   apply (auto)
  apply (simp add: rem_env_def)
  done

lemma fv_contain_env: "\<lbrakk> free_vars e' \<subseteq> free_vars e \<rbrakk> \<Longrightarrow> contain_env (fv_restr_env e s) (fv_restr_env e' s)"    
  apply (simp add: contain_env_def)
  apply (simp add: fv_restr_env_def)
  apply (auto)
  apply (case_tac "s x")
   apply (auto)
  apply (simp add: fv_restr_env_def)
  apply (auto)
  done

lemma rem_fv_contain_env: "\<lbrakk> free_vars e' - {x} \<subseteq> free_vars e \<rbrakk> \<Longrightarrow> contain_env (fv_restr_env e (rem_env s x)) (fv_restr_env e' (rem_env s x))"    
  apply (simp add: contain_env_def)
  apply (simp add: fv_restr_env_def)
  apply (auto)
  apply (simp add: rem_env_def)
  apply (auto)
  apply (case_tac "s xa")
   apply (auto)
  apply (simp add: fv_restr_env_def)
  apply (simp add: rem_env_def)
  apply (auto)
  done
    
lemma rem_fv_restr_env: "rem_env (fv_restr_env e s) x = fv_restr_env e (rem_env s x)"    
  apply (case_tac "\<not> (\<forall> y. rem_env (fv_restr_env e s) x y = fv_restr_env e (rem_env s x) y)")
   apply (auto)
  apply (simp add: rem_env_def)
  apply (simp add: fv_restr_env_def)
  apply (case_tac "x = y")
   apply (auto)
   apply (case_tac "x \<in> free_vars e")
    apply (auto)
  apply (simp add: fv_restr_env_def)
  apply (case_tac "y \<in> free_vars e")
   apply (auto)
  done

    
    (* the question is, how do we allow for replicable pairs while enforcing full resource disjointness?
        i guess the "natural" way to do it based on what we already have is to simply allow pairs that contain
        values that are not unique to also be values.

        - if x is in the end perms, x is in the reqs. if r is own, (lift rx r) subtracts it out.
        - if r is not own, it means that e is replicable, in which case it is again not a var,
        - x is not in the end perms, which is trivial

        an even cleaner solution is to make a "replicable" pair value and type accordingly.
        in this case e is still a var, however at the level of reduction semantics, we can keep
        the var out of the name set.
     *)
    
end