theory WellTypedAlt
  imports WTLemma
begin
  
datatype wta_tag =
  ConstRule
  | OpRule
  | VarRule
  | PairRule wta_tag wta_tag
  | IfRule wta_tag wta_tag wta_tag
  | LamRule wta_tag
  | AppRule wta_tag wta_tag
  | WeakPostRule wta_tag
  | StrReqRule wta_tag
  | WeakReqRule wta_tag
    
fun well_typed_alt :: "wta_tag \<Rightarrow> pt_env \<Rightarrow> owner_env \<Rightarrow> perm_use_env \<Rightarrow> p_exp \<Rightarrow> p_type \<Rightarrow> perm_use_env \<Rightarrow> perm_use_env \<Rightarrow> bool" where
  "well_typed_alt ConstRule env delta r_s1 e tau r_s2 rx = (\<exists> c. e = ConstExp c \<and> tau \<in> const_type c \<and> r_s2 = r_s1 \<and> rx = empty_use_env)"
| "well_typed_alt OpRule env delta r_s1 e tau r_s2 rx = (\<exists> xop. e = OpExp xop \<and> tau = op_type xop \<and> r_s2 = r_s1 \<and> rx = empty_use_env)"
| "well_typed_alt VarRule env delta r_s1 e tau r_s2 rx = (\<exists> v tau_x. e = VarExp v \<and> env (res_name v) = Some tau \<and>
    env (owner_name delta v) = Some tau_x \<and> leq_use_env (ereq_use_env (owner_name delta v) tau_x) r_s1 \<and> r_s2 = diff_use_env r_s1 (ereq_use_env (owner_name delta v) tau_x) \<and>
    rx = diff_use_env (ereq_use_env (owner_name delta v) tau_x) (ereq_use_env (owner_name delta v) tau_x))"
| "well_typed_alt (PairRule w1 w2) env delta r_s1 e tau r_s3 rf = (\<exists> e1 e2 t1 t2 r r_s2 rx1 rx2. e = PairExp e1 e2 \<and>
    tau = PairTy t1 t2 r \<and> well_typed_alt w1 env delta r_s1 e1 t1 r_s2 rx1 \<and> well_typed_alt w2 env delta r_s2 e2 t2 r_s3 rx2 \<and>
    leq_use_env (lift_use_env rx1 r) r_s3 \<and> leq_use_env (lift_use_env rx2 r) r_s3 \<and> aff_leq (max_aff (req_type t1) (req_type t2)) r \<and>
    disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r) \<and>
    rf = pair_req (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) empty_use_env tau
  )"  
| "well_typed_alt (IfRule w1 w2 w3) env delta r_s1 e tau r_s3 rx = (\<exists> e1 e2 e3 rx' r_s2 rx1 rx2. e = IfExp e1 e2 e3 \<and>
    well_typed_alt w1 env delta r_s1 e1 BoolTy r_s2 rx' \<and> well_typed_alt w2 env delta r_s2 e2 tau r_s3 rx1 \<and> well_typed_alt w3 env delta r_s2 e3 tau r_s3 rx2 \<and>
    rx = comp_use_env rx1 rx2)"
| "well_typed_alt (LamRule w) env delta r_s1 ex tau r_s2 rx = (\<exists> x e t1 t2 r a r_end r_s'. ex = LamExp x e \<and>
    tau = FunTy t1 t2 r a \<and>
    well_typed_alt w (add_env env (Var x) t1) delta (add_use_env rx (Var x) r) e t2 r_s' r_end \<and> aff_use_env rx a \<and>
    leq_use_env rx r_s1 \<and> r_s2 = r_s1)"
| "well_typed_alt (AppRule w1 w2) env delta r_s1 e tau r_sf rx = (\<exists> e1 e2 t1 r a r_s2 rx1 rx2 r_s3. e = AppExp e1 e2 \<and>
    well_typed_alt w1 env delta r_s1 e1 (FunTy t1 tau r a) r_s2 rx1 \<and> well_typed_alt w2 env delta r_s2 e2 t1 r_s3 rx2 \<and>
    r_sf = diff_use_env r_s3 (comp_use_env rx1 (lift_use_env rx2 r)) \<and> (*r \<noteq> NoPerm \<and>*) (*safe_use_lift rx2 r \<and>
    safe_type t1 r \<and>*) leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3 \<and>
    disj_use_env rx1 (lift_use_env rx2 r) \<and> leq_use_env rx r_sf \<and> 
    rx = app_req rx1 rx2 r tau empty_use_env
  )"
| "well_typed_alt (WeakPostRule tag) env delta r_s1 e tau r_s2 rx = (\<exists> r_c. well_typed_alt tag env delta r_s1 e tau r_c rx \<and>
    leq_use_env rx r_s2 \<and> leq_use_env r_s2 r_c)"
| "well_typed_alt (StrReqRule tag) env delta r_s1 e tau r_s2 rx = (\<exists> rx'. well_typed_alt tag env delta r_s1 e tau r_s2 rx' \<and>
    leq_use_env rx' rx \<and> leq_use_env rx r_s2)"
| "well_typed_alt (WeakReqRule tag) env delta r_s1 e tau r_s2 rx = (\<exists> r_se r_xe r_ex. well_typed_alt tag env delta r_s1 e tau r_se r_xe \<and>
    r_s2 = diff_use_env r_se r_ex \<and> rx = diff_use_env r_xe r_ex \<and> leq_use_env r_ex r_s1)"
  
  
lemma well_typed_equiv1: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx \<rbrakk> \<Longrightarrow> (\<exists> tag. well_typed_alt tag env delta r_s1 e tau r_s2 rx)"  
  apply (induct e arbitrary: env r_s1 r_s2 tau rx)
        apply (auto)
    (* const case *)
        apply (rule_tac x="StrReqRule (WeakPostRule ConstRule)" in exI)
        apply (auto)
         apply (rule_tac leq_empty_use_env)
        apply (rule_tac leq_empty_use_env)
    (* op case *)
       apply (rule_tac x="StrReqRule (WeakPostRule OpRule)" in exI)
       apply (auto)
        apply (rule_tac leq_empty_use_env)
       apply (rule_tac leq_empty_use_env)
    (* var case *)
      apply (rule_tac x="WeakPostRule (StrReqRule (WeakReqRule VarRule))" in exI)
      apply (auto)
      apply (rule_tac x="diff_use_env (diff_use_env r_s1 (ereq_use_env (owner_name delta x) tau_x)) r_ex" in exI)
      apply (auto)
       apply (rule_tac x="diff_use_env (diff_use_env (ereq_use_env (owner_name delta x) tau_x) (ereq_use_env (owner_name delta x) tau_x)) r_ex" in exI)
       apply (auto)
        apply (rule_tac lhs_fold_dcl_use_env)
        apply (simp)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (rule_tac rhs_fold_dcl_use_env)
        apply (simp_all)
      apply (rule_tac rhs_fold_dcl_use_env)
      apply (simp)
    (* pair case *)
     apply (case_tac "\<exists>tag. well_typed_alt tag env delta r_s1 e1 t1 r_s2a rx1")
      apply (erule_tac exE)
      apply (auto)
     apply (case_tac "\<exists>tag. well_typed_alt tag env delta r_s2a e2 t2 r_s3 rx2")
      apply (erule_tac exE)
      apply (auto)
     apply (rule_tac x="WeakPostRule (StrReqRule (WeakReqRule (PairRule tag taga)))" in exI)
     apply (auto)
     apply (rule_tac x="diff_use_env r_s3 r_ex" in exI)
     apply (auto)
     apply (rule_tac x="pair_req (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex (PairTy t1 t2 r)" in exI)
     apply (auto)
      apply (rule_tac x="r_s3" in exI)
      apply (rule_tac x="pair_req (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) empty_use_env (PairTy t1 t2 r)" in exI)
      apply (auto)
      apply (rule_tac x="r_ex" in exI)
      apply (auto)
      apply (simp add: pair_req_def)
      apply (auto)
       apply (simp add: diff_empty_use_env1)
      apply (simp add: diff_empty_use_env2)
     apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
      apply (auto)
    (* if case *)
     apply (case_tac "\<exists>tag. well_typed_alt tag env delta r_s1 e1 BoolTy r_s2a rx'")
      apply (erule_tac exE)
      apply (auto)
     apply (case_tac "\<exists>tag. well_typed_alt tag env delta r_s2a e2 tau r_s2 rx1")
      apply (erule_tac exE)
      apply (auto)
     apply (case_tac "\<exists>tag. well_typed_alt tag env delta r_s2a e3 tau r_s2 rx2")
      apply (erule_tac exE)
      apply (auto)
    apply (rule_tac x="IfRule tag taga tagb" in exI)
    apply (auto)
    (* lam case *)
   apply (case_tac "\<exists>tag. well_typed_alt tag (add_env env (Var x1a) t1) delta (add_use_env rxa (Var x1a) r) e t2 r_s' r_end")
    apply (erule_tac exE)
    apply (auto)
   apply (rule_tac x="WeakPostRule (StrReqRule (WeakReqRule (LamRule tag)))" in exI)
   apply (auto)
   apply (rule_tac x="diff_use_env r_s1 r_ex" in exI)
   apply (auto)
   apply (rule_tac x="diff_use_env rxa r_ex" in exI)
   apply (auto)
   apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
    apply (auto)
    (* app case *)
  apply (case_tac "\<exists>tag. well_typed_alt tag env delta r_s1 e1 (FunTy t1 tau r a) r_s2a rx1")
   apply (erule_tac exE)
   apply (auto)
  apply (case_tac "\<exists>tag. well_typed_alt tag env delta r_s2a e2 t1 r_s3 rx2")
   apply (erule_tac exE)
   apply (auto)
  apply (rule_tac x="WeakPostRule (StrReqRule (WeakReqRule (AppRule tag taga)))" in exI)
  apply (auto)
  apply (rule_tac x="diff_use_env (diff_use_env r_s3 (comp_use_env rx1 (lift_use_env rx2 r))) r_ex" in exI)
  apply (auto)
   apply (rule_tac x="app_req rx1 rx2 r tau r_ex" in exI)
   apply (auto)
    apply (rule_tac x="diff_use_env r_s3 (comp_use_env rx1 (lift_use_env rx2 r))" in exI)
    apply (rule_tac x="app_req rx1 rx2 r tau empty_use_env" in exI)
    apply (auto)
     apply (rule_tac x="t1" in exI)
     apply (rule_tac x="r" in exI)
     apply (rule_tac x="a" in exI)
     apply (rule_tac x="r_s2a" in exI)
     apply (rule_tac x="rx1" in exI)
     apply (auto)
     apply (rule_tac x="rx2" in exI)
     apply (rule_tac x="r_s3" in exI)
     apply (auto)
     apply (simp add: app_req_def)
     apply (auto)
      apply (rule_tac leq_empty_use_env)
     apply (rule_tac dist_diff_leq_use_env_gen)
      apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac self_comp_leq_use_env1)
      apply (rule_tac comp_leq_use_env2)
      apply (rule_tac self_lift_leq_use_env)
     apply (rule_tac self_comp_leq_use_env1)
    apply (rule_tac x="r_ex" in exI)
    apply (auto)
    apply (simp add: app_req_def)
    apply (auto)
     apply (simp add: diff_empty_use_env1)
    apply (simp add: comp_empty_use_env2)
    apply (simp add: diff_comp_use_env)
   apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
    apply (rule_tac rhs_fold_dcl_use_env)
    apply (simp_all)
  apply (rule_tac rhs_fold_dcl_use_env)
  apply (simp)
  done
   
lemma well_typed_equiv2: "\<lbrakk> well_typed_alt tag env delta r_s1 e tau r_s2 rx \<rbrakk> \<Longrightarrow> well_typed env delta r_s1 e tau r_s2 rx"      
  apply (induct tag arbitrary: env r_s1 e tau r_s2 rx)  
           apply (auto)
    (* const + op case *)
             apply (rule_tac id_leq_use_env)
            apply (rule_tac leq_empty_use_env)
           apply (rule_tac id_leq_use_env)
          apply (rule_tac leq_empty_use_env)
    (* var case *)
         apply (rule_tac x="empty_use_env" in exI)
         apply (auto)
           apply (rule_tac dist_diff_leq_use_env_gen)
            apply (rule_tac id_leq_use_env)
           apply (rule_tac dist_comp_leq_use_env)
            apply (rule_tac id_leq_use_env)
           apply (rule_tac leq_empty_use_env)
          apply (rule_tac dist_diff_leq_use_env_gen)
           apply (simp)
          apply (rule_tac id_leq_use_env)
         apply (rule_tac leq_empty_use_env)
        apply (rule_tac dist_diff_leq_use_env_gen)
         apply (rule_tac id_leq_use_env)
        apply (rule_tac self_comp_leq_use_env1)
    (* pair case *)
       apply (rule_tac x="r_s2a" in exI)
       apply (rule_tac x="r_s2" in exI)
       apply (rule_tac x="rx1" in exI)
       apply (auto)
       apply (rule_tac x="rx2" in exI)
       apply (auto)
       apply (rule_tac x="empty_use_env" in exI)
       apply (auto)
          apply (simp add: diff_empty_use_env2)
          apply (rule_tac id_leq_use_env)
         apply (simp add: pair_req_def)
         apply (auto)
          apply (rule_tac leq_empty_use_env)
         apply (rule_tac diff_leq_use_env)
         apply (rule_tac dist_comp_leq_use_env)
          apply (simp_all)
        apply (rule_tac leq_empty_use_env)
       apply (simp add: pair_req_def)
       apply (auto)
        apply (rule_tac leq_empty_use_env)
        apply (rule_tac id_leq_use_env)
    (* if case *)
      apply (rule_tac x="rx'" in exI)
      apply (rule_tac x="r_s2a" in exI)
       apply (auto)
       apply (rule_tac x="rx1" in exI)
       apply (auto)
       apply (rule_tac x="rx2" in exI)
       apply (auto)
    (* lam case *)
      apply (rule_tac x="rx" in exI)
      apply (auto)
       apply (rule_tac x="r_end" in exI)
       apply (rule_tac x="r_s'" in exI)
       apply (auto)
      apply (rule_tac x="empty_use_env" in exI)
      apply (auto)
         apply (simp add: diff_empty_use_env2)
         apply (rule_tac id_leq_use_env)
       apply (rule_tac leq_empty_use_env)
      apply (rule_tac self_diff_leq_use_env)
    (* app case *)
     apply (rule_tac x="t1" in exI)
     apply (rule_tac x="r" in exI)
     apply (rule_tac x="a" in exI)
     apply (rule_tac x="r_s2a" in exI)
     apply (rule_tac x="rx1" in exI)
     apply (auto)
     apply (rule_tac x="rx2" in exI)
     apply (rule_tac x="r_s3" in exI)
     apply (auto)
     apply (rule_tac x="empty_use_env" in exI)
     apply (auto)
       apply (rule_tac dist_diff_leq_use_env_gen)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac leq_empty_use_env)
      apply (rule_tac leq_empty_use_env)
     apply (rule_tac id_leq_use_env)
    (* post weakening case *)
    apply (rule_tac r_c="r_c" in well_typed_decr_end_perm)
      apply (auto)
    (* req strengthening case *)
   apply (rule_tac rx="rx'" in well_typed_incr_req)
     apply (auto)
    (* req weakening case *)
  apply (rule_tac well_typed_diff_end_perm)
   apply (auto)
  done

end