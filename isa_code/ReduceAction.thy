theory ReduceAction
  imports ReduceProper ReduceWTS
begin
  
  (* ###### constructive permission definitions.
      the idea here is that i want to constructively state which permissions are being consumed.
      the difficult part is that because the "permissions consumed" involves 
  *)
    
datatype gen_act =
  NoResAct
  | AddResAct string p_type (*perm_use_env*)
  | Add2ResAct string string p_type
  | ReadResAct
  | WriteResAct string perm_use_env
    
fun red_env :: "pt_env \<Rightarrow> gen_act \<Rightarrow> pt_env" where
  "red_env env NoResAct = env"
| "red_env env (AddResAct x tau) = add_env env (Loc x) tau"
| "red_env env (Add2ResAct x1 x2 tau) = add_env (add_env env (Loc x1) (ChanTy tau SEnd)) (Loc x2) (ChanTy tau REnd)"
| "red_env env ReadResAct = env"
| "red_env env (WriteResAct x r_s) = env"
  
fun red_delta :: "owner_env \<Rightarrow> gen_act \<Rightarrow> owner_env" where
  "red_delta delta (WriteResAct x r_s) = ext_delta delta (delta x) r_s"
| "red_delta delta (AddResAct x tau) = add_delta delta x x"
| "red_delta delta (Add2ResAct x1 x2 tau) = add_delta (add_delta delta x1 x1) x2 x2"
| "red_delta delta r_ax = delta"
  
fun exp_red_use_env where
  "exp_red_use_env r_s NoResAct = r_s"
  (* remove resources used to create the value, add the new perm *)
| "exp_red_use_env r_s (AddResAct x tau) = add_use_env r_s (Loc x) OwnPerm"
| "exp_red_use_env r_s (Add2ResAct x1 x2 tau) = add_use_env (add_use_env r_s (Loc x1) OwnPerm) (Loc x2) OwnPerm"
| "exp_red_use_env r_s ReadResAct = r_s"  
| "exp_red_use_env r_s (WriteResAct x r_s') = (diff_use_env r_s r_s')"
  
fun end_red_use_env where  
  "end_red_use_env r_s (WriteResAct x r_s') = (diff_use_env r_s r_s')"
| "end_red_use_env r_s r_ax = r_s"
  (*
fun red_nres_map :: "nres_map \<Rightarrow> gen_act \<Rightarrow> nres_map" where
  "red_nres_map rs_map NoResAct = rs_map"  
| "red_nres_map rs_map (AddResAct x tau r_s) = add_env rs_map x r_s"
| "red_nres_map rs_map (Add2ResAct x1 x2 tau) = add_env (add_env rs_map x1 empty_use_env) x2 empty_use_env"
| "red_nres_map rs_map ReadResAct = rs_map"
| "red_nres_map rs_map (WriteResAct x r_s) = add_env rs_map x (comp_use_env (nres_lookup rs_map x) r_s)"
  *)
  
  (*
fun safe_act where
  "safe_act s r_s NoResAct = True"
| "safe_act s r_s (AddResAct x tau r_x) = (s x = None \<and> leq_use_env r_x r_s)"
| "safe_act s r_s (Add2ResAct x1 x2 tau) = (s x1 = None \<and> s x2 = None \<and> x1 \<noteq> x2)"
| "safe_act s r_s ReadResAct = True"
| "safe_act s r_s (WriteResAct x r_x) = (s x \<noteq> None \<and> leq_use_env r_x r_s)"
  
fun corr_act where
  "corr_act ax NoResAct = (ax = NoAct)"
| "corr_act ax (AddResAct x tau r_s) = (ax = MakeAct x)"
| "corr_act ax (Add2ResAct x1 x2 tau) = (ax = Mk2Act x1 x2)"
| "corr_act ax ReadResAct = (\<exists> x. ax = UseAct x)"
| "corr_act ax (WriteResAct x r_s) = (\<exists> x. ax = UseAct x)"  
  *)
  
fun safe_act where
  "safe_act s r_s NoResAct = True"
| "safe_act s r_s (AddResAct x tau) = (s x = None)"
| "safe_act s r_s (Add2ResAct x1 x2 tau) = (s x1 = None \<and> s x2 = None \<and> x1 \<noteq> x2)"
| "safe_act s r_s ReadResAct = True"
| "safe_act s r_s (WriteResAct x r_x) = (s x \<noteq> None \<and> leq_use_env r_x r_s)"
  
definition corr_act where
  "corr_act ax g_ax = True"    
  
lemma leq_safe_act: "\<lbrakk> safe_act s r_x g_ax; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> safe_act s r_s g_ax"    
  apply (case_tac g_ax)
      apply (auto)
   apply (rule_tac r_sb="r_x" in trans_leq_use_env)
    apply (auto)
  done  
  
  
definition valid_reduct where
  "valid_reduct r_exp = (\<forall> are s1 env delta r_f r_s1 e1 tau r_s2 rx ax s2 e2. (
    r_exp are (s1, e1) ax (s2, e2) \<and> well_typed env delta r_s1 e1 tau r_s2 rx \<and>
    well_typed_state s1 env delta \<and> (*valid_exp_use_env s1 r_f \<and> *) sub_use_env s1 r_f \<and> leq_use_env r_s1 r_f) \<longrightarrow>
    (\<exists> g_ax. well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) e2 tau (end_red_use_env r_s2 g_ax) (end_red_use_env rx g_ax) \<and>
      well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
      (*valid_exp_use_env s2 (exp_red_use_env r_f g_ax)*) sub_use_env s2 (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax)
  )"  
  

lemma red_contain_env: "\<lbrakk> safe_act s r_s g_ax; sub_env s env \<rbrakk> \<Longrightarrow> contain_env (red_env env g_ax) env"
  apply (case_tac g_ax)
      apply (auto)
      apply (rule_tac id_contain_env)
     apply (rule_tac add_contain_env)
     apply (simp add: sub_env_def)
     apply (erule_tac x="Loc x21" in allE)
     apply (auto)
    apply (rule_tac env_b="add_env env (Loc x31) (ChanTy x33 SEnd)" in trans_contain_env)
     apply (rule_tac add_contain_env)
     apply (simp add: add_env_def)
     apply (case_tac "env (Loc x32)")
      apply (auto)
     apply (simp add: sub_env_def)
     apply (erule_tac x="Loc x32" in allE)
     apply (auto)
    apply (rule_tac add_contain_env)
    apply (case_tac "env (Loc x31)")
     apply (auto)
    apply (simp add: sub_env_def)
    apply (erule_tac x="Loc x31" in allE)
    apply (auto)
   apply (rule_tac id_contain_env)
  apply (rule_tac id_contain_env)
  done
    
    (* ##### safe-reduction specific validity lemmas ##### *)

lemma red_sep_nres_map: "\<lbrakk> p_map u = Some r_s; disj_nres_map p_map; sub_nres_map s1 p_map;
  safe_act s1 r_s g_ax; sub_use_env s1 r_s \<rbrakk> \<Longrightarrow> sep_nres_map (exp_red_use_env r_s g_ax) (rem_env p_map u)"
  apply (simp add: sep_nres_map_def)
  apply (auto)
    (* we dont have to check x = u, since u has been removed from the map *)
  apply (case_tac "u = x")
   apply (auto)
   apply (simp add: nres_lookup_def)
   apply (simp add: rem_env_def)
   apply (rule_tac empty_strong_disj_use_env2)
    (* otherwise, the lookup is the same as it was in p_map *)
  apply (cut_tac rs_map="p_map" and x="u" and y="x" in nres_rem_diff)
   apply (auto)
    (* from here we do case analysis on the possible ways that r_s has been modified *)
    (* if it has not been modified the case is simple *)
  apply (case_tac "exp_red_use_env r_s g_ax = r_s")
   apply (simp add: disj_nres_map_def)
   apply (erule_tac x="u" in allE)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (simp add: nres_lookup_def)
    (* make case: if x21 has been added, the rest of r_s is disjoint from p_map x *)
  apply (case_tac g_ax)
     apply (auto)
    apply (rule_tac add_strong_disj_use_env)
     apply (simp add: disj_nres_map_def)
     apply (erule_tac x="u" in allE)
     apply (erule_tac x="x" in allE)
     apply (auto)
     apply (simp add: nres_lookup_def)
    (* now we have to prove that x21 was not in p_map, which should be true since p_map is sub-ordinate to s *)
    apply (case_tac "p_map x")
     apply (simp add: nres_lookup_def)
     apply (simp add: empty_use_env_def)
    apply (simp add: sub_nres_map_def)
    apply (erule_tac x="x" in allE)
    apply (simp add: sub_use_env_def)
    apply (erule_tac x="Loc x21" in allE)
    apply (auto)
    (* make 2 case: start by assuming we have p_map x *)
   apply (case_tac "p_map x")
    apply (simp add: nres_lookup_def)
    apply (rule_tac empty_strong_disj_use_env2)
    (* otherwise, prove r_s disjoint from p_map x *)
   apply (rule_tac add_strong_disj_use_env)
    apply (rule_tac add_strong_disj_use_env)
     apply (simp add: disj_nres_map_def)
     apply (erule_tac x="u" in allE)
     apply (erule_tac x="x" in allE)
     apply (auto)
     apply (simp add: nres_lookup_def)
    (* after this, prove x31 / x32 do not appear in p_map x *)
    apply (simp add: sub_nres_map_def)
    apply (erule_tac x="x" in allE)
    apply (simp add: sub_use_env_def)
    apply (erule_tac x="Loc x31" in allE)
    apply (auto)
   apply (simp add: sub_nres_map_def)
   apply (erule_tac x="x" in allE)
   apply (simp add: sub_use_env_def)
   apply (erule_tac x="Loc x32" in allE)
    apply (auto)
    (* write case: otherwise, x42 was removed from r_s, so disjointness should be simple *)
  apply (rule_tac r_s="r_s" in strong_disj_leq_use_env1)
   apply (simp add: disj_nres_map_def)
   apply (erule_tac x="u" in allE)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (simp add: nres_lookup_def)
  apply (rule_tac self_diff_leq_use_env)
  done
  
(*
lemma red_sep_nres_map2: "\<lbrakk> p_map v = Some r_p; p_map u = Some r_s; u \<noteq> v; disj_nres_map p_map;
  safe_act s1 r_s g_ax; sep_nres_map r_p rs_map \<rbrakk> \<Longrightarrow> sep_nres_map r_p (red_nres_map rs_map g_ax)"    
  apply (case_tac g_ax)
      apply (auto)
    (* make case *)
    apply (rule_tac add_sep_nres_map)
     apply (simp)
    apply (rule_tac r_s="r_s" in strong_disj_leq_use_env2)
     apply (simp add: disj_nres_map_def)
     apply (auto)
    apply (erule_tac x="v" in allE)
    apply (erule_tac x="u" in allE)
    apply (simp add: nres_lookup_def)
    (* make 2 case *)
   apply (rule_tac add_sep_nres_map)
    apply (rule_tac add_sep_nres_map)
     apply (simp)
    apply (rule_tac empty_strong_disj_use_env2)
   apply (rule_tac empty_strong_disj_use_env2)
    (* write case *)
  apply (rule_tac add_sep_nres_map)
   apply (simp)
  apply (rule_tac strong_disj_comp_use_env1)
   apply (simp add: sep_nres_map_def)
  apply (rule_tac r_s="r_s" in strong_disj_leq_use_env2)
   apply (simp add: disj_nres_map_def)
   apply (erule_tac x="v" in allE)
   apply (erule_tac x="u" in allE)
   apply (simp add: nres_lookup_def)
  apply (simp)
  done    *)
    
    
definition loc_use_env where
  "loc_use_env r_s = (\<forall> x. case x of
    Var x \<Rightarrow> r_s (Var x) = NoPerm
    | Loc y \<Rightarrow> True
  )"
    
lemma wtedi_strong_disj_use_env: "\<lbrakk> strong_disj_use_env r_s r_ex; leq_use_env r_x r_s; loc_use_env r_ex \<rbrakk> \<Longrightarrow> strong_disj_use_env (add_use_env r_x (Var x) r) r_ex"  
  apply (rule_tac r_s="add_use_env r_s (Var x) r" in strong_disj_leq_use_env1)
   apply (simp add: strong_disj_use_env_def)
   apply (simp add: add_use_env_def)
   apply (auto)
   apply (simp add: loc_use_env_def)
   apply (erule_tac x="Var x" in allE)
   apply (erule_tac x="Var x" in allE)
   apply (auto)
  apply (rule_tac dist_add_leq_use_env)
  apply (simp)
  done    
    (*
lemma wtedx_adjust: "\<lbrakk> well_typed env delta r_s e1 t1 r_s2 rx1; well_typed env delta r_s2 e2 t2 r_s3 rx2; leq_use_env r_s (diff_use_env r_s3 r_ex) \<rbrakk> \<Longrightarrow>
  well_typed env delta r_s e1 t1 r_s rx1 \<and> well_typed env delta r_s e2 t2 r_s rx2"
  apply (auto)
   apply (rule_tac r_c="r_s2" in well_typed_decr_end_perm)
     apply (simp)
    apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
     apply (rule_tac diff_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
   apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac well_typed_perm_leqx)
   apply (auto)
  apply (rule_tac r_c="r_s3" in well_typed_decr_end_perm)
    apply (rule_tac ?r_s1.0="r_s2" in well_typed_incr_start_perm)
     apply (simp)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
    apply (rule_tac self_diff_leq_use_env)
   apply (simp)
  apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
   apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  apply (rule_tac well_typed_perm_leqx)
  apply (auto)
  done
    
    
  
lemma well_typed_ext_deltax: "\<lbrakk> well_typed env delta r_s e tau r_s r_x; strong_disj_use_env r_x r_ex; mem_val_env env; loc_use_env r_ex \<rbrakk> \<Longrightarrow>
  well_typed env (ext_delta delta x r_ex) r_s e tau r_s r_x"
  apply (induct e arbitrary: env r_s tau r_x)
        apply (auto)
    (* var case *)
      apply (case_tac "owner_name (ext_delta delta x r_ex) xa \<noteq> owner_name delta xa")
       apply (case_tac xa)
        apply (auto)
      apply (case_tac "req_type tau_x \<noteq> Ref")
       apply (simp add: mem_val_env_def)
       apply (erule_tac x="Loc (delta x2)" in allE)
       apply (auto)
       apply (case_tac tau_x)
             apply (auto)
      apply (case_tac "r_x (Loc (delta x2)) = NoPerm")
       apply (case_tac "comp_use_env (ereq_use_env (Loc (delta x2)) tau_x) r_exa (Loc (delta x2)) = OwnPerm")
        apply (cut_tac r_s="r_s" and r_x="comp_use_env (ereq_use_env (Loc (delta x2)) tau_x) r_exa" in self_diff_weak_use_env)
          apply (simp)
         apply (rule_tac dist_comp_leq_use_env)
          apply (auto)
        apply (simp add: weak_use_env_def)
       apply (cut_tac r_x="diff_use_env (ereq_use_env (Loc (delta x2)) tau_x) (comp_use_env (ereq_use_env (Loc (delta x2)) tau_x) r_exa)" and r_s="r_x" and x="Loc (delta x2)" in leq_use_none)
         apply (simp_all)
       apply (cut_tac r_s="ereq_use_env (Loc (delta x2)) tau_x" and r_x="comp_use_env (ereq_use_env (Loc (delta x2)) tau_x) r_exa" and x="Loc (delta x2)" in diff_use_eq)
        apply (auto)
       apply (simp add: ereq_use_env_def)
       apply (simp add: one_use_env_def)
       apply (simp add: end_req_perm_def)
      apply (simp add: strong_disj_use_env_def)
      apply (simp add: ext_delta_def)
      apply (auto)
    (* pair case *)
     apply (cut_tac env="env" and r_s="r_s" and ?e1.0="e1" and ?e2.0="e2" in wtedx_adjust)
        apply (auto)
     apply (rule_tac x="r_s" in exI)
     apply (rule_tac x="r_s" in exI)
     apply (rule_tac x="rx1" in exI)
     apply (auto)
     apply (rule_tac x="rx2" in exI)
     apply (auto)
     apply (cut_tac r_x="r_s2a" and r_s="r_s1" and r_ex="r_x" in strong_disj_leq_use_env1)
       apply (auto)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    (* if case *)
    apply (rule_tac x="rx'" in exI)
    apply (rule_tac x="r_s2a" in exI)
    apply (cut_tac r_x="r_s2a" and r_s="r_s1" and r_ex="r_x" in strong_disj_leq_use_env1)
      apply (auto)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (rule_tac x="rx1" in exI)
    apply (auto)
    apply (rule_tac x="rx2" in exI)
    apply (auto)
    (* lam case *)
   apply (rule_tac x="rxa" in exI)
   apply (auto)
   apply (rule_tac x="r_end" in exI)
   apply (rule_tac x="r_s'" in exI)
   apply (cut_tac r_x="rxa" and x="x1a" and r="r" and r_ex="r_x" and r_s="r_s1" in wtedi_strong_disj_use_env)
      apply (auto)
   apply (case_tac "\<not> mem_val_env (add_env env (Var x1a) t1)")
    apply (simp add: mem_val_env_def)
    apply (simp add: add_env_def)
   apply (auto)
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
  apply (cut_tac r_x="r_s2a" and r_s="r_s1" and r_ex="r_x" in strong_disj_leq_use_env1)
    apply (auto)
  apply (rule_tac well_typed_perm_leq)
  apply (auto)
  done    *)
    
lemma well_typed_ext_delta_ih: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; strong_disj_use_env r_s1 r_x; mem_val_env env; loc_use_env r_x \<rbrakk> \<Longrightarrow>
  well_typed env (ext_delta delta x r_x) r_s1 e tau r_s2 rx"
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
    (* var case *)
      apply (case_tac "owner_name (ext_delta delta x r_x) xa \<noteq> owner_name delta xa")
       apply (case_tac xa)
        apply (auto)
      apply (case_tac "req_type tau_x \<noteq> Ref")
       apply (simp add: mem_val_env_def)
       apply (erule_tac x="Loc (delta x2)" in allE)
       apply (auto)
       apply (case_tac tau_x)
             apply (auto)
      apply (case_tac "r_s1 (Loc (delta x2)) = NoPerm")
       apply (cut_tac r_x="ereq_use_env (Loc (delta x2)) tau_x" and r_s="r_s1" and x="Loc (delta x2)" in leq_use_none)
         apply (simp_all)
       apply (simp add: ereq_use_env_def)
       apply (simp add: one_use_env_def)
       apply (simp add: end_req_perm_def)
      apply (simp add: strong_disj_use_env_def)
      apply (simp add: ext_delta_def)
      apply (auto)
    (* pair case *)
     apply (rule_tac x="r_s2a" in exI)
     apply (rule_tac x="r_s3" in exI)
     apply (rule_tac x="rx1" in exI)
     apply (auto)
     apply (rule_tac x="rx2" in exI)
     apply (auto)
     apply (cut_tac r_x="r_s2a" and r_s="r_s1" and r_ex="r_x" in strong_disj_leq_use_env1)
       apply (auto)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    (* if case *)
    apply (rule_tac x="rx'" in exI)
    apply (rule_tac x="r_s2a" in exI)
    apply (cut_tac r_x="r_s2a" and r_s="r_s1" and r_ex="r_x" in strong_disj_leq_use_env1)
      apply (auto)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (rule_tac x="rx1" in exI)
    apply (auto)
    apply (rule_tac x="rx2" in exI)
    apply (auto)
    (* lam case *)
   apply (rule_tac x="rxa" in exI)
   apply (auto)
   apply (rule_tac x="r_end" in exI)
   apply (rule_tac x="r_s'" in exI)
   apply (cut_tac r_x="rxa" and x="x1a" and r="r" and r_ex="r_x" and r_s="r_s1" in wtedi_strong_disj_use_env)
      apply (auto)
   apply (case_tac "\<not> mem_val_env (add_env env (Var x1a) t1)")
    apply (simp add: mem_val_env_def)
    apply (simp add: add_env_def)
   apply (auto)
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
  apply (cut_tac r_x="r_s2a" and r_s="r_s1" and r_ex="r_x" in strong_disj_leq_use_env1)
    apply (auto)
  apply (rule_tac well_typed_perm_leq)
  apply (auto)
  done

definition loc_restr where    
  "loc_restr r_s = (\<lambda> x. case x of
    Var x \<Rightarrow> NoPerm
    | Loc y \<Rightarrow> r_s x
  )"  
  
lemma loc_restr_ext_delta: "ext_delta delta x r_s = ext_delta delta x (loc_restr r_s)"  
  apply (case_tac "\<forall> y. ext_delta delta x r_s y= ext_delta delta x (loc_restr r_s) y")
   apply (auto)
  apply (simp add: ext_delta_def)
  apply (simp add: loc_restr_def)
  done
    
lemma loc_restr_use_env: "loc_use_env (loc_restr r_s)"    
  apply (simp add: loc_use_env_def)
  apply (auto)
  apply (case_tac x)
   apply (auto)
  apply (simp add: loc_restr_def)
  done
    
lemma loc_restr_leq_use_env: "leq_use_env (loc_restr r_s) r_s"    
  apply (simp add: leq_use_env_def)
  apply (simp add: loc_restr_def)
  apply (auto)
  apply (case_tac x)
   apply (auto)
  apply (case_tac "r_s (Loc x2)")
    apply (auto)
  done

lemma dist_loc_restr_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (loc_restr r_x) (loc_restr r_s)"        
  apply (simp add: loc_restr_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac x)
   apply (auto)
  done

lemma well_typed_ext_delta: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; strong_disj_use_env r_s1 r_x; mem_val_env env \<rbrakk> \<Longrightarrow>
  well_typed env (ext_delta delta x r_x) r_s1 e tau r_s2 rx"
  apply (cut_tac delta="delta" and x="x" and r_s="r_x" in loc_restr_ext_delta)
  apply (auto)
  apply (rule_tac well_typed_ext_delta_ih)
     apply (auto)
   apply (rule_tac r_s="r_x" in strong_disj_leq_use_env2)
    apply (simp)
   apply (rule_tac loc_restr_leq_use_env)
  apply (rule_tac loc_restr_use_env)
  done    
    
lemma well_typed_ext_deltax: "\<lbrakk> well_typed env delta r_x e tau r_x r_x; leq_use_env r_x r_s; strong_disj_use_env r_x r_ex; mem_val_env env \<rbrakk> \<Longrightarrow>
  well_typed env (ext_delta delta x r_ex) r_s e tau r_s r_x"
  apply (rule_tac r_s="r_x" in well_typed_incr_simul_perm)
   apply (simp)
  apply (rule_tac well_typed_ext_delta)
    apply (auto)
  done
  
end