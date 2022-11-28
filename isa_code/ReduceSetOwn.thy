theory ReduceSetOwn
  imports SubstDropEnv ReduceProper
begin
  
    (* ##### defines a properly formed memory *)
  
fun mem_ty where
  "mem_ty (ArrayTy tau) = unlim tau"
| "mem_ty (ChanTy tau c_end) = True"
| "mem_ty tau = False"
    
definition mem_val_env where
  "mem_val_env env = (\<forall> x. case x of
    Var x \<Rightarrow> True
    | Loc b \<Rightarrow> (case env x of
      None \<Rightarrow> True
      | Some tau \<Rightarrow> mem_ty tau
    )
  )"      
  
lemma add_mem_val_env: "\<lbrakk> mem_val_env env \<rbrakk> \<Longrightarrow> mem_val_env (add_env env (Var x) tau)"  
  apply (simp add: mem_val_env_def)
  apply (auto)
  apply (case_tac "xa = Var x")
   apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (case_tac xa)
   apply (auto)
  apply (simp add: add_env_def)
  done
    
    (*
      ##### preliminary definitions for defining how permission environments change after ownership rewriting
     *)
  
    (* defines the set of ownership annotation vars in an expression *)
  (*
fun ann_vars where
  "ann_vars (ConstExp c) = {}"
| "ann_vars (OpExp xop) = {}"
| "ann_vars (VarExp (VarType x)) = {}"
| "ann_vars (VarExp (LocType x y)) = {y}"
| "ann_vars (PairExp e1 e2) = (ann_vars e1 \<union> ann_vars e2)"    
| "ann_vars (IfExp e1 e2 e3) = (ann_vars e1 \<union> ann_vars e2 \<union> ann_vars e3)"  
| "ann_vars (LamExp x e) = (ann_vars e)"  
| "ann_vars (AppExp e1 e2) = (ann_vars e1 \<union> ann_vars e2)"   
  
definition not_ann_var where
  "not_ann_var x e = (x \<notin> ann_vars e)"  
  
lemma ann_res_vars: "\<lbrakk> Loc x \<in> res_vars e \<rbrakk> \<Longrightarrow> x \<in> ann_vars e"  
  apply (induct e)
        apply (auto)
  apply (case_tac xa)
   apply (auto)
  done
  *)
    (* semi-weakness: defines weakness over a set of variables *)
  (*
definition semi_weak_use_env where
  "semi_weak_use_env r_s r_set = (\<forall> x. x \<in> r_set \<longrightarrow> r_s (Loc x) \<noteq> OwnPerm)"

lemma sw_leq_use_env: "\<lbrakk> leq_use_env r_x r_s; semi_weak_use_env r_s r_set \<rbrakk> \<Longrightarrow> semi_weak_use_env r_x r_set"  
  apply (simp add: semi_weak_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="Loc x" in allE)
  apply (auto)
  apply (case_tac "r_s (Loc x)")
    apply (auto)
  done      

lemma sw_add_use_env: "\<lbrakk> semi_weak_use_env r_s r_set; x \<notin> r_set \<rbrakk> \<Longrightarrow> semi_weak_use_env (add_use_env r_s (Loc x) r) r_set"    
  apply (simp add: semi_weak_use_env_def)
  apply (simp add: add_use_env_def)
  done
  
lemma sw_add_use_env2: "\<lbrakk> semi_weak_use_env r_s r_set \<rbrakk> \<Longrightarrow> semi_weak_use_env (add_use_env r_s (Var x) r) r_set"    
  apply (simp add: semi_weak_use_env_def)
  apply (simp add: add_use_env_def)
  done
    
lemma rhs_sw_leq_use_none: "\<lbrakk> leq_use_env (diff_use_env r_x r_ex) r_s; r_s (Loc x) = NoPerm; semi_weak_use_env r_ex r_set; x \<in> r_set  \<rbrakk> \<Longrightarrow> r_x (Loc x) = NoPerm"    
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: semi_weak_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="Loc x" in allE)
  apply (auto)
  apply (case_tac "r_ex (Loc x)")
    apply (auto)
   apply (case_tac "r_x (Loc x)")
     apply (auto)
  apply (case_tac "r_x (Loc x)")
    apply (auto)
  done 
    
lemma semi_weak_drop_use_env: "semi_weak_use_env (drop_use_env r_s) r_set"    
  apply (simp add: semi_weak_use_env_def)
  apply (auto)
  apply (simp add: drop_use_env_def)
  apply (case_tac "r_s (Loc x)")
    apply (auto)
  done    
    
    (* pwrite_use_env: pwrite(P, S, x) =
        if (exists z \<in> S and z \<in> P) P + {x: use}
        else P
      (x is only written if one of the vars from S is in P)
    *)
    
definition set_use_none :: "perm_use_env \<Rightarrow> string set \<Rightarrow> bool" where
  "set_use_none r_s r_set = (\<forall> x. x \<in> r_set \<longrightarrow> r_s (Loc x) = NoPerm)"
    

    
lemma leq_set_use_none: "\<lbrakk> leq_use_env r_x r_s; set_use_none r_s s \<rbrakk> \<Longrightarrow> set_use_none r_x s"  
  apply (simp add: set_use_none_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="Loc x" in allE)
  apply (auto)
  apply (case_tac "r_x (Loc x)")
    apply (auto)
  done    
    
    
lemma disj_add_use_env_sw: "\<lbrakk> disj_use_env r_x r_s; semi_weak_use_env r_s r_set; x \<in> r_set \<rbrakk> \<Longrightarrow> disj_use_env (add_use_env r_x (Loc x) UsePerm) r_s"    
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: add_use_env_def)
  apply (auto)
  apply (simp add: semi_weak_use_env_def)
  done    
    
lemma disj_pwrite_use_env: "\<lbrakk> semi_weak_use_env r_x r_set; semi_weak_use_env r_s r_set; x \<in> r_set; disj_use_env r_x r_s \<rbrakk> \<Longrightarrow>
  disj_use_env (pwrite_use_env r_x r_set x) (pwrite_use_env r_s r_set x)"   
  apply (simp add: pwrite_use_env_def)
  apply (auto)
    apply (rule_tac comm_disj_use_env)
    apply (rule_tac disj_add_use_env_sw)
    apply (rule_tac comm_disj_use_env)
     apply (auto)
   apply (rule_tac disj_add_use_env_sw)
    apply (auto)
  apply (rule_tac disj_add_use_env_sw)
   apply (rule_tac comm_disj_use_env)
   apply (rule_tac disj_add_use_env_sw)
    apply (rule_tac comm_disj_use_env)
    apply (auto)
  apply (simp add: semi_weak_use_env_def)
  apply (simp add: add_use_env_def)
  done
  
lemma disj_lift_pwrite_use_env: "\<lbrakk> disj_use_env (lift_use_env r_x r) (lift_use_env r_s r);
  leq_use_env (lift_use_env r_x r) r_c; leq_use_env (lift_use_env r_s r) r_c; semi_weak_use_env r_c r_set; x \<in> r_set \<rbrakk> \<Longrightarrow>
  disj_use_env (lift_use_env (pwrite_use_env r_x r_set x) r) (lift_use_env (pwrite_use_env r_s r_set x) r)"    
  apply (case_tac "\<not> is_own r")
   apply (simp add: is_own_def)
    apply (case_tac r)
      apply (auto)
    apply (rule_tac disj_pwrite_use_env)
       apply (auto)
     apply (rule_tac r_s="r_c" in sw_leq_use_env)
      apply (auto)
    apply (rule_tac r_s="r_c" in sw_leq_use_env)
     apply (auto)
   apply (rule_tac disj_pwrite_use_env)
     apply (auto)
    apply (rule_tac r_s="r_c" in sw_leq_use_env)
     apply (auto)
   apply (rule_tac r_s="r_c" in sw_leq_use_env)
    apply (auto)
  apply (case_tac "\<not> set_use_none r_x r_set")
   apply (simp add: set_use_none_def)
   apply (auto)
   apply (simp add: leq_use_env_def)
   apply (erule_tac x="Loc xa" in allE)
   apply (simp add: is_own_def)
   apply (simp add: semi_weak_use_env_def)
   apply (case_tac "r_c (Loc xa)")
     apply (auto)
    (* if r_s uses x in r_set, r_c x = Own, a contradiction by semi-weakness *)
  apply (case_tac "\<not> set_use_none r_s r_set")
   apply (simp add: set_use_none_def)
   apply (auto)
   apply (simp add: leq_use_env_def)
   apply (erule_tac x="Loc xa" in allE)
   apply (erule_tac x="Loc xa" in allE)
   apply (simp add: semi_weak_use_env_def)
   apply (simp add: is_own_def)
   apply (case_tac "r_c (Loc xa)")
     apply (auto)
  apply (simp add: pwrite_use_env_def)
  done    

    (* - pwrite equality lemmas *)
    
lemma lift_pwrite_use_env: "\<lbrakk> semi_weak_use_env (lift_use_env r_s r) r_set \<rbrakk> \<Longrightarrow>
  pwrite_use_env (lift_use_env r_s r) r_set x = lift_use_env (pwrite_use_env r_s r_set x) r"
  apply (case_tac "is_own r")
   apply (case_tac "\<not> set_use_none r_s r_set")
    apply (simp add: set_use_none_def)
    apply (auto)
    apply (simp add: semi_weak_use_env_def)
    apply (simp add: is_own_def)
    apply (erule_tac x="xa" in allE)
    apply (auto)
   apply (simp add: pwrite_use_env_def)
   apply (auto)
   apply (simp add: set_use_none_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (simp add: is_own_def)
  apply (simp add: is_own_def)
  apply (case_tac r)
    apply (auto)
  done
    
lemma pwc_add_use_env1: "\<lbrakk> semi_weak_use_env r_x r_set; x \<in> r_set \<rbrakk> \<Longrightarrow> comp_use_env r_x (add_use_env r_s (Loc x) UsePerm) = add_use_env (comp_use_env r_x r_s) (Loc x) UsePerm"    
  apply (case_tac "\<forall> y. comp_use_env r_x (add_use_env r_s (Loc x) UsePerm) y = add_use_env (comp_use_env r_x r_s) (Loc x) UsePerm y")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: semi_weak_use_env_def)
  apply (case_tac "Loc x = y")
   apply (auto)
  apply (case_tac "r_x (Loc x)")
    apply (auto)
  done

lemma pwc_add_use_env2: "\<lbrakk> semi_weak_use_env r_s r_set; x \<in> r_set \<rbrakk> \<Longrightarrow> comp_use_env (add_use_env r_x (Loc x) UsePerm) r_s = add_use_env (comp_use_env r_x r_s) (Loc x) UsePerm"    
  apply (case_tac "\<forall> y. comp_use_env (add_use_env r_x (Loc x) UsePerm) r_s y = add_use_env (comp_use_env r_x r_s) (Loc x) UsePerm y")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: semi_weak_use_env_def)
  apply (case_tac "Loc x = y")
   apply (auto)
  apply (case_tac "r_s (Loc x)")
    apply (auto)
  done    
  
lemma pwrite_comp_use_env: "\<lbrakk> semi_weak_use_env r_x r_set; semi_weak_use_env r_s r_set; x \<in> r_set \<rbrakk> \<Longrightarrow>
  comp_use_env (pwrite_use_env r_x r_set x) (pwrite_use_env r_s r_set x) = pwrite_use_env (comp_use_env r_x r_s) r_set x"
  apply (case_tac "set_use_none r_x r_set")
   apply (case_tac "set_use_none r_s r_set")
    apply (simp add: pwrite_use_env_def)
    apply (auto)
    apply (simp add: set_use_none_def)
    apply (simp add: comp_use_env_def)
    apply (auto)
   apply (simp add: pwrite_use_env_def)
   apply (auto)
    apply (simp add: set_use_none_def)
    apply (simp add: comp_use_env_def)
    apply (auto)
    apply (erule_tac x="xa" in allE)
    apply (erule_tac x="xa" in allE)
    apply (auto)
    apply (case_tac "r_s (Loc xa)")
      apply (auto)
   apply (rule_tac pwc_add_use_env1)
   apply (auto)
  apply (case_tac "set_use_none r_s r_set")
   apply (simp add: pwrite_use_env_def)
   apply (auto)
    apply (simp add: set_use_none_def)
    apply (simp add: comp_use_env_def)
    apply (auto)
    apply (erule_tac x="xa" in allE)
    apply (erule_tac x="xa" in allE)
    apply (auto)
    apply (case_tac "r_x (Loc xa)")
      apply (auto)
   apply (rule_tac pwc_add_use_env2)
   apply (auto)
  apply (simp add: pwrite_use_env_def)
  apply (auto)
   apply (simp add: set_use_none_def)
   apply (simp add: comp_use_env_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (auto) 
   apply (case_tac "r_x (Loc xa)")
     apply (auto)
   apply (case_tac "r_s (Loc xa)")
     apply (auto)
  apply (rule_tac dist_add_comp_use_env)
  done    
  
lemma diff_pwrite_rem_use_env: "\<lbrakk> semi_weak_use_env r_x r_set; x \<in> r_set \<rbrakk> \<Longrightarrow>
  diff_use_env (pwrite_use_env r_s r_set x) (rem_use_env r_x (Loc x)) = pwrite_use_env (diff_use_env r_s r_x) r_set x"    
  apply (case_tac "set_use_none r_s r_set")
   apply (simp add: pwrite_use_env_def)
   apply (auto)
   apply (simp add: set_use_none_def)
    apply (case_tac "\<forall> y. diff_use_env r_s (rem_use_env r_x (Loc x)) y = diff_use_env r_s r_x y")
     apply (auto)
    apply (simp add: diff_use_env_def)
    apply (simp add: rem_use_env_def)
    apply (case_tac "Loc x = y")
     apply (auto)
   apply (simp add: set_use_none_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (auto)
   apply (cut_tac r_x="diff_use_env r_s r_x" and r_s="r_s" and x="Loc xa" in leq_use_none)
     apply (auto)
   apply (rule_tac self_diff_leq_use_env)
  apply (simp add: pwrite_use_env_def)
  apply (auto)
   apply (simp add: set_use_none_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (auto)
   apply (case_tac "r_x (Loc xa) \<noteq> OwnPerm")
    apply (simp add: diff_use_env_def)
    apply (case_tac "r_x (Loc xa)")
      apply (auto)
   apply (simp add: semi_weak_use_env_def)
  apply (simp add: semi_weak_use_env_def)
  apply (simp add: diff_add_rem_use_env)
  done    
    
    (* #### actual ownership rewriting algorithm *)
  
fun set_own where
  "set_own (ConstExp c) b = ConstExp c"
| "set_own (OpExp xop) b = OpExp xop"
| "set_own (VarExp v) b = (case v of
    VarType x \<Rightarrow> VarExp v
    | LocType x y \<Rightarrow> VarExp (LocType x b))"
| "set_own (PairExp e1 e2) b = (PairExp (set_own e1 b) (set_own e2 b))"
| "set_own (IfExp e1 e2 e3) b = (IfExp (set_own e1 b) (set_own e2 b) (set_own e3 b))"
| "set_own (LamExp x e) b = (LamExp x (set_own e b))"  
| "set_own (AppExp e1 e2) b = (AppExp (set_own e1 b) (set_own e2 b))"
  
lemma well_typed_set_own_ann_vars: "\<lbrakk> well_typed env r_s1 (set_own e b) tau r_s2 rx; x \<noteq> b \<rbrakk> \<Longrightarrow> x \<notin> ann_vars (set_own e b)"  
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
    (* var case *)
          apply (case_tac xa)
           apply (auto)
    (* other cases *)
         apply (iprover)
        apply (iprover)
       apply (iprover)
      apply (iprover)
     apply (iprover)
    apply (iprover)
   apply (iprover)
  apply (iprover)
  done
    
lemma well_typed_set_own_none: "\<lbrakk> ann_vars e = {}; well_typed env r_s1 e tau r_s2 rx \<rbrakk> \<Longrightarrow>
   well_typed env r_s1 (set_own e b) tau r_s2 rx"    
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)  
        apply (auto)
    (* var case *)
      apply (case_tac x)
       apply (auto)
    (* pair case *)
     apply (rule_tac x="r_s2a" in exI)
     apply (rule_tac x="r_s3" in exI)
     apply (rule_tac x="rx1" in exI)
     apply (auto)
     apply (rule_tac x="rx2" in exI)
     apply (auto)
    (* if case *)
    apply (rule_tac x="rx'" in exI)
    apply (rule_tac x="r_s2a" in exI)
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
  done  
 
lemma well_typed_no_av_use: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; r_s1 (Loc x) = NoPerm \<rbrakk> \<Longrightarrow> not_ann_var x e"    
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
    (* const + op cases *)
        apply (simp add: not_ann_var_def)
       apply (simp add: not_ann_var_def)
    (* var case *)
      apply (simp add: not_ann_var_def)
      apply (auto)
      apply (simp add: leq_use_env_def)
      apply (simp add: ereq_use_env_def)
      apply (simp add: one_use_env_def)
      apply (erule_tac x="Loc x" in allE)
      apply (case_tac xa)
       apply (auto)
      apply (simp add: end_req_perm_def)
    (* pair case *)
     apply (simp add: not_ann_var_def)
     apply (cut_tac r_x="r_s2a" and r_s="r_s1" and x="Loc x" in leq_use_none)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
    (* if case *)
    apply (simp add: not_ann_var_def)
    apply (cut_tac r_x="r_s2a" and r_s="r_s1" and x="Loc x" in leq_use_none)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    (* lam case *)
   apply (simp add: not_ann_var_def)
   apply (cut_tac r_x="rxa" and r_s="r_s1" and x="Loc x" in leq_use_none)
     apply (auto)
   apply (case_tac "\<not> add_use_env rxa (Var x1a) r (Loc x) = NoPerm")
    apply (simp add: add_use_env_def)
   apply (auto)
   apply (iprover)
    (* app case *)
  apply (simp add: not_ann_var_def)
  apply (cut_tac r_x="r_s2a" and r_s="r_s1" and x="Loc x" in leq_use_none)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
  done    
    
lemma water_var_case: "\<lbrakk>ann_vars (VarExp x) \<subseteq> r_set; semi_weak_use_env r_s1 r_set; b \<in> r_set; env (Loc b) = Some t; mem_ty t; env (res_name x) = Some tau;
        env (owner_name x) = Some tau_x; value_req x tau tau_x; leq_use_env (ereq_use_env (owner_name x) tau_x) r_s1;
        leq_use_env r_s2 (diff_use_env r_s1 (comp_use_env (ereq_use_env (owner_name x) tau_x) r_ex)); leq_use_env rx r_s2; leq_use_env r_ex r_s1;
        leq_use_env (diff_use_env (ereq_use_env (owner_name x) tau_x) (comp_use_env (ereq_use_env (owner_name x) tau_x) r_ex)) rx\<rbrakk>
       \<Longrightarrow> well_typed env (add_use_env r_s1 (Loc b) UsePerm) (case x of VarType xa \<Rightarrow> VarExp x | LocType x y \<Rightarrow> VarExp (LocType x b)) tau
            (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx r_set b)"
    (* var case. non-value *)
       (*apply (simp add: not_free_var_def)*)
  apply (case_tac x)
   apply (auto)
      apply (rule_tac rhs_add_leq_use_env)
       apply (auto)
      apply (simp add: ereq_use_env_def)
      apply (simp add: one_use_env_def)
     apply (rule_tac x="rem_use_env r_ex (Loc b)" in exI)
     apply (auto)
        apply (rule_tac r_sb="diff_use_env (add_use_env r_s1 (Loc b) UsePerm) (rem_use_env (comp_use_env (ereq_use_env (Var x1) tau_x) r_ex) (Loc b))" in trans_leq_use_env)
         apply (simp add: dist_rem_comp_use_env)
         apply (rule_tac unroll_dcl_use_env)
         apply (rule_tac dist_diff_leq_use_env)
         apply (rule_tac rhs_diff_rem_leq_use_env2)
          apply (simp add: ereq_use_env_def)
          apply (simp add: one_use_env_def)
         apply (rule_tac id_leq_use_env)
        apply (rule_tac t="diff_use_env (add_use_env r_s1 (Loc b) UsePerm) (rem_use_env (comp_use_env (ereq_use_env (Var x1) tau_x) r_ex) (Loc b))"
           and s="add_use_env (diff_use_env r_s1 (comp_use_env (ereq_use_env (Var x1) tau_x) r_ex)) (Loc b) UsePerm" in subst)
         apply (rule_tac diff_add_rem_use_env)
        apply (rule_tac dist_add_leq_use_env)
        apply (simp)
       apply (rule_tac add_pwrite_leq_use_env)
         apply (rule_tac r_s="r_s1" in sw_leq_use_env)
          apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env (Var x1) tau_x) r_ex)" in trans_leq_use_env)
           apply (rule_tac self_diff_leq_use_env)
          apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
           apply (auto)
       apply (rule_tac dist_add_leq_use_env)
       apply (simp)
      apply (rule_tac rhs_add_leq_use_env)
       apply (rule_tac rem_leq_use_env)
       apply (simp)
      apply (simp add: rem_use_env_def)
     apply (rule_tac r_sb="diff_use_env (ereq_use_env (Var x1) tau_x) (comp_use_env (ereq_use_env (Var x1) tau_x) r_ex)" in trans_leq_use_env)
      apply (rule_tac pwrite_leq_use_env)
        apply (rule_tac r_s="r_s1" in sw_leq_use_env)
         apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env (Var x1) tau_x) r_ex)" in trans_leq_use_env)
          apply (rule_tac self_diff_leq_use_env)
         apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
          apply (auto)
     apply (rule_tac unroll_dcl_use_env)
     apply (rule_tac rhs_diff_rem_leq_use_env2)
      apply (cut_tac r_x="r_ex" and r_s="r_s1" in sw_leq_use_env)
        apply (simp)
       apply (auto)
      apply (simp add: semi_weak_use_env_def)
     apply (rule_tac id_leq_use_env)
    apply (case_tac t)
          apply (auto)
   apply (rule_tac ereq_leq_use_envx)
   apply (simp add: end_req_perm_def)
   apply (simp add: add_use_env_def)
   apply (case_tac t)
         apply (auto)
    (* var case. value cases *)
  apply (rule_tac x="rem_use_env r_ex (Loc b)" in exI)
  apply (auto)
     apply (rule_tac rhs_flip_use_env)
     apply (rule_tac rhs_unroll_dcl_use_env)
     apply (rule_tac rhs_weak_leq_use_env)
      apply (rule_tac weak_ereq_use_env)
      apply (simp add: unlim_def)
      apply (case_tac t)
            apply (auto)
     apply (rule_tac t="diff_use_env (add_use_env r_s1 (Loc b) UsePerm) (rem_use_env r_ex (Loc b))" and s="add_use_env (diff_use_env r_s1 r_ex) (Loc b) UsePerm" in subst)
      apply (rule_tac diff_add_rem_use_env)
     apply (rule_tac dist_add_leq_use_env)
     apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env (Loc x22) tau_x) r_ex)" in trans_leq_use_env)
      apply (rule_tac dist_diff_leq_use_env_gen)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac self_comp_leq_use_env2)
     apply (simp)
    apply (rule_tac add_pwrite_leq_use_env)
      apply (rule_tac r_s="r_s1" in sw_leq_use_env)
       apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env (Loc x22) tau_x) r_ex)" in trans_leq_use_env)
        apply (rule_tac self_diff_leq_use_env)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (auto)
    apply (rule_tac dist_add_leq_use_env)
    apply (simp)
   apply (rule_tac rhs_add_leq_use_env)
    apply (rule_tac rem_leq_use_env)
    apply (simp)
   apply (simp add: rem_use_env_def)
    (* - req bound manipulation *)
  apply (simp add: pwrite_use_env_def)
  apply (auto)
    (* - say that we do not add a perm to rx. this means x1a is not in rx, which is impossible since r_s1 is weak *)
   apply (case_tac "rx (Loc x22) \<noteq> NoPerm")
    apply (simp add: set_use_none_def)
   apply (case_tac "ereq_use_env (Loc x22) tau_x (Loc x22) \<noteq> UsePerm")
    apply (simp add: ereq_use_env_def)
    apply (simp add: one_use_env_def)
    apply (simp add: end_req_perm_def)
   apply (case_tac "comp_use_env (ereq_use_env (Loc x22) tau_x) r_ex (Loc x22) \<noteq> OwnPerm")
    apply (cut_tac r_x="ereq_use_env (Loc x22) tau_x" and r_s="rx" and r_ex="comp_use_env (ereq_use_env (Loc x22) tau_x) r_ex" and x="Loc x22" in diff_use_leq)
      apply (auto)
   apply (cut_tac r_x="comp_use_env (ereq_use_env (Loc x22) tau_x) r_ex" and r_s="r_s1" and x="Loc x22" in leq_use_own)
     apply (simp)
    apply (rule_tac dist_comp_leq_use_env)
     apply (auto)
   apply (simp add: semi_weak_use_env_def)
    (* - otherwise we know what x is *)
  apply (rule_tac diff_leq_use_env)
  apply (rule_tac ereq_leq_use_envx)
  apply (simp add: add_use_env_def)
  apply (simp add: end_req_perm_def)
  apply (case_tac t)
        apply (auto)
  done  
  
lemma water_pair_case: "\<lbrakk>\<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e1 tau r_s2 rx; semi_weak_use_env r_s1 r_set; env (Loc b) = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 (Loc b) UsePerm) (set_own e1 b) tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx r_set b);
        \<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e2 tau r_s2 rx; semi_weak_use_env r_s1 r_set; env (Loc b) = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 (Loc b) UsePerm) (set_own e2 b) tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx r_set b);
        semi_weak_use_env r_s1 r_set; b \<in> r_set; env (Loc b) = Some t; mem_ty t; ann_vars e1 \<subseteq> r_set; ann_vars e2 \<subseteq> r_set; well_typed env r_s1 e1 t1 r_s2a rx1;
        well_typed env r_s2a e2 t2 r_s3 rx2; leq_use_env (lift_use_env rx1 r) r_s3; leq_use_env (lift_use_env rx2 r) r_s3;
        aff_leq (max_aff (req_type t1) (req_type t2)) r; disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r); leq_use_env r_s2 (diff_use_env r_s3 r_ex);
        leq_use_env rx r_s2; leq_use_env r_ex r_s1; leq_use_env (pair_req (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex (PairTy t1 t2 r)) rx\<rbrakk>
       \<Longrightarrow> \<exists>r_s2a r_s3 rx1.
              well_typed env (add_use_env r_s1 (Loc b) UsePerm) (set_own e1 b) t1 r_s2a rx1 \<and>
              (\<exists>rx2. well_typed env r_s2a (set_own e2 b) t2 r_s3 rx2 \<and>
                     leq_use_env (lift_use_env rx1 r) r_s3 \<and>
                     leq_use_env (lift_use_env rx2 r) r_s3 \<and>
                     disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r) \<and>
                     (\<exists>r_ex. leq_use_env (add_use_env r_s2 (Loc b) UsePerm) (diff_use_env r_s3 r_ex) \<and>
                             leq_use_env (pwrite_use_env rx r_set b) (add_use_env r_s2 (Loc b) UsePerm) \<and>
                             leq_use_env r_ex (add_use_env r_s1 (Loc b) UsePerm) \<and>
                             leq_use_env (pair_req (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex (PairTy t1 t2 r)) (pwrite_use_env rx r_set b)))"    
  apply (rule_tac x="add_use_env r_s2a (Loc b) UsePerm" in exI)
  apply (rule_tac x="add_use_env r_s3 (Loc b) UsePerm" in exI)
  apply (rule_tac x="pwrite_use_env rx1 r_set b" in exI)
  apply (auto)
  apply (cut_tac r_sc="r_s3" and r_sb="r_s2a" and r_sa="r_s1" in trans_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  apply (cut_tac r_x="lift_use_env rx1 r" and r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
     apply (auto)
  apply (cut_tac r_x="lift_use_env rx2 r" and r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
     apply (auto)
  apply (rule_tac x="pwrite_use_env rx2 r_set b" in exI)
  apply (auto)
      apply (cut_tac r_x="r_s2a" and r_s="r_s1" in sw_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
     apply (rule_tac lift_pwrite_leq_use_env)
       apply (rule_tac r_s="r_s1" in sw_leq_use_env)
        apply (auto)
    apply (rule_tac lift_pwrite_leq_use_env)
      apply (rule_tac r_s="r_s1" in sw_leq_use_env)
       apply (auto)
   apply (rule_tac r_c="r_s1" in disj_lift_pwrite_use_env)
       apply (auto)
    apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
     apply (auto)
   apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
    apply (auto)
  apply (rule_tac x="rem_use_env r_ex (Loc b)" in exI)
  apply (auto)
     apply (rule_tac t="diff_use_env (add_use_env r_s3 (Loc b) UsePerm) (rem_use_env r_ex (Loc b))"
          and s="add_use_env (diff_use_env r_s3 r_ex) (Loc b) UsePerm" in subst)
      apply (rule_tac diff_add_rem_use_env)
     apply (rule_tac dist_add_leq_use_env)
     apply (simp)
    apply (rule_tac add_pwrite_leq_use_env)
      apply (rule_tac r_s="r_s1" in sw_leq_use_env)
       apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
        apply (rule_tac diff_leq_use_env)
        apply (simp)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (auto)
    apply (rule_tac dist_add_leq_use_env)
    apply (simp)
   apply (rule_tac rhs_add_leq_use_env)
    apply (rule_tac rem_leq_use_env)
    apply (auto)
   apply (simp add: rem_use_env_def)
  apply (case_tac "req_type (PairTy t1 t2 r) = Prim")
   apply (simp add: pair_req_def)
   apply (rule_tac leq_empty_use_env)
  apply (simp add: pair_req_def)
  apply (rule_tac t="lift_use_env (pwrite_use_env rx1 r_set b) r" and s="pwrite_use_env (lift_use_env rx1 r) r_set b" in subst)
   apply (rule_tac lift_pwrite_use_env)
   apply (rule_tac r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
     apply (auto)
  apply (rule_tac t="lift_use_env (pwrite_use_env rx2 r_set b) r" and s="pwrite_use_env (lift_use_env rx2 r) r_set b" in subst)
   apply (rule_tac lift_pwrite_use_env)
   apply (rule_tac r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
     apply (auto)
  apply (simp add: pwrite_comp_use_env)
  apply (cut_tac r_x="r_ex" and r_s="r_s1" in sw_leq_use_env)
    apply (auto)
  apply (simp add: diff_pwrite_rem_use_env)
  apply (rule_tac dist_pwrite_leq_use_env)
    apply (rule_tac r_s="r_s1" in sw_leq_use_env)
     apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
      apply (rule_tac diff_leq_use_env)
      apply (simp)
     apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
      apply (auto)
  done

lemma water_if_case: "\<lbrakk>\<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e1 tau r_s2 rx; semi_weak_use_env r_s1 r_set; env (Loc b) = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 (Loc b) UsePerm) (set_own e1 b) tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx r_set b);
        \<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e2 tau r_s2 rx; semi_weak_use_env r_s1 r_set; env (Loc b) = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 (Loc b) UsePerm) (set_own e2 b) tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx r_set b);
        \<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e3 tau r_s2 rx; semi_weak_use_env r_s1 r_set; env (Loc b) = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 (Loc b) UsePerm) (set_own e3 b) tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx r_set b);
        semi_weak_use_env r_s1 r_set; b \<in> r_set; env (Loc b) = Some t; mem_ty t; ann_vars e1 \<subseteq> r_set; well_typed env r_s1 e1 BoolTy r_s2a rx';
        ann_vars e2 \<subseteq> r_set; ann_vars e3 \<subseteq> r_set; well_typed env r_s2a e2 tau r_s2 rx1; well_typed env r_s2a e3 tau r_s2 rx2\<rbrakk>
       \<Longrightarrow> \<exists>rx' r_s2a.
              well_typed env (add_use_env r_s1 (Loc b) UsePerm) (set_own e1 b) BoolTy r_s2a rx' \<and>
              (\<exists>rx1a. well_typed env r_s2a (set_own e2 b) tau (add_use_env r_s2 (Loc b) UsePerm) rx1a \<and>
                      (\<exists>rx2a. well_typed env r_s2a (set_own e3 b) tau (add_use_env r_s2 (Loc b) UsePerm) rx2a \<and>
                              pwrite_use_env (comp_use_env rx1 rx2) r_set b = comp_use_env rx1a rx2a))"    
  apply (rule_tac x="pwrite_use_env rx' r_set b" in exI)
  apply (rule_tac x="add_use_env r_s2a (Loc b) UsePerm" in exI)
  apply (auto)
  apply (cut_tac r_x="r_s2a" and r_s="r_s1" and r_set="r_set" in sw_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
  apply (rule_tac x="pwrite_use_env rx1 r_set b" in exI)
  apply (auto)
  apply (rule_tac x="pwrite_use_env rx2 r_set b" in exI)
  apply (auto)
  apply (cut_tac r_x="r_s2" and r_s="r_s2a" in sw_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
  apply (cut_tac r_x="rx1" and r_s="r_s2" in sw_leq_use_env)
    apply (rule_tac well_typed_perm_leqx)
    apply (auto)
  apply (cut_tac r_x="rx2" and r_s="r_s2" in sw_leq_use_env)
    apply (rule_tac well_typed_perm_leqx)
    apply (auto)
  apply (simp add: pwrite_comp_use_env)
  done    
    
lemma wtae_end_leq_use_env2: "\<lbrakk> leq_use_env r_x (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow>
  leq_use_env (add_use_env r_x x UsePerm) (diff_use_env (add_use_env r_s x UsePerm) (rem_use_env r_ex x))"  
  apply (rule_tac t="diff_use_env (add_use_env r_s x UsePerm) (rem_use_env r_ex x)"
      and s="add_use_env (diff_use_env r_s r_ex) x UsePerm" in subst)
   apply (rule_tac diff_add_rem_use_env)
  apply (rule_tac dist_add_leq_use_env)
  apply (simp)  
  done    
    
lemma water_lam_case: "\<lbrakk>\<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e tau r_s2 rx; semi_weak_use_env r_s1 r_set; env (Loc b) = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 (Loc b) UsePerm) (set_own e b) tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx r_set b);
        ann_vars e \<subseteq> r_set; semi_weak_use_env r_s1 r_set; b \<in> r_set; env (Loc b) = Some t; mem_ty t;
        well_typed (add_env env (Var x1a) t1) (add_use_env rxa (Var x1a) r) e t2 r_s' r_end; aff_use_env rxa a; leq_use_env rxa r_s1;
        leq_use_env r_s2 (diff_use_env r_s1 r_ex); leq_use_env rx r_s2; leq_use_env r_ex r_s1; leq_use_env (diff_use_env rxa r_ex) rx\<rbrakk>
       \<Longrightarrow> \<exists>rxa. (\<exists>r_end r_s'. well_typed (add_env env (Var x1a) t1) (add_use_env rxa (Var x1a) r) (set_own e b) t2 r_s' r_end) \<and>
                 aff_use_env rxa a \<and>
                 leq_use_env rxa (add_use_env r_s1 (Loc b) UsePerm) \<and>
                 (\<exists>r_ex. leq_use_env (add_use_env r_s2 (Loc b) UsePerm) (diff_use_env (add_use_env r_s1 (Loc b) UsePerm) r_ex) \<and>
                         leq_use_env (pwrite_use_env rx r_set b) (add_use_env r_s2 (Loc b) UsePerm) \<and>
                         leq_use_env r_ex (add_use_env r_s1 (Loc b) UsePerm) \<and> leq_use_env (diff_use_env rxa r_ex) (pwrite_use_env rx r_set b))"
    (* lam case. rxa does not contain any members of r_set *)
  apply (case_tac "set_use_none rxa r_set")
   apply (rule_tac x="rxa" in exI)
   apply (auto)
     apply (rule_tac x="r_end" in exI)
     apply (rule_tac x="r_s'" in exI)
     apply (rule_tac well_typed_set_own_none)
      apply (auto)
     apply (cut_tac env="add_env env (Var x1a) t1" and ?r_s1.0="add_use_env rxa (Var x1a) r" and x="x" and e="e" in well_typed_no_av_use)
       apply (auto)
      apply (simp add: add_use_env_def)
      apply (simp add: set_use_none_def)
      apply (auto)
     apply (simp add: not_ann_var_def)
    apply (rule_tac rhs_add_leq_use_env)
     apply (simp)
    apply (simp add: set_use_none_def)
   apply (rule_tac x="rem_use_env r_ex (Loc b)" in exI)
   apply (auto)
      apply (rule_tac wtae_end_leq_use_env2)
      apply (simp)
     apply (rule_tac add_pwrite_leq_use_env)
       apply (rule_tac r_s="r_s1" in sw_leq_use_env)
        apply (rule_tac r_sb="diff_use_env r_s1 r_ex" in trans_leq_use_env)
         apply (rule_tac self_diff_leq_use_env)
        apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
         apply (auto)
     apply (rule_tac dist_add_leq_use_env)
     apply (simp)
    apply (rule_tac rhs_add_leq_use_env)
     apply (rule_tac rem_leq_use_env)
     apply (simp)
    apply (simp add: rem_use_env_def)
   apply (rule_tac pwrite_leq_use_env)
     apply (rule_tac r_s="r_s1" in sw_leq_use_env)
      apply (rule_tac r_sb="diff_use_env r_s1 r_ex" in trans_leq_use_env)
       apply (rule_tac self_diff_leq_use_env)
      apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
       apply (auto)
   apply (rule_tac r_sb="diff_use_env rxa r_ex" in trans_leq_use_env)
    apply (simp)
    apply (rule_tac rhs_diff_rem_leq_use_env)
    apply (simp add: set_use_none_def)
   apply (rule_tac id_leq_use_env)  
    (* lam case. rxa contains at least one member of r_set *)
    (* - prelim: rxa is not primitive *)
  apply (case_tac "a = Prim")
   apply (simp add: set_use_none_def)
   apply (auto)
   apply (simp add: aff_use_env_def)
  apply (simp add: null_use_env_def)
    (* - prelim: rx has at least one value as well *)
  apply (case_tac "set_use_none rx r_set")
   apply (simp add: set_use_none_def)
   apply (auto)
   apply (erule_tac x="x" in allE)
   apply (cut_tac r_ex="r_ex" and r_x="rxa" and r_s="rx" and x="x" in rhs_sw_leq_use_none)
       apply (auto)
   apply (rule_tac r_s="r_s1" in sw_leq_use_env)
    apply (auto)
    (* - prelim: x \<noteq> x1a *)
  apply (rule_tac x="add_use_env rxa (Loc b) UsePerm" in exI)
  apply (auto)
     apply (rule_tac x="pwrite_use_env r_end r_set b" in exI)
     apply (rule_tac x="add_use_env r_s' (Loc b) UsePerm" in exI)
     apply (rule_tac t="add_use_env (add_use_env rxa (Loc b) UsePerm) (Var x1a) r" and s="add_use_env (add_use_env rxa (Var x1a) r) (Loc b) UsePerm" in subst)
      apply (simp add: almost_comm_add_use_env)
     apply (cut_tac r_s="rxa" and x="x1a" and r="r" and r_set="r_set" in sw_add_use_env2)
      apply (rule_tac r_s="r_s1" in sw_leq_use_env)
       apply (auto)
     apply (case_tac "\<not> add_env env (Var x1a) t1 (Loc b) = Some t")
      apply (simp add: add_env_def)
     apply (auto)
    apply (simp add: aff_use_env_def)
    apply (case_tac a)
      apply (auto)
    apply (simp add: weak_use_env_def)
    apply (simp add: add_use_env_def)
   apply (rule_tac dist_add_leq_use_env)
   apply (simp)
  apply (rule_tac x="rem_use_env r_ex (Loc b)" in exI)
  apply (auto)
     apply (rule_tac t="diff_use_env (add_use_env r_s1(Loc b) UsePerm) (rem_use_env r_ex (Loc b))" and
        s="add_use_env (diff_use_env r_s1 r_ex) (Loc b) UsePerm" in subst)
      apply (rule_tac diff_add_rem_use_env)
     apply (rule_tac dist_add_leq_use_env)
     apply (simp)
    apply (rule_tac add_pwrite_leq_use_env)
      apply (rule_tac r_s="r_s1" in sw_leq_use_env)
       apply (rule_tac r_sb="diff_use_env r_s1 r_ex" in trans_leq_use_env)
        apply (rule_tac self_diff_leq_use_env)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (auto)
    apply (rule_tac dist_add_leq_use_env)
    apply (simp)
   apply (rule_tac rhs_add_leq_use_env)
    apply (rule_tac rem_leq_use_env)
    apply (simp)
   apply (simp add: rem_use_env_def)
  apply (simp add: pwrite_use_env_def)
  apply (rule_tac t="diff_use_env (add_use_env rxa (Loc b) UsePerm) (rem_use_env r_ex (Loc b))" and
      s="add_use_env (diff_use_env rxa r_ex) (Loc b) UsePerm" in subst)
   apply (rule_tac diff_add_rem_use_env)
  apply (rule_tac dist_add_leq_use_env)
  apply (simp)
  done
    
lemma wtae_end_leq_use_env1: "\<lbrakk> leq_use_env r_x (diff_use_env r_s (comp_use_env r_exa r_exb)); r_exa x \<noteq> OwnPerm \<rbrakk> \<Longrightarrow>
  leq_use_env (add_use_env r_x x UsePerm) (diff_use_env (add_use_env r_s x UsePerm) (comp_use_env r_exa (rem_use_env r_exb x)))"    
  apply (rule_tac r_sb="diff_use_env (add_use_env r_s x UsePerm) (rem_use_env (comp_use_env r_exa r_exb) x)" in trans_leq_use_env)
   apply (simp add: dist_rem_comp_use_env)
   apply (rule_tac unroll_dcl_use_env)
   apply (rule_tac dist_diff_leq_use_env)
   apply (rule_tac rhs_diff_rem_leq_use_env2)
    apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac t="diff_use_env (add_use_env r_s x UsePerm) (rem_use_env (comp_use_env r_exa r_exb) x)"
      and s="add_use_env (diff_use_env r_s (comp_use_env r_exa r_exb)) x UsePerm" in subst)
   apply (rule_tac diff_add_rem_use_env)
  apply (rule_tac dist_add_leq_use_env)
  apply (simp)
  done
    
lemma wtae_req_leq_use_env1: "\<lbrakk> leq_use_env (diff_use_env r_x (comp_use_env r_exa r_exb)) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env (add_use_env r_x x UsePerm) (comp_use_env r_exa (rem_use_env r_exb x))) (add_use_env r_s x UsePerm)"
  apply (rule_tac r_sb="diff_use_env (add_use_env r_x x UsePerm) (rem_use_env (comp_use_env r_exa r_exb) x)" in trans_leq_use_env)
   apply (rule_tac t="diff_use_env (add_use_env r_x x UsePerm) (rem_use_env (comp_use_env r_exa r_exb) x)"
      and s="add_use_env (diff_use_env r_x (comp_use_env r_exa r_exb)) x UsePerm" in subst)
    apply (rule_tac diff_add_rem_use_env)
   apply (rule_tac dist_add_leq_use_env)
   apply (simp)
  apply (rule_tac dist_diff_leq_use_env_gen)
   apply (rule_tac id_leq_use_env)
  apply (simp add: dist_rem_comp_use_env)
  apply (rule_tac dist_comp_leq_use_env)
   apply (rule_tac comp_leq_use_env1)
   apply (rule_tac self_rem_leq_use_env)
  apply (rule_tac self_comp_leq_use_env2)
  done
    
lemma water_app_case: "\<lbrakk>\<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e1 tau r_s2 rx; semi_weak_use_env r_s1 r_set; env (Loc b) = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 (Loc b) UsePerm) (set_own e1 b) tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx r_set b);
        \<And>env r_s1 tau r_s2 rx.
           \<lbrakk>well_typed env r_s1 e2 tau r_s2 rx; semi_weak_use_env r_s1 r_set; env (Loc b) = Some t\<rbrakk>
           \<Longrightarrow> well_typed env (add_use_env r_s1 (Loc b) UsePerm) (set_own e2 b) tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx r_set b);
        semi_weak_use_env r_s1 r_set; b \<in> r_set; env (Loc b) = Some t; mem_ty t; ann_vars e1 \<subseteq> r_set; ann_vars e2 \<subseteq> r_set;
        well_typed env r_s1 e1 (FunTy t1 tau r a) r_s2a rx1; well_typed env r_s2a e2 t1 r_s3 rx2;
        leq_use_env r_s2 (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex));
        leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3; disj_use_env rx1 (lift_use_env rx2 r); leq_use_env rx r_s2; leq_use_env r_ex r_s1;
        leq_use_env (app_req rx1 rx2 r tau r_ex) rx\<rbrakk>
       \<Longrightarrow> \<exists>t1 r a r_s2a rx1.
              well_typed env (add_use_env r_s1 (Loc b) UsePerm) (set_own e1 b) (FunTy t1 tau r a) r_s2a rx1 \<and>
              (\<exists>rx2 r_s3. well_typed env r_s2a (set_own e2 b) t1 r_s3 rx2 \<and>
                          (\<exists>r_ex. leq_use_env (add_use_env r_s2 (Loc b) UsePerm) (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)) \<and>
                                  leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3 \<and>
                                  disj_use_env rx1 (lift_use_env rx2 r) \<and>
                                  leq_use_env (pwrite_use_env rx r_set b) (add_use_env r_s2 (Loc b) UsePerm) \<and>
                                  leq_use_env r_ex (add_use_env r_s1 (Loc b) UsePerm) \<and> leq_use_env (app_req rx1 rx2 r tau r_ex) (pwrite_use_env rx r_set b)))"    
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="r" in exI)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="add_use_env r_s2a (Loc b) UsePerm" in exI)
  apply (rule_tac x="pwrite_use_env rx1 r_set b" in exI)
  apply (auto)
  apply (rule_tac x="pwrite_use_env rx2 r_set b" in exI)
  apply (rule_tac x="add_use_env r_s3 (Loc b) UsePerm" in exI)
  apply (auto)
   apply (cut_tac r_x="r_s2a" and r_s="r_s1" in sw_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
    apply (auto)
  apply (cut_tac r_sc="r_s3" and r_sb="r_s2a" and r_sa="r_s1" in trans_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  apply (cut_tac r_sc="r_s2" and r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" and r_sa="r_s1" in trans_leq_use_env)
    apply (rule_tac diff_leq_use_env)
    apply (auto)
  apply (cut_tac r_x="lift_use_env rx2 r" and r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (auto)
    apply (rule_tac self_comp_leq_use_env2)
  apply (cut_tac r_x="rx1" and r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (auto)
    apply (rule_tac self_comp_leq_use_env1)
  apply (rule_tac t="lift_use_env (pwrite_use_env rx2 r_set b) r" and s="pwrite_use_env (lift_use_env rx2 r) r_set b" in subst)
   apply (rule_tac lift_pwrite_use_env)
   apply (simp)
  apply (simp add: pwrite_comp_use_env)
  apply (rule_tac x="rem_use_env r_ex (Loc b)" in exI)
  apply (auto)
       apply (rule_tac wtae_end_leq_use_env1)
        apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
         apply (rule_tac unroll_dcl_use_env)
         apply (rule_tac dist_diff_leq_use_env)
         apply (rule_tac rhs_pwrite_diff_leq_use_env)
         apply (rule_tac id_leq_use_env)
        apply (simp)
       apply (simp add: pwrite_use_env_def)
       apply (auto)
        apply (cut_tac r_x="comp_use_env rx1 (lift_use_env rx2 r)" and r_s="r_s1" and x="Loc b" in leq_use_no_own)
          apply (simp add: semi_weak_use_env_def)
         apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
          apply (auto)
       apply (simp add: add_use_env_def)
      apply (rule_tac add_pwrite_leq_use_env)
        apply (rule_tac r_s="r_s1" in sw_leq_use_env)
         apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
          apply (auto)
      apply (rule_tac dist_add_leq_use_env)
      apply (simp)
     apply (rule_tac disj_pwrite_use_env)
        apply (auto)
    apply (rule_tac add_pwrite_leq_use_env)
      apply (rule_tac r_s="r_s1" in sw_leq_use_env)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (auto)
    apply (rule_tac dist_add_leq_use_env)
    apply (simp)
   apply (rule_tac rhs_add_leq_use_env)
    apply (rule_tac rem_leq_use_env)
    apply (simp)
   apply (simp add: rem_use_env_def)
  apply (simp add: app_req_def)
  apply (auto)
   apply (rule_tac leq_empty_use_env)
  apply (rule_tac t="lift_use_env (pwrite_use_env rx2 r_set b) r" and s="pwrite_use_env (lift_use_env rx2 r) r_set b" in subst)
   apply (rule_tac lift_pwrite_use_env)
   apply (simp)
  apply (cut_tac r_x="rx2" and r_s="lift_use_env rx2 r" in sw_leq_use_env)
    apply (rule_tac self_lift_leq_use_env)
   apply (simp)
  apply (simp add: pwrite_comp_use_env)
  apply (case_tac "\<not> set_use_none (comp_use_env rx1 rx2) r_set")
   apply (case_tac "pwrite_use_env (comp_use_env rx1 rx2) r_set b \<noteq> add_use_env (comp_use_env rx1 rx2) (Loc b) UsePerm")
    apply (simp add: pwrite_use_env_def)
   apply (auto)
   apply (case_tac "set_use_none rx r_set")
    apply (simp add: set_use_none_def)
    apply (auto)
    apply (cut_tac r_x="comp_use_env rx1 rx2" and r_s="rx" and r_ex="comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex" and x="x" in rhs_sw_leq_use_none)
        apply (auto)
    apply (rule_tac r_s="r_s1" in sw_leq_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
       apply (auto)
   apply (case_tac "pwrite_use_env rx r_set b \<noteq> add_use_env rx (Loc b) UsePerm")
    apply (simp add: pwrite_use_env_def)
   apply (auto)
   apply (rule_tac wtae_req_leq_use_env1)
   apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
    apply (simp)
   apply (rule_tac unroll_dcl_use_env)
   apply (rule_tac dist_diff_leq_use_env)
   apply (rule_tac dist_diff_leq_use_env_gen)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac pwrite_leq_use_env)
     apply (rule_tac r_s="r_s1" in sw_leq_use_env)
      apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
       apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (case_tac "pwrite_use_env (comp_use_env rx1 rx2) r_set b \<noteq> comp_use_env rx1 rx2")
   apply (simp add: pwrite_use_env_def)
  apply (auto)
  apply (rule_tac pwrite_leq_use_env)
    apply (rule_tac sw_leq_use_env)
     apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
      apply (auto)
  apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac unroll_dcl_use_env)
  apply (rule_tac rhs_diff_rem_leq_use_env2)
   apply (rule_tac r_s="r_s1" in leq_use_no_own)
    apply (simp add: semi_weak_use_env_def)
   apply (simp)
  apply (rule_tac dist_diff_leq_use_env)
  apply (rule_tac dist_diff_leq_use_env_gen)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac pwrite_leq_use_env)
    apply (rule_tac r_s="r_s1" in sw_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (auto)
  apply (rule_tac id_leq_use_env) 
  done
    
lemma well_typed_set_own_rep: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx;
  ann_vars e \<subseteq> r_set; semi_weak_use_env r_s1 r_set; b \<in> r_set; env (Loc b) = Some t; mem_ty t \<rbrakk> \<Longrightarrow>
  well_typed env (add_use_env r_s1 (Loc b) UsePerm) (set_own e b) tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx r_set b)"      
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
    (* const + op cases *)
           apply (rule_tac dist_add_leq_use_env)
            apply (auto)
          apply (rule_tac add_pwrite_leq_use_env)
           apply (rule_tac r_s="r_s1" in sw_leq_use_env)
           apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
            apply (auto)
          apply (rule_tac dist_add_leq_use_env)
          apply (auto)
         apply (rule_tac dist_add_leq_use_env)
         apply (auto)
        apply (rule_tac add_pwrite_leq_use_env)
         apply (rule_tac r_s="r_s1" in sw_leq_use_env)
           apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
            apply (auto)
        apply (rule_tac dist_add_leq_use_env)
        apply (auto)
    (* var case. *)
      apply (rule_tac water_var_case)
                  apply (auto)
    (* pair case. *)
     apply (rule_tac water_pair_case)
                      apply (auto)
    (* if case *)
    apply (rule_tac water_if_case)
                apply (auto)
    (* lam case *)
   apply (rule_tac water_lam_case)
               apply (auto)
    (* app case *)
  apply (rule_tac water_app_case)
                 apply (auto)
  done  
  
lemma wtae_diff_use_env: "\<lbrakk> strong_use_env r_s \<rbrakk> \<Longrightarrow> diff_use_env (add_use_env r_s x UsePerm) (rem_use_env r_s x) = one_use_env x UsePerm"    
  apply (case_tac "\<forall> y. diff_use_env (add_use_env r_s x UsePerm) (rem_use_env r_s x) y = one_use_env x UsePerm y")
   apply (auto)
  apply (simp add: one_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: strong_use_env_def)
  apply (case_tac "x = y")
   apply (auto)
  apply (erule_tac x="y" in allE)
  apply (case_tac "r_s y")
    apply (auto)
  done    
  
lemma well_typed_set_own: "\<lbrakk> well_typed env r_x e tau r_x r_x; is_value e;
  env (Loc b) = Some t; mem_ty t; unlim tau; r_s (Loc b) \<noteq> NoPerm; mem_val_env env; sub_env s env \<rbrakk> \<Longrightarrow>
  well_typed env r_s (set_own e b) tau r_s (one_use_env (Loc b) UsePerm)"    
    (* to prove that ack_exp works with arbitrary permissions, we want to prove that it works with just x. *)
  apply (rule_tac r_s="one_use_env (Loc b) UsePerm" in well_typed_incr_simul_perm)
   apply (simp add: leq_use_env_def)
   apply (simp add: one_use_env_def)
   apply (case_tac "r_s (Loc b)")
     apply (auto)
    (* call the induction hypothesis *)
  apply (cut_tac env="env" and ?r_s1.0="drop_use_env r_x" and e="e" and tau="tau" and
        ?r_s2.0="drop_use_env r_x" and rx="drop_use_env r_x" and b="b" and r_set="{b} \<union> ann_vars e" and
        t="t" in well_typed_set_own_rep)    
        apply (rule_tac wt_sexp_drop_all)
          apply (auto)
     apply (simp add: unlim_def)
    apply (rule_tac value_is_sexp)
    apply (simp)
   apply (rule_tac semi_weak_drop_use_env)
    (* to reduce r_x to just b, we must invoke the diff lemma *)
  apply (cut_tac eq_own)
  apply (auto)
  apply (rule_tac t="one_use_env (Loc b) UsePerm" and s="diff_use_env (add_use_env (lift_use_env r_x r) (Loc b) UsePerm)
    (rem_use_env (lift_use_env r_x r) (Loc b))" in subst)
   apply (rule_tac wtae_diff_use_env)
   apply (rule_tac strong_lift_use_env)
   apply (simp)
    (* permission manipulation *)
  apply (rule_tac well_typed_diff_perms)
   apply (rule_tac rx="pwrite_use_env (drop_use_env r_x) (insert b (ann_vars e)) b" in well_typed_incr_req)
     apply (rule_tac r_s="add_use_env (drop_use_env r_x) (Loc b) UsePerm" in well_typed_incr_simul_perm)
      apply (rule_tac dist_add_leq_use_env)
      apply (rule_tac drop_leq_use_env)
      apply (rule_tac self_lift_leq_use_env)
     apply (simp)
    (* proving requirements change was valid *)
    apply (rule_tac add_pwrite_leq_use_env)
      apply (rule_tac semi_weak_drop_use_env)
     apply (auto)
    apply (rule_tac dist_add_leq_use_env)
    apply (rule_tac drop_leq_use_env)
    apply (rule_tac self_lift_leq_use_env)
   apply (rule_tac id_leq_use_env)
    (* proving that the diff was valid, which should be true since b is the only non-prim var. say that x \<noteq> b *)
  apply (case_tac "x \<noteq> Loc b")
   apply (auto)
   apply (case_tac x)
    apply (auto)
    (* - say that x is a var. then it must be in the env, which is impossible since env is under some s *)
    apply (simp add: non_prim_vars_def)
    apply (simp add: non_prim_entry_def)
    apply (simp add: sub_env_def)
    apply (erule_tac x="Var x1" in allE)
    apply (auto)
    (* - otherwise, x is a res var in set_own, which means it must be an ann var, which is impossible *)
   apply (simp add: non_prim_vars_def)
   apply (auto)
   apply (cut_tac x="x2" and e="set_own e b" in ann_res_vars)
    apply (auto)
   apply (cut_tac x="x2" and e="e" and b="b" in well_typed_set_own_ann_vars)
     apply (auto)
    (* - then x = b, which is fine *)
  apply (simp add: own_env_vars_def)
  apply (simp add: rem_use_env_def)
  done
    
    (* ##### other set_own lemmas *)
    
lemma set_own_value: "\<lbrakk> is_value v \<rbrakk> \<Longrightarrow> is_value (set_own v b)"    
  apply (induct v)
        apply (auto)
   apply (case_tac x)
    apply (auto)
  apply (case_tac v1)
        apply (auto)
  done
    
    (* a permission env is "proper" relative to x if every location used cen be found from x. *)
    
definition proper_use_env where
  "proper_use_env rs_map x e r_s = (\<forall> y. (y \<in> ref_vars e \<and> r_s (Loc y) \<noteq> NoPerm) \<longrightarrow> (\<exists> l. path_lookup rs_map x l y))"
  
lemma leq_proper_use_env: "\<lbrakk> proper_use_env rs_map x e r_s; leq_use_env r_x r_s; ref_vars e' \<subseteq> ref_vars e \<rbrakk> \<Longrightarrow> proper_use_env rs_map x e' r_x"
  apply (simp add: proper_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="Loc y" in allE)
  apply (auto)
  apply (case_tac "r_x (Loc y)")
    apply (auto)
  done
  
lemma add_proper_use_env: "\<lbrakk> proper_use_env rs_map x e r_s \<rbrakk> \<Longrightarrow>
  proper_use_env rs_map x e (add_use_env r_s (Var y) r)"    
  apply (simp add: proper_use_env_def)
  apply (simp add: add_use_env_def)
  done    
    
lemma proper_set_own_ih: "\<lbrakk> proper_use_env rs_map b e r_s; proper_exp rs_map e;
   well_typed env r_s e tau r_se r_xe \<rbrakk> \<Longrightarrow> proper_exp rs_map (set_own e b)"    
  apply (induct e arbitrary: env r_s tau r_se r_xe)
        apply (auto)
    (* var case. we first posit that there is a path between b \<leadsto> x22 *)
      apply (case_tac "x")
       apply (auto)
      apply (simp add: proper_exp_def)
      apply (case_tac "\<not> (\<exists> l. path_lookup rs_map b l x22)")
       apply (simp add: proper_use_env_def)
       apply (erule_tac x="x22" in allE)
       apply (auto)
       apply (cut_tac r_x="ereq_use_env (Loc x22) tau_x" and r_s="r_s" and x="Loc x22" in leq_use_none)
         apply (simp_all)
       apply (simp add: ereq_use_env_def)
       apply (simp add: one_use_env_def)
       apply (simp add: end_req_perm_def)
    (* - we merge this with x22 \<leadsto> x21 *)
      apply (rule_tac x="la @ l" in exI)
      apply (rule_tac y="x22" in path_lookup_append)
       apply (auto)
    (* pair case *)
     apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_pair)
      apply (auto)
     apply (cut_tac r_x="r_s" and r_s="r_s" and rs_map="rs_map" and e="PairExp e1 e2" and e'="e1" and x="b" in leq_proper_use_env)
        apply (auto)
      apply (rule_tac id_leq_use_env)
     apply (cut_tac r_x="r_s2" and r_s="r_s" and rs_map="rs_map" and e="PairExp e1 e2" and e'="e2" and x="b" in leq_proper_use_env)
        apply (auto)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (simp add: proper_exp_def)
    (* if case *)
    apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" and ?e3.0="e3" in proper_if)
     apply (auto)
    apply (cut_tac r_x="r_s" and r_s="r_s" and rs_map="rs_map" and x="b" and e="IfExp e1 e2 e3" and e'="e1"  in leq_proper_use_env)
       apply (auto)
     apply (rule_tac id_leq_use_env)
    apply (cut_tac r_x="r_s2" and r_s="r_s" and rs_map="rs_map" and x="b" and e="IfExp e1 e2 e3" and e'="e2" in leq_proper_use_env)
       apply (auto)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (cut_tac r_x="r_s2" and r_s="r_s" and rs_map="rs_map" and x="b" and e="IfExp e1 e2 e3" and e'="e3"  in leq_proper_use_env)
      apply (auto)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (simp add: proper_exp_def)
    (* lam case *)
   apply (cut_tac r_s="rx" and rs_map="rs_map" and e="e" and x="b" and y="x1a" and r="r" in add_proper_use_env)
     apply (rule_tac r_s="r_s" and e="e" in leq_proper_use_env)
       apply (simp add: proper_use_env_def)
      apply (auto)
   apply (simp add: proper_exp_def)
    (* app case *)
  apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_app)
   apply (auto)
  apply (cut_tac r_x="r_s" and r_s="r_s" and rs_map="rs_map" and e="AppExp e1 e2" and e'="e1" and x="b" in leq_proper_use_env)
     apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (cut_tac r_x="r_s2" and r_s="r_s" and rs_map="rs_map" and e="AppExp e1 e2" and e'="e2" and x="b" in leq_proper_use_env)
     apply (auto)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  apply (simp add: proper_exp_def)
  done    
    
lemma proper_set_own: "\<lbrakk> path_lookup rs_map b l a; rs_map a = Some r_s;
  proper_exp rs_map e; mem_val_env env;
  well_typed env r_s e tau r_se r_xe \<rbrakk> \<Longrightarrow> proper_exp rs_map (set_own e b)"   
  apply (rule_tac env="env" and r_s="r_s" and r_se="r_se" and tau="tau" and r_xe="r_xe" in proper_set_own_ih)
    (* we expect everything from r_s1 to be contained in the completion of rs_map since
        r_s1 is derived from some resource y, where there is a path from x to y *)
    apply (simp add: proper_use_env_def)
    apply (auto)
  apply (rule_tac x="l @ [y]" in exI)
  apply (rule_tac y="a" in path_lookup_append)
   apply (auto)
  done
    
*)
  

definition ref_memory where
  "ref_memory env = (\<forall> x. case env (Loc x) of
    None \<Rightarrow> True
    | Some tau \<Rightarrow> req_type tau = Ref)"
  
    (* we want to prove that when you read a value from an array, it will fit into the new delta.
        we believe this to be true in the same sense that set_own is true. that replacing every single
        permission with {b: *} should be acceptable.
    *)
  
    (*
lemma well_typed_set_own: "\<lbrakk> well_typed env r_x e tau r_x r_x; is_value e;
  env (Loc b) = Some t; mem_ty t; unlim tau; r_s (Loc b) \<noteq> NoPerm; mem_val_env env; sub_env s env \<rbrakk> \<Longrightarrow>
  well_typed env r_s (set_own e b) tau r_s (one_use_env (Loc b) UsePerm)"  
    *)
  

definition semi_weak_use_env where
  "semi_weak_use_env r_s = (\<forall> x. case x of
    Var x \<Rightarrow> True
    | Loc y \<Rightarrow> r_s (Loc y) \<noteq> OwnPerm
  )"    
  
lemma sw_leq_use_env: "\<lbrakk> leq_use_env r_x r_s; semi_weak_use_env r_s \<rbrakk> \<Longrightarrow> semi_weak_use_env r_x"  
  apply (simp add: semi_weak_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)  
  apply (case_tac x)
   apply (auto)
  apply (case_tac "r_s (Loc x2)")
    apply (auto)    
  done      
(*
lemma sw_add_use_env: "\<lbrakk> semi_weak_use_env r_s \<rbrakk> \<Longrightarrow> semi_weak_use_env (add_use_env r_s (Loc x) r)"    
  apply (simp add: semi_weak_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (case_tac xa)
   apply (auto)
  apply (simp add: add_use_env_def)
  apply (case_tac "x = x2")
   apply (auto)
    
  done*)
  
lemma sw_add_use_env: "\<lbrakk> semi_weak_use_env r_s \<rbrakk> \<Longrightarrow> semi_weak_use_env (add_use_env r_s (Var x) r)"    
  apply (simp add: semi_weak_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (case_tac xa)
   apply (auto)
  apply (simp add: add_use_env_def)
  done
    
lemma rhs_sw_leq_use_none: "\<lbrakk> leq_use_env (diff_use_env r_x r_ex) r_s; r_s (Loc x) = NoPerm; semi_weak_use_env r_ex  \<rbrakk> \<Longrightarrow> r_x (Loc x) = NoPerm"    
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: semi_weak_use_env_def)
  apply (erule_tac x="Loc x" in allE)
  apply (erule_tac x="Loc x" in allE)
  apply (auto)
  apply (case_tac "r_x (Loc x)")
    apply (auto)
   apply (case_tac "r_ex (Loc x)")
     apply (auto)
  apply (case_tac "r_ex (Loc x)")
    apply (auto)
  done 
    
lemma semi_weak_drop_use_env: "semi_weak_use_env (drop_use_env r_s)"    
  apply (simp add: semi_weak_use_env_def)
  apply (auto)
  apply (case_tac x)
   apply (auto)
  apply (simp add: drop_use_env_def)
  apply (case_tac "r_s (Loc x2)")
    apply (auto)
  done      
  
definition any_loc_use where
  "any_loc_use r_s = (\<exists> x. r_s (Loc x) \<noteq> NoPerm)"
  
definition pwrite_use_env :: "perm_use_env \<Rightarrow> string \<Rightarrow> perm_use_env" where
  "pwrite_use_env r_s x = (if \<not> any_loc_use r_s then r_s else add_use_env r_s (Loc x) UsePerm)"  

lemma leq_any_loc_use: "\<lbrakk> leq_use_env r_x r_s; any_loc_use r_x \<rbrakk> \<Longrightarrow> any_loc_use r_s"  
  apply (simp add: any_loc_use_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (rule_tac x="x" in exI)
  apply (erule_tac x="Loc x" in allE)
  apply (case_tac "r_x (Loc x)")
    apply (auto)
  done     
  
lemma dist_pwrite_leq_use_env: "\<lbrakk> semi_weak_use_env r_s; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (pwrite_use_env r_x x) (pwrite_use_env r_s x)"
  apply (case_tac "any_loc_use r_x")
   apply (simp add: pwrite_use_env_def)
    apply (auto)
    apply (cut_tac r_x="r_x" and r_s="r_s" in leq_any_loc_use)
      apply (auto)
   apply (rule_tac dist_add_leq_use_env)
   apply (simp)
  apply (simp add: pwrite_use_env_def)
  apply (auto)
  apply (rule_tac rhs_add_leq_use_env)
  apply (simp)
  apply (case_tac "r_x (Loc x)")
    apply (auto)
  apply (cut_tac r_x="r_x" and r_s="r_s" and x="Loc x" in leq_use_no_own)
    apply (auto)
  apply (simp add: semi_weak_use_env_def)
  apply (erule_tac x="Loc x" in allE)
  apply (auto)
  done
 
lemma rem_pwrite_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (rem_use_env r_x (Loc x)) (pwrite_use_env r_s x)"       
  apply (simp add: pwrite_use_env_def)
  apply (auto)
   apply (rule_tac rem_leq_use_env)
   apply (simp)
  apply (rule_tac rhs_add_leq_use_env)
   apply (rule_tac rem_leq_use_env)
   apply (simp)
  apply (simp add: rem_use_env_def)
  done
  
lemma pwrite_leq_use_env: "\<lbrakk> semi_weak_use_env r_s; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x (pwrite_use_env r_s x)"    
  apply (simp add: pwrite_use_env_def)
  apply (auto)
  apply (rule_tac rhs_add_leq_use_env)
   apply (simp)
  apply (case_tac "r_x (Loc x)")
    apply (auto)
  apply (cut_tac r_x="r_x" and r_s="r_s" and x="Loc x" in leq_use_no_own)
    apply (auto)
  apply (simp add: semi_weak_use_env_def)
  apply (erule_tac x="Loc x" in allE)
  apply (auto)
  done
 
lemma add_pwrite_leq_use_env: "\<lbrakk> semi_weak_use_env r_x; leq_use_env (add_use_env r_x (Loc x) UsePerm) r_s \<rbrakk> \<Longrightarrow> leq_use_env (pwrite_use_env r_x x) r_s"      
  apply (simp add: pwrite_use_env_def)
  apply (auto)
  apply (rule_tac r_sb="add_use_env r_x (Loc x) UsePerm" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac rhs_add_leq_use_env)
   apply (rule_tac id_leq_use_env)
  apply (case_tac "r_x (Loc x)")
    apply (auto)
  apply (simp add: semi_weak_use_env_def)
  apply (erule_tac x="Loc x" in allE)
  apply (auto)
  done    
    
lemma lift_pwrite_leq_use_env: "\<lbrakk> semi_weak_use_env r_s; leq_use_env (lift_use_env r_x r) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (lift_use_env (pwrite_use_env r_x x) r) (add_use_env r_s (Loc x) UsePerm)"    
  apply (simp add: pwrite_use_env_def)
  apply (auto)
   apply (rule_tac rhs_add_leq_use_env)
    apply (simp)
   apply (cut_tac r_x="lift_use_env r_x r" and r_s="r_s" in sw_leq_use_env)
     apply (auto)
   apply (simp add: semi_weak_use_env_def)
   apply (erule_tac x="Loc x" in allE)
   apply (erule_tac x="Loc x" in allE)
   apply (auto)
   apply (case_tac "lift_use_env r_x r (Loc x)")
     apply (auto)
  apply (case_tac "r = OwnPerm")
   apply (simp add: any_loc_use_def)
   apply (auto)
   apply (case_tac "r_s (Loc xa) = OwnPerm")
    apply (simp add: semi_weak_use_env_def)
    apply (erule_tac x="Loc xa" in allE)
    apply (auto)
   apply (simp add: leq_use_env_def)
   apply (erule_tac x="Loc xa" in allE)
   apply (case_tac "r_s (Loc xa)")
     apply (auto)
  apply (case_tac "lift_use_env r_x r \<noteq> r_x")
   apply (case_tac r)
     apply (auto)
  apply (case_tac "lift_use_env (add_use_env r_x (Loc x) UsePerm) r \<noteq> add_use_env r_x (Loc x) UsePerm")
   apply (case_tac r)
     apply (auto)
  apply (rule_tac dist_add_leq_use_env)
  apply (simp)
  done    
    
lemma rhs_pwrite_diff_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env r_x r_ex) (diff_use_env r_s (pwrite_use_env r_ex x))"    
  apply (simp add: pwrite_use_env_def)
  apply (auto)
   apply (rule_tac dist_diff_leq_use_env)
   apply (simp)
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: add_use_env_def)
  apply (auto)
   apply (erule_tac x="Loc x" in allE)
   apply (simp add: any_loc_use_def)
   apply (case_tac "r_ex (Loc x)")
     apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (simp add: any_loc_use_def)
  apply (case_tac "r_ex xa")
    apply (auto)
  done

lemma disj_add_use_env_sw: "\<lbrakk> disj_use_env r_x r_s; semi_weak_use_env r_s \<rbrakk> \<Longrightarrow> disj_use_env (add_use_env r_x (Loc x) UsePerm) r_s"    
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: add_use_env_def)
  apply (auto)
  apply (simp add: semi_weak_use_env_def)
  apply (erule_tac x="Loc x" in allE)
  apply (erule_tac x="Loc x" in allE)
  apply (auto)
  done      
    
lemma disj_pwrite_use_env: "\<lbrakk> semi_weak_use_env r_x; semi_weak_use_env r_s; disj_use_env r_x r_s \<rbrakk> \<Longrightarrow>
  disj_use_env (pwrite_use_env r_x x) (pwrite_use_env r_s x)"   
  apply (simp add: pwrite_use_env_def)
  apply (auto)
    apply (rule_tac comm_disj_use_env)
    apply (rule_tac disj_add_use_env_sw)
    apply (rule_tac comm_disj_use_env)
     apply (auto)
   apply (rule_tac disj_add_use_env_sw)
    apply (auto)
  apply (rule_tac disj_add_use_env_sw)
   apply (rule_tac comm_disj_use_env)
   apply (rule_tac disj_add_use_env_sw)
    apply (rule_tac comm_disj_use_env)
    apply (auto)
  apply (simp add: semi_weak_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (erule_tac x="xa" in allE)
  apply (case_tac xa)
   apply (auto)
  apply (simp add: add_use_env_def)
  apply (case_tac "x = x2")
   apply (auto)
  done    
    
lemma disj_lift_pwrite_use_env: "\<lbrakk> disj_use_env (lift_use_env r_x r) (lift_use_env r_s r);
  leq_use_env (lift_use_env r_x r) r_c; leq_use_env (lift_use_env r_s r) r_c; semi_weak_use_env r_c \<rbrakk> \<Longrightarrow>
  disj_use_env (lift_use_env (pwrite_use_env r_x x) r) (lift_use_env (pwrite_use_env r_s x) r)"
    (* if r \<noteq> Own, then normal disjointness applies *)
  apply (case_tac "\<not> is_own r")
   apply (simp add: is_own_def)
   apply (case_tac r)
     apply (auto)
    apply (rule_tac disj_pwrite_use_env)
       apply (auto)
     apply (rule_tac r_s="r_c" in sw_leq_use_env)
      apply (auto)
    apply (rule_tac r_s="r_c" in sw_leq_use_env)
     apply (auto)
   apply (rule_tac disj_pwrite_use_env)
     apply (auto)
    apply (rule_tac r_s="r_c" in sw_leq_use_env)
     apply (auto)
   apply (rule_tac r_s="r_c" in sw_leq_use_env)
    apply (auto)
    (* otherwise, say that r_x uses Loc xa. then r_c (Loc xa) = Own, a contradiction *)
  apply (case_tac "any_loc_use r_x")
   apply (simp add: any_loc_use_def)
   apply (auto)
   apply (simp add: leq_use_env_def)
   apply (erule_tac x="Loc xa" in allE)
   apply (simp add: is_own_def)
   apply (simp add: semi_weak_use_env_def)
   apply (erule_tac x="Loc xa" in allE)
   apply (erule_tac x="Loc xa" in allE) 
   apply (case_tac "r_c (Loc xa)")
     apply (auto)
    (* same for r_s *)
  apply (case_tac "any_loc_use r_s")
   apply (simp add: any_loc_use_def)
   apply (auto)
   apply (simp add: leq_use_env_def)
   apply (erule_tac x="Loc xa" in allE)
   apply (erule_tac x="Loc xa" in allE)
   apply (simp add: semi_weak_use_env_def)
   apply (erule_tac x="Loc xa" in allE)
   apply (simp add: is_own_def)
   apply (case_tac "r_c (Loc xa)")
     apply (auto)
  apply (simp add: pwrite_use_env_def)
  done       
    
    (* - pwrite equality lemmas *)
    
lemma lift_pwrite_use_env: "\<lbrakk> semi_weak_use_env (lift_use_env r_s r) \<rbrakk> \<Longrightarrow>
  pwrite_use_env (lift_use_env r_s r) x = lift_use_env (pwrite_use_env r_s x) r"
  apply (case_tac "is_own r")
   apply (case_tac "any_loc_use r_s")
    apply (simp add: any_loc_use_def)
    apply (auto)
    apply (simp add: semi_weak_use_env_def)
    apply (simp add: is_own_def)
    apply (erule_tac x="Loc xa" in allE)
    apply (auto)
   apply (simp add: pwrite_use_env_def)
   apply (auto)
   apply (simp add: any_loc_use_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (simp add: is_own_def)
  apply (simp add: is_own_def)
  apply (case_tac r)
    apply (auto)
  done
    
lemma pwc_add_use_env1: "\<lbrakk> semi_weak_use_env r_x \<rbrakk> \<Longrightarrow> comp_use_env r_x (add_use_env r_s (Loc x) UsePerm) = add_use_env (comp_use_env r_x r_s) (Loc x) UsePerm"    
  apply (case_tac "\<forall> y. comp_use_env r_x (add_use_env r_s (Loc x) UsePerm) y = add_use_env (comp_use_env r_x r_s) (Loc x) UsePerm y")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: semi_weak_use_env_def)
  apply (erule_tac x="Loc x" in allE)
  apply (auto)
  apply (case_tac "Loc x = y")
   apply (auto)
  apply (case_tac "r_x (Loc x)")
    apply (auto)
  done

lemma pwc_add_use_env2: "\<lbrakk> semi_weak_use_env r_s \<rbrakk> \<Longrightarrow> comp_use_env (add_use_env r_x (Loc x) UsePerm) r_s = add_use_env (comp_use_env r_x r_s) (Loc x) UsePerm"    
  apply (case_tac "\<forall> y. comp_use_env (add_use_env r_x (Loc x) UsePerm) r_s y = add_use_env (comp_use_env r_x r_s) (Loc x) UsePerm y")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: semi_weak_use_env_def)
  apply (erule_tac x="Loc x" in allE)
  apply (auto)
  apply (case_tac "Loc x = y")
   apply (auto)
  apply (case_tac "r_s (Loc x)")
    apply (auto)
  done    

lemma pwrite_comp_use_env: "\<lbrakk> semi_weak_use_env r_x; semi_weak_use_env r_s \<rbrakk> \<Longrightarrow>
  comp_use_env (pwrite_use_env r_x x) (pwrite_use_env r_s x) = pwrite_use_env (comp_use_env r_x r_s) x"
  apply (case_tac "\<not> any_loc_use r_x")
   apply (case_tac "\<not> any_loc_use r_s")
    apply (simp add: pwrite_use_env_def)
    apply (auto)
    apply (simp add: any_loc_use_def)
    apply (simp add: comp_use_env_def)
   apply (simp add: pwrite_use_env_def)
   apply (auto)
    apply (simp add: any_loc_use_def)
    apply (simp add: comp_use_env_def)
    apply (auto)
    apply (erule_tac x="xa" in allE)
    apply (erule_tac x="xa" in allE)
    apply (case_tac "r_s (Loc xa)")
      apply (auto)
   apply (rule_tac pwc_add_use_env1)
   apply (auto)
  apply (case_tac "\<not> any_loc_use r_s")
   apply (simp add: pwrite_use_env_def)
   apply (auto)
    apply (simp add: any_loc_use_def)
    apply (simp add: comp_use_env_def)
    apply (auto)
    apply (erule_tac x="xa" in allE)
    apply (erule_tac x="xa" in allE)
    apply (case_tac "r_x (Loc xa)")
      apply (auto)
   apply (rule_tac pwc_add_use_env2)
   apply (auto)
  apply (simp add: pwrite_use_env_def)
  apply (auto)
   apply (simp add: any_loc_use_def)
   apply (simp add: comp_use_env_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (case_tac "r_x (Loc xa)")
     apply (auto)
   apply (case_tac "r_s (Loc xa)")
     apply (auto)
  apply (rule_tac dist_add_comp_use_env)
  done    

lemma diff_pwrite_rem_use_env: "\<lbrakk> semi_weak_use_env r_x \<rbrakk> \<Longrightarrow>
  diff_use_env (pwrite_use_env r_s x) (rem_use_env r_x (Loc x)) = pwrite_use_env (diff_use_env r_s r_x) x"    
  apply (case_tac "\<not> any_loc_use r_s")
   apply (simp add: pwrite_use_env_def)
   apply (auto)
   apply (simp add: any_loc_use_def)
    apply (case_tac "\<forall> y. diff_use_env r_s (rem_use_env r_x (Loc x)) y = diff_use_env r_s r_x y")
     apply (auto)
    apply (simp add: diff_use_env_def)
    apply (simp add: rem_use_env_def)
    apply (case_tac "Loc x = y")
     apply (auto)
   apply (simp add: any_loc_use_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (cut_tac r_x="diff_use_env r_s r_x" and r_s="r_s" and x="Loc xa" in leq_use_none)
     apply (auto)
   apply (rule_tac self_diff_leq_use_env)
  apply (simp add: pwrite_use_env_def)
  apply (auto)
   apply (simp add: any_loc_use_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (case_tac "r_x (Loc xa) \<noteq> OwnPerm")
    apply (simp add: diff_use_env_def)
    apply (case_tac "r_x (Loc xa)")
      apply (auto)
   apply (simp add: semi_weak_use_env_def)
   apply (erule_tac x="Loc xa" in allE)
   apply (auto)
  apply (simp add: semi_weak_use_env_def)
  apply (simp add: diff_add_rem_use_env)
  done 
  
definition rv_delta where
  "rv_delta delta e b = (\<forall> x. x \<in> ref_vars e \<longrightarrow> delta x = b)"  
  
lemma water_var_case: "\<lbrakk> semi_weak_use_env r_s1; env (Loc b) = Some t; mem_ty t; rv_delta delta' (VarExp x) b; mem_val_env env;
       env (res_name x) = Some tau;  env (owner_name delta x) = Some tau_x; leq_use_env (ereq_use_env (owner_name delta x) tau_x) r_s1;
       leq_use_env r_s2 (diff_use_env r_s1 (comp_use_env (ereq_use_env (owner_name delta x) tau_x) r_ex));
       leq_use_env rx r_s2;  leq_use_env r_ex r_s1;
       leq_use_env (diff_use_env (ereq_use_env (owner_name delta x) tau_x) (comp_use_env (ereq_use_env (owner_name delta x) tau_x) r_ex)) rx \<rbrakk> \<Longrightarrow>
       \<exists>r_ex tau_x.
          env (owner_name delta' x) = Some tau_x \<and>
          leq_use_env (ereq_use_env (owner_name delta' x) tau_x) (add_use_env r_s1 (Loc b) UsePerm) \<and>
          leq_use_env (add_use_env r_s2 (Loc b) UsePerm) (diff_use_env (add_use_env r_s1 (Loc b) UsePerm) (comp_use_env (ereq_use_env (owner_name delta' x) tau_x) r_ex)) \<and>
          leq_use_env (pwrite_use_env rx b) (add_use_env r_s2 (Loc b) UsePerm) \<and>
          leq_use_env r_ex (add_use_env r_s1 (Loc b) UsePerm) \<and>
          leq_use_env (diff_use_env (ereq_use_env (owner_name delta' x) tau_x) (comp_use_env (ereq_use_env (owner_name delta' x) tau_x) r_ex)) (pwrite_use_env rx b)"  
    (* var case. non-value *)
  apply (case_tac x)
   apply (auto)
    apply (rule_tac rhs_add_leq_use_env)
     apply (auto)
    apply (simp add: ereq_use_env_def)
    apply (simp add: one_use_env_def)
   apply (rule_tac x="rem_use_env r_ex (Loc b)" in exI)
   apply (auto)
      apply (rule_tac r_sb="diff_use_env (add_use_env r_s1 (Loc b) UsePerm) (rem_use_env (comp_use_env (ereq_use_env (Var x1) tau_x) r_ex) (Loc b))" in trans_leq_use_env)
       apply (simp add: dist_rem_comp_use_env)
       apply (rule_tac unroll_dcl_use_env)
       apply (rule_tac dist_diff_leq_use_env)
       apply (rule_tac rhs_diff_rem_leq_use_env2)
        apply (simp add: ereq_use_env_def)
        apply (simp add: one_use_env_def)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac t="diff_use_env (add_use_env r_s1 (Loc b) UsePerm) (rem_use_env (comp_use_env (ereq_use_env (Var x1) tau_x) r_ex) (Loc b))"
           and s="add_use_env (diff_use_env r_s1 (comp_use_env (ereq_use_env (Var x1) tau_x) r_ex)) (Loc b) UsePerm" in subst)
       apply (rule_tac diff_add_rem_use_env)
      apply (rule_tac dist_add_leq_use_env)
      apply (simp)
     apply (rule_tac add_pwrite_leq_use_env)
      apply (rule_tac r_s="r_s1" in sw_leq_use_env)
       apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env (Var x1) tau_x) r_ex)" in trans_leq_use_env)
        apply (rule_tac self_diff_leq_use_env)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (auto)
     apply (rule_tac dist_add_leq_use_env)
     apply (simp)
    apply (rule_tac rhs_add_leq_use_env)
     apply (rule_tac rem_leq_use_env)
     apply (simp)
    apply (simp add: rem_use_env_def)
   apply (rule_tac r_sb="diff_use_env (ereq_use_env (Var x1) tau_x) (comp_use_env (ereq_use_env (Var x1) tau_x) r_ex)" in trans_leq_use_env)
    apply (rule_tac pwrite_leq_use_env)
     apply (rule_tac r_s="r_s1" in sw_leq_use_env)
      apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env (Var x1) tau_x) r_ex)" in trans_leq_use_env)
       apply (rule_tac self_diff_leq_use_env)
      apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
       apply (auto)
   apply (rule_tac unroll_dcl_use_env)
   apply (rule_tac rhs_diff_rem_leq_use_env2)
    apply (cut_tac r_x="r_ex" and r_s="r_s1" in sw_leq_use_env)
      apply (simp)
     apply (auto)
    apply (simp add: semi_weak_use_env_def)
    apply (erule_tac x="Loc b" in allE)
    apply (erule_tac x="Loc b" in allE)
    apply (auto)
   apply (rule_tac id_leq_use_env)
    (* var case. value cases *)
  apply (case_tac "delta' x2 \<noteq> b")
   apply (simp add: rv_delta_def)
   apply (auto)
   apply (rule_tac ereq_leq_use_envx)
   apply (simp add: add_use_env_def)
   apply (simp add: end_req_perm_def)
   apply (case_tac t)
         apply (auto)
  apply (rule_tac x="rem_use_env r_ex (Loc b)" in exI)
  apply (auto)
     apply (rule_tac rhs_flip_use_env)
     apply (rule_tac rhs_unroll_dcl_use_env)
     apply (rule_tac rhs_weak_leq_use_env)
      apply (rule_tac weak_ereq_use_env)
      apply (simp add: unlim_def)
      apply (case_tac t)
            apply (auto)
     apply (rule_tac t="diff_use_env (add_use_env r_s1 (Loc (delta' x2)) UsePerm) (rem_use_env r_ex (Loc (delta' x2)))" and s="add_use_env (diff_use_env r_s1 r_ex) (Loc (delta' x2)) UsePerm" in subst)
      apply (rule_tac diff_add_rem_use_env)
     apply (rule_tac dist_add_leq_use_env)
     apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env (Loc (delta x2)) tau_x) r_ex)" in trans_leq_use_env)
      apply (rule_tac dist_diff_leq_use_env_gen)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac self_comp_leq_use_env2)
     apply (simp)
    apply (rule_tac add_pwrite_leq_use_env)
     apply (rule_tac r_s="r_s1" in sw_leq_use_env)
      apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env (Loc (delta x2)) tau_x) r_ex)" in trans_leq_use_env)
       apply (rule_tac self_diff_leq_use_env)
      apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
       apply (auto)
    apply (rule_tac dist_add_leq_use_env)
    apply (simp)
   apply (rule_tac rhs_add_leq_use_env)
    apply (rule_tac rem_leq_use_env)
    apply (simp)
   apply (simp add: rem_use_env_def)
    (* - req bound manipulation *)
  apply (simp add: pwrite_use_env_def)
  apply (auto)
    (* - say that we do not add a perm to rx. this means (delta x2) is not in rx, which is impossible since it is in r_s1 (and r_s1 is weak) *)
   apply (case_tac "rx (Loc (delta x2)) \<noteq> NoPerm")
    apply (simp add: any_loc_use_def)
   apply (case_tac "comp_use_env (ereq_use_env (Loc (delta x2)) tau_x) r_ex (Loc (delta x2)) = OwnPerm")
    apply (cut_tac r_x="comp_use_env (ereq_use_env (Loc (delta x2)) tau_x) r_ex" and r_s="r_s1" and x="Loc (delta x2)" in leq_use_own)
      apply (simp)
     apply (rule_tac dist_comp_leq_use_env)
      apply (simp_all)
    apply (simp add: semi_weak_use_env_def)
    apply (erule_tac x="Loc (delta x2)" in allE)
    apply (auto)
   apply (cut_tac r_x="ereq_use_env (Loc (delta x2)) tau_x" and r_ex="comp_use_env (ereq_use_env (Loc (delta x2)) tau_x) r_ex" and r_s="rx" and x="Loc (delta x2)" in diff_use_leq)
     apply (auto)
   apply (simp add: ereq_use_env_def)
   apply (simp add: one_use_env_def)
   apply (simp add: end_req_perm_def)
   apply (simp add: mem_val_env_def)
   apply (erule_tac x="Loc (delta x2)" in allE)
   apply (auto)
   apply (case_tac tau_x)
         apply (auto)
    (* - otherwise we know what x is *)
  apply (rule_tac diff_leq_use_env)
  apply (rule_tac ereq_leq_use_envx)
  apply (simp add: add_use_env_def)
  apply (simp add: end_req_perm_def)
  apply (case_tac t)
        apply (auto)  
  done
  
lemma water_pair_case: "\<lbrakk> \<And>env r_s1 tau r_s2 rx. \<lbrakk>
           well_typed env delta r_s1 e1 tau r_s2 rx;
           semi_weak_use_env r_s1; env (Loc b) = Some t; mem_val_env env; rv_delta delta' e1 b \<rbrakk> \<Longrightarrow>
              well_typed env delta' (add_use_env r_s1 (Loc b) UsePerm) e1 tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx b);
       \<And>env r_s1 tau r_s2 rx. \<lbrakk>
           well_typed env delta r_s1 e2 tau r_s2 rx; semi_weak_use_env r_s1; env (Loc b) = Some t; mem_val_env env; rv_delta delta' e2 b \<rbrakk> \<Longrightarrow>
              well_typed env delta' (add_use_env r_s1 (Loc b) UsePerm) e2 tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx b);
       semi_weak_use_env r_s1; env (Loc b) = Some t; mem_ty t; mem_val_env env; rv_delta delta' (PairExp e1 e2) b;
       well_typed env delta r_s1 e1 t1 r_s2a rx1; well_typed env delta r_s2a e2 t2 r_s3 rx2; leq_use_env (lift_use_env rx1 r) r_s3;
       leq_use_env (lift_use_env rx2 r) r_s3; aff_leq (max_aff (req_type t1) (req_type t2)) r; disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r);
       leq_use_env r_s2 (diff_use_env r_s3 r_ex); leq_use_env rx r_s2; leq_use_env r_ex r_s1;
       leq_use_env (pair_req (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex (PairTy t1 t2 r)) rx \<rbrakk> \<Longrightarrow>
       \<exists>r_s2a r_s3 rx1.
          well_typed env delta' (add_use_env r_s1 (Loc b) UsePerm) e1 t1 r_s2a rx1 \<and>
          (\<exists>rx2. well_typed env delta' r_s2a e2 t2 r_s3 rx2 \<and>
                 leq_use_env (lift_use_env rx1 r) r_s3 \<and>
                 leq_use_env (lift_use_env rx2 r) r_s3 \<and>
                 disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r) \<and>
                 (\<exists>r_ex. leq_use_env (add_use_env r_s2 (Loc b) UsePerm) (diff_use_env r_s3 r_ex) \<and>
                         leq_use_env (pwrite_use_env rx b) (add_use_env r_s2 (Loc b) UsePerm) \<and>
                         leq_use_env r_ex (add_use_env r_s1 (Loc b) UsePerm) \<and> leq_use_env (pair_req (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex (PairTy t1 t2 r)) (pwrite_use_env rx b)))"    
  apply (rule_tac x="add_use_env r_s2a (Loc b) UsePerm" in exI)
  apply (rule_tac x="add_use_env r_s3 (Loc b) UsePerm" in exI)
  apply (cut_tac r_sc="r_s3" and r_sb="r_s2a" and r_sa="r_s1" in trans_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  apply (cut_tac r_x="lift_use_env rx1 r" and r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
     apply (auto)
  apply (cut_tac r_x="lift_use_env rx2 r" and r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
     apply (auto)
  apply (rule_tac x="pwrite_use_env rx1 b" in exI)
  apply (auto)
   apply (case_tac "\<not> rv_delta delta' e1 b")
    apply (simp add: rv_delta_def)
   apply (auto)
  apply (rule_tac x="pwrite_use_env rx2 b" in exI)
  apply (auto)
      apply (case_tac "\<not> rv_delta delta' e2 b")
       apply (simp add: rv_delta_def)
      apply (auto)
      apply (cut_tac r_x="r_s2a" and r_s="r_s1" in sw_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
     apply (rule_tac lift_pwrite_leq_use_env)
      apply (rule_tac r_s="r_s1" in sw_leq_use_env)
       apply (auto)
    apply (rule_tac lift_pwrite_leq_use_env)
     apply (rule_tac r_s="r_s1" in sw_leq_use_env)
      apply (auto)
   apply (rule_tac r_c="r_s1" in disj_lift_pwrite_use_env)
       apply (auto)
    apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
     apply (auto)
   apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
    apply (auto)
  apply (rule_tac x="rem_use_env r_ex (Loc b)" in exI)
  apply (auto)
     apply (rule_tac t="diff_use_env (add_use_env r_s3 (Loc b) UsePerm) (rem_use_env r_ex (Loc b))"
          and s="add_use_env (diff_use_env r_s3 r_ex) (Loc b) UsePerm" in subst)
      apply (rule_tac diff_add_rem_use_env)
     apply (rule_tac dist_add_leq_use_env)
     apply (simp)
    apply (rule_tac add_pwrite_leq_use_env)
     apply (rule_tac r_s="r_s1" in sw_leq_use_env)
      apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
       apply (rule_tac diff_leq_use_env)
       apply (simp)
      apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
       apply (auto)
    apply (rule_tac dist_add_leq_use_env)
    apply (simp)
   apply (rule_tac rhs_add_leq_use_env)
    apply (rule_tac rem_leq_use_env)
    apply (auto)
   apply (simp add: rem_use_env_def)
  apply (case_tac "req_type (PairTy t1 t2 r) = Prim")
   apply (simp add: pair_req_def)
   apply (rule_tac leq_empty_use_env)
  apply (simp add: pair_req_def)
  apply (rule_tac t="lift_use_env (pwrite_use_env rx1 b) r" and s="pwrite_use_env (lift_use_env rx1 r) b" in subst)
   apply (rule_tac lift_pwrite_use_env)
   apply (rule_tac r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
     apply (auto)
  apply (rule_tac t="lift_use_env (pwrite_use_env rx2 b) r" and s="pwrite_use_env (lift_use_env rx2 r) b" in subst)
   apply (rule_tac lift_pwrite_use_env)
   apply (rule_tac r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
     apply (auto)
  apply (simp add: pwrite_comp_use_env)
  apply (cut_tac r_x="r_ex" and r_s="r_s1" in sw_leq_use_env)
    apply (auto)
  apply (simp add: diff_pwrite_rem_use_env)
  apply (rule_tac dist_pwrite_leq_use_env)
   apply (rule_tac r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
     apply (rule_tac diff_leq_use_env)
     apply (simp)
    apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
     apply (auto)
  done
    
lemma water_if_case: "\<lbrakk> \<And>env r_s1 tau r_s2 rx.
           \<lbrakk> well_typed env delta r_s1 e1 tau r_s2 rx; semi_weak_use_env r_s1; env (Loc b) = Some t; mem_val_env env; rv_delta delta' e1 b \<rbrakk> \<Longrightarrow>
            well_typed env delta' (add_use_env r_s1 (Loc b) UsePerm) e1 tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx b);
       \<And>env r_s1 tau r_s2 rx.
           \<lbrakk> well_typed env delta r_s1 e2 tau r_s2 rx; semi_weak_use_env r_s1; env (Loc b) = Some t; mem_val_env env; rv_delta delta' e2 b \<rbrakk> \<Longrightarrow>
            well_typed env delta' (add_use_env r_s1 (Loc b) UsePerm) e2 tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx b);
       \<And>env r_s1 tau r_s2 rx.
           \<lbrakk> well_typed env delta r_s1 e3 tau r_s2 rx; semi_weak_use_env r_s1; env (Loc b) = Some t; mem_val_env env; rv_delta delta' e3 b \<rbrakk> \<Longrightarrow>
            well_typed env delta' (add_use_env r_s1 (Loc b) UsePerm) e3 tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx b);
       semi_weak_use_env r_s1; env (Loc b) = Some t; mem_ty t; mem_val_env env; rv_delta delta' (IfExp e1 e2 e3) b;
       well_typed env delta r_s1 e1 BoolTy r_s2a rx'; well_typed env delta r_s2a e2 tau r_s2 rx1; well_typed env delta r_s2a e3 tau r_s2 rx2 \<rbrakk> \<Longrightarrow>
       \<exists>rx' r_s2a. well_typed env delta' (add_use_env r_s1 (Loc b) UsePerm) e1 BoolTy r_s2a rx' \<and>
                   (\<exists>rx1a. well_typed env delta' r_s2a e2 tau (add_use_env r_s2 (Loc b) UsePerm) rx1a \<and>
                           (\<exists>rx2a. well_typed env delta' r_s2a e3 tau (add_use_env r_s2 (Loc b) UsePerm) rx2a \<and> pwrite_use_env (comp_use_env rx1 rx2) b = comp_use_env rx1a rx2a))"    
  apply (rule_tac x="pwrite_use_env rx' b" in exI)
  apply (case_tac "\<not> (rv_delta delta' e1 b \<and> rv_delta delta' e2 b \<and> rv_delta delta' e3 b)")
   apply (simp add: rv_delta_def)
  apply (auto)
  apply (rule_tac x="add_use_env r_s2a (Loc b) UsePerm" in exI)
  apply (auto)
  apply (cut_tac r_x="r_s2a" and r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
  apply (rule_tac x="pwrite_use_env rx1 b" in exI)
  apply (auto)
  apply (rule_tac x="pwrite_use_env rx2 b" in exI)
  apply (auto)
  apply (cut_tac r_x="r_s2" and r_s="r_s2a" in sw_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
  apply (cut_tac r_x="rx1" and r_s="r_s2" in sw_leq_use_env)
    apply (rule_tac well_typed_perm_leqx)
    apply (auto)
  apply (cut_tac r_x="rx2" and r_s="r_s2" in sw_leq_use_env)
    apply (rule_tac well_typed_perm_leqx)
    apply (auto)
  apply (simp add: pwrite_comp_use_env)
  done
    
lemma wt_read_value_none: "\<lbrakk> ref_vars e = {}; well_typed env delta r_s1 e tau r_s2 rx \<rbrakk> \<Longrightarrow>
   well_typed env delta' r_s1 e tau r_s2 rx"    
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)  
        apply (auto)
    (* var case *)
      apply (case_tac x)
       apply (auto)
    (* pair case *)
     apply (rule_tac x="r_s2a" in exI)
     apply (rule_tac x="r_s3" in exI)
     apply (rule_tac x="rx1" in exI)
     apply (auto)
     apply (rule_tac x="rx2" in exI)
     apply (auto)
    (* if case *)
    apply (rule_tac x="rx'" in exI)
    apply (rule_tac x="r_s2a" in exI)
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
  done      

lemma wtae_end_leq_use_env2: "\<lbrakk> leq_use_env r_x (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow>
  leq_use_env (add_use_env r_x x UsePerm) (diff_use_env (add_use_env r_s x UsePerm) (rem_use_env r_ex x))"  
  apply (rule_tac t="diff_use_env (add_use_env r_s x UsePerm) (rem_use_env r_ex x)"
      and s="add_use_env (diff_use_env r_s r_ex) x UsePerm" in subst)
   apply (rule_tac diff_add_rem_use_env)
  apply (rule_tac dist_add_leq_use_env)
  apply (simp)  
  done    
    
definition not_ref_var where
  "not_ref_var x e = (x \<notin> ref_vars e)"
    
lemma well_typed_no_rv_use: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; mem_val_env env; r_s1 (Loc (delta x)) = NoPerm \<rbrakk> \<Longrightarrow> not_ref_var x e"    
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
    (* const + op cases *)
        apply (simp add: not_ref_var_def)
       apply (simp add: not_ref_var_def)
    (* var case *)
      apply (simp add: not_ref_var_def)
      apply (auto)
      apply (simp add: leq_use_env_def)
      apply (simp add: ereq_use_env_def)
      apply (simp add: one_use_env_def)
      apply (erule_tac x="Loc (delta x)" in allE)
      apply (case_tac xa)
       apply (auto)
      apply (simp add: mem_val_env_def)
      apply (erule_tac x="Loc (delta x)" in allE)
      apply (auto)
      apply (simp add: end_req_perm_def)
      apply (case_tac tau_x)
            apply (auto)
    (* pair case *)
     apply (simp add: not_ref_var_def)
     apply (cut_tac r_x="r_s2a" and r_s="r_s1" and x="Loc (delta x)" in leq_use_none)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
    (* if case *)
    apply (simp add: not_ref_var_def)
    apply (cut_tac r_x="r_s2a" and r_s="r_s1" and x="Loc (delta x)" in leq_use_none)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    (* lam case *)
   apply (simp add: not_ref_var_def)
   apply (cut_tac r_x="rxa" and r_s="r_s1" and x="Loc (delta x)" in leq_use_none)
     apply (auto)
   apply (case_tac "\<not> add_use_env rxa (Var x1a) r (Loc (delta x)) = NoPerm")
    apply (simp add: add_use_env_def)
   apply (case_tac "\<not> mem_val_env (add_env env (Var x1a) t1)")
    apply (cut_tac env="env" and x="x1a" and tau="t1" in add_mem_val_env)
     apply (auto)
   apply (iprover)
    (* app case *)
  apply (simp add: not_ref_var_def)
  apply (cut_tac r_x="r_s2a" and r_s="r_s1" and x="Loc (delta x)" in leq_use_none)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
  done        
    
lemma water_lam_case: "\<lbrakk> \<And>env r_s1 tau r_s2 rx.
           \<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; semi_weak_use_env r_s1; env (Loc b) = Some t; mem_val_env env; rv_delta delta' e b \<rbrakk> \<Longrightarrow>
            well_typed env delta' (add_use_env r_s1 (Loc b) UsePerm) e tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx b);
       semi_weak_use_env r_s1; env (Loc b) = Some t; mem_ty t; mem_val_env env; rv_delta delta' (LamExp x1a e) b;
       well_typed (add_env env (Var x1a) t1) delta (add_use_env rxa (Var x1a) r) e t2 r_s' r_end;
       aff_use_env rxa a; leq_use_env rxa r_s1; leq_use_env r_s2 (diff_use_env r_s1 r_ex);
       leq_use_env rx r_s2; leq_use_env r_ex r_s1; leq_use_env (diff_use_env rxa r_ex) rx \<rbrakk> \<Longrightarrow>
       \<exists>rxa. (\<exists>r_end r_s'. well_typed (add_env env (Var x1a) t1) delta' (add_use_env rxa (Var x1a) r) e t2 r_s' r_end) \<and>
             aff_use_env rxa a \<and>
             leq_use_env rxa (add_use_env r_s1 (Loc b) UsePerm) \<and>
             (\<exists>r_ex. leq_use_env (add_use_env r_s2 (Loc b) UsePerm) (diff_use_env (add_use_env r_s1 (Loc b) UsePerm) r_ex) \<and>
                     leq_use_env (pwrite_use_env rx b) (add_use_env r_s2 (Loc b) UsePerm) \<and>
                     leq_use_env r_ex (add_use_env r_s1 (Loc b) UsePerm) \<and> leq_use_env (diff_use_env rxa r_ex) (pwrite_use_env rx b))"    
    (* lam case. rxa does not contain any members of r_set *)
  apply (case_tac "\<not> rv_delta delta' e b")
   apply (simp add: rv_delta_def)
  apply (auto)
  apply (case_tac "\<not> any_loc_use rxa")
   apply (rule_tac x="rxa" in exI)
   apply (auto)
     apply (rule_tac x="r_end" in exI)
     apply (rule_tac x="r_s'" in exI)
     apply (rule_tac wt_read_value_none)
      apply (auto)
     apply (cut_tac env="add_env env (Var x1a) t1" and ?r_s1.0="add_use_env rxa (Var x1a) r" and x="x" and e="e" in well_typed_no_rv_use)
        apply (auto)
       apply (rule_tac add_mem_val_env)
       apply (auto)
      apply (simp add: add_use_env_def)
      apply (simp add: any_loc_use_def)
     apply (simp add: not_ref_var_def)
    apply (rule_tac rhs_add_leq_use_env)
     apply (simp)
    apply (simp add: any_loc_use_def)
   apply (rule_tac x="rem_use_env r_ex (Loc b)" in exI)
   apply (auto)
      apply (rule_tac wtae_end_leq_use_env2)
      apply (simp)
     apply (rule_tac add_pwrite_leq_use_env)
       apply (rule_tac r_s="r_s1" in sw_leq_use_env)
        apply (rule_tac r_sb="diff_use_env r_s1 r_ex" in trans_leq_use_env)
         apply (rule_tac self_diff_leq_use_env)
        apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
         apply (auto)
     apply (rule_tac dist_add_leq_use_env)
     apply (simp)
    apply (rule_tac rhs_add_leq_use_env)
     apply (rule_tac rem_leq_use_env)
     apply (simp)
    apply (simp add: rem_use_env_def)
   apply (rule_tac pwrite_leq_use_env)
     apply (rule_tac r_s="r_s1" in sw_leq_use_env)
      apply (rule_tac r_sb="diff_use_env r_s1 r_ex" in trans_leq_use_env)
       apply (rule_tac self_diff_leq_use_env)
      apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
       apply (auto)
   apply (rule_tac r_sb="diff_use_env rxa r_ex" in trans_leq_use_env)
    apply (simp)
    apply (rule_tac rhs_diff_rem_leq_use_env)
    apply (simp add: any_loc_use_def)
   apply (rule_tac id_leq_use_env)  
    (* lam case. rxa contains at least one member of r_set *)
    (* - prelim: rxa is not primitive *)
  apply (case_tac "a = Prim")
   apply (simp add: any_loc_use_def)
   apply (auto)
   apply (simp add: aff_use_env_def)
  apply (simp add: null_use_env_def)
    (* - prelim: rx has at least one value as well *)
  apply (case_tac "\<not> any_loc_use rx")
   apply (simp add: any_loc_use_def)
   apply (auto)
   apply (erule_tac x="x" in allE)
   apply (cut_tac r_ex="r_ex" and r_x="rxa" and r_s="rx" and x="x" in rhs_sw_leq_use_none)
       apply (auto)
   apply (rule_tac r_s="r_s1" in sw_leq_use_env)
    apply (auto)
    (* - prelim: x \<noteq> x1a *)
  apply (rule_tac x="add_use_env rxa (Loc b) UsePerm" in exI)
  apply (auto)
     apply (rule_tac x="pwrite_use_env r_end b" in exI)
     apply (rule_tac x="add_use_env r_s' (Loc b) UsePerm" in exI)
     apply (rule_tac t="add_use_env (add_use_env rxa (Loc b) UsePerm) (Var x1a) r" and s="add_use_env (add_use_env rxa (Var x1a) r) (Loc b) UsePerm" in subst)
      apply (simp add: almost_comm_add_use_env)
     apply (cut_tac r_s="rxa" and x="x1a" and r="r" in sw_add_use_env)
      apply (rule_tac r_s="r_s1" in sw_leq_use_env)
       apply (auto)
     apply (case_tac "\<not> add_env env (Var x1a) t1 (Loc b) = Some t")
      apply (simp add: add_env_def)
     apply (auto)
     apply (case_tac "\<not> mem_val_env (add_env env (Var x1a) t1)")
      apply (cut_tac env="env" and x="x1a" and tau="t1" in add_mem_val_env)
       apply (auto)
    apply (simp add: aff_use_env_def)
    apply (case_tac a)
      apply (auto)
    apply (simp add: weak_use_env_def)
    apply (simp add: add_use_env_def)
   apply (rule_tac dist_add_leq_use_env)
   apply (simp)
  apply (rule_tac x="rem_use_env r_ex (Loc b)" in exI)
  apply (auto)
     apply (rule_tac t="diff_use_env (add_use_env r_s1(Loc b) UsePerm) (rem_use_env r_ex (Loc b))" and
        s="add_use_env (diff_use_env r_s1 r_ex) (Loc b) UsePerm" in subst)
      apply (rule_tac diff_add_rem_use_env)
     apply (rule_tac dist_add_leq_use_env)
     apply (simp)
    apply (rule_tac add_pwrite_leq_use_env)
      apply (rule_tac r_s="r_s1" in sw_leq_use_env)
       apply (rule_tac r_sb="diff_use_env r_s1 r_ex" in trans_leq_use_env)
        apply (rule_tac self_diff_leq_use_env)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (auto)
    apply (rule_tac dist_add_leq_use_env)
    apply (simp)
   apply (rule_tac rhs_add_leq_use_env)
    apply (rule_tac rem_leq_use_env)
    apply (simp)
   apply (simp add: rem_use_env_def)
  apply (simp add: pwrite_use_env_def)
  apply (rule_tac t="diff_use_env (add_use_env rxa (Loc b) UsePerm) (rem_use_env r_ex (Loc b))" and
      s="add_use_env (diff_use_env rxa r_ex) (Loc b) UsePerm" in subst)
   apply (rule_tac diff_add_rem_use_env)
  apply (rule_tac dist_add_leq_use_env)
  apply (simp)
  done

lemma wtae_end_leq_use_env1: "\<lbrakk> leq_use_env r_x (diff_use_env r_s (comp_use_env r_exa r_exb)); r_exa x \<noteq> OwnPerm \<rbrakk> \<Longrightarrow>
  leq_use_env (add_use_env r_x x UsePerm) (diff_use_env (add_use_env r_s x UsePerm) (comp_use_env r_exa (rem_use_env r_exb x)))"    
  apply (rule_tac r_sb="diff_use_env (add_use_env r_s x UsePerm) (rem_use_env (comp_use_env r_exa r_exb) x)" in trans_leq_use_env)
   apply (simp add: dist_rem_comp_use_env)
   apply (rule_tac unroll_dcl_use_env)
   apply (rule_tac dist_diff_leq_use_env)
   apply (rule_tac rhs_diff_rem_leq_use_env2)
    apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac t="diff_use_env (add_use_env r_s x UsePerm) (rem_use_env (comp_use_env r_exa r_exb) x)"
      and s="add_use_env (diff_use_env r_s (comp_use_env r_exa r_exb)) x UsePerm" in subst)
   apply (rule_tac diff_add_rem_use_env)
  apply (rule_tac dist_add_leq_use_env)
  apply (simp)
  done    
    
lemma wtae_req_leq_use_env1: "\<lbrakk> leq_use_env (diff_use_env r_x (comp_use_env r_exa r_exb)) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env (add_use_env r_x x UsePerm) (comp_use_env r_exa (rem_use_env r_exb x))) (add_use_env r_s x UsePerm)"
  apply (rule_tac r_sb="diff_use_env (add_use_env r_x x UsePerm) (rem_use_env (comp_use_env r_exa r_exb) x)" in trans_leq_use_env)
   apply (rule_tac t="diff_use_env (add_use_env r_x x UsePerm) (rem_use_env (comp_use_env r_exa r_exb) x)"
      and s="add_use_env (diff_use_env r_x (comp_use_env r_exa r_exb)) x UsePerm" in subst)
    apply (rule_tac diff_add_rem_use_env)
   apply (rule_tac dist_add_leq_use_env)
   apply (simp)
  apply (rule_tac dist_diff_leq_use_env_gen)
   apply (rule_tac id_leq_use_env)
  apply (simp add: dist_rem_comp_use_env)
  apply (rule_tac dist_comp_leq_use_env)
   apply (rule_tac comp_leq_use_env1)
   apply (rule_tac self_rem_leq_use_env)
  apply (rule_tac self_comp_leq_use_env2)
  done
    
lemma water_app_case: "\<lbrakk> \<And>env r_s1 tau r_s2 rx.
           \<lbrakk> well_typed env delta r_s1 e1 tau r_s2 rx; semi_weak_use_env r_s1;  env (Loc b) = Some t; mem_val_env env; rv_delta delta' e1 b \<rbrakk> \<Longrightarrow>
            well_typed env delta' (add_use_env r_s1 (Loc b) UsePerm) e1 tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx b);
       \<And>env r_s1 tau r_s2 rx.
           \<lbrakk> well_typed env delta r_s1 e2 tau r_s2 rx; semi_weak_use_env r_s1; env (Loc b) = Some t; mem_val_env env; rv_delta delta' e2 b \<rbrakk> \<Longrightarrow>
            well_typed env delta' (add_use_env r_s1 (Loc b) UsePerm) e2 tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx b);
       semi_weak_use_env r_s1; env (Loc b) = Some t; mem_ty t; mem_val_env env; rv_delta delta' (AppExp e1 e2) b;
       well_typed env delta r_s1 e1 (FunTy t1 tau r a) r_s2a rx1; well_typed env delta r_s2a e2 t1 r_s3 rx2;
       leq_use_env r_s2 (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex));
       leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3; disj_use_env rx1 (lift_use_env rx2 r);
       leq_use_env rx r_s2; leq_use_env r_ex r_s1; leq_use_env (app_req rx1 rx2 r tau r_ex) rx \<rbrakk> \<Longrightarrow>
       \<exists>t1 r a r_s2a rx1.
          well_typed env delta' (add_use_env r_s1 (Loc b) UsePerm) e1 (FunTy t1 tau r a) r_s2a rx1 \<and>
          (\<exists>rx2 r_s3. well_typed env delta' r_s2a e2 t1 r_s3 rx2 \<and>
                      (\<exists>r_ex. leq_use_env (add_use_env r_s2 (Loc b) UsePerm) (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)) \<and>
                              leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3 \<and>
                              disj_use_env rx1 (lift_use_env rx2 r) \<and>
                              leq_use_env (pwrite_use_env rx b) (add_use_env r_s2 (Loc b) UsePerm) \<and>
                              leq_use_env r_ex (add_use_env r_s1 (Loc b) UsePerm) \<and> leq_use_env (app_req rx1 rx2 r tau r_ex) (pwrite_use_env rx b)))"    
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="r" in exI)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="add_use_env r_s2a (Loc b) UsePerm" in exI)
  apply (rule_tac x="pwrite_use_env rx1 b" in exI)
  apply (auto)
   apply (case_tac "\<not> rv_delta delta' e1 b")
    apply (simp add: rv_delta_def)
   apply (auto) 
  apply (rule_tac x="pwrite_use_env rx2 b" in exI)
  apply (rule_tac x="add_use_env r_s3 (Loc b) UsePerm" in exI)
  apply (auto)
   apply (case_tac "\<not> rv_delta delta' e2 b")
    apply (simp add: rv_delta_def)
   apply (auto)
   apply (cut_tac r_x="r_s2a" and r_s="r_s1" in sw_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
    apply (auto)
  apply (cut_tac r_sc="r_s3" and r_sb="r_s2a" and r_sa="r_s1" in trans_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  apply (cut_tac r_sc="r_s2" and r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" and r_sa="r_s1" in trans_leq_use_env)
    apply (rule_tac diff_leq_use_env)
    apply (auto)
  apply (cut_tac r_x="lift_use_env rx2 r" and r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (auto)
    apply (rule_tac self_comp_leq_use_env2)
  apply (cut_tac r_x="rx1" and r_s="r_s1" in sw_leq_use_env)
    apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (auto)
    apply (rule_tac self_comp_leq_use_env1)
  apply (rule_tac t="lift_use_env (pwrite_use_env rx2 b) r" and s="pwrite_use_env (lift_use_env rx2 r) b" in subst)
   apply (rule_tac lift_pwrite_use_env)
   apply (simp)
  apply (simp add: pwrite_comp_use_env)
  apply (rule_tac x="rem_use_env r_ex (Loc b)" in exI)
  apply (auto)
       apply (rule_tac wtae_end_leq_use_env1)
        apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
         apply (rule_tac unroll_dcl_use_env)
         apply (rule_tac dist_diff_leq_use_env)
         apply (rule_tac rhs_pwrite_diff_leq_use_env)
         apply (rule_tac id_leq_use_env)
        apply (simp)
       apply (simp add: pwrite_use_env_def)
       apply (auto)
        apply (simp add: any_loc_use_def)
       apply (simp add: add_use_env_def)
      apply (rule_tac add_pwrite_leq_use_env)
        apply (rule_tac r_s="r_s1" in sw_leq_use_env)
         apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
          apply (auto)
      apply (rule_tac dist_add_leq_use_env)
      apply (simp)
     apply (rule_tac disj_pwrite_use_env)
        apply (auto)
    apply (rule_tac add_pwrite_leq_use_env)
      apply (rule_tac r_s="r_s1" in sw_leq_use_env)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (auto)
    apply (rule_tac dist_add_leq_use_env)
    apply (simp)
   apply (rule_tac rhs_add_leq_use_env)
    apply (rule_tac rem_leq_use_env)
    apply (simp)
   apply (simp add: rem_use_env_def)
  apply (simp add: app_req_def)
  apply (auto)
   apply (rule_tac leq_empty_use_env)
  apply (rule_tac t="lift_use_env (pwrite_use_env rx2 b) r" and s="pwrite_use_env (lift_use_env rx2 r) b" in subst)
   apply (rule_tac lift_pwrite_use_env)
   apply (simp)
  apply (cut_tac r_x="rx2" and r_s="lift_use_env rx2 r" in sw_leq_use_env)
    apply (rule_tac self_lift_leq_use_env)
   apply (simp)
  apply (simp add: pwrite_comp_use_env)
  apply (case_tac "any_loc_use (comp_use_env rx1 rx2)")
   apply (case_tac "pwrite_use_env (comp_use_env rx1 rx2) b \<noteq> add_use_env (comp_use_env rx1 rx2) (Loc b) UsePerm")
    apply (simp add: pwrite_use_env_def)
   apply (auto)
   apply (case_tac "\<not> any_loc_use rx")
    apply (simp add: any_loc_use_def)
    apply (auto)
    apply (cut_tac r_x="comp_use_env rx1 rx2" and r_s="rx" and r_ex="comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex" and x="x" in rhs_sw_leq_use_none)
        apply (auto)
    apply (rule_tac r_s="r_s1" in sw_leq_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
       apply (auto)
   apply (case_tac "pwrite_use_env rx b \<noteq> add_use_env rx (Loc b) UsePerm")
    apply (simp add: pwrite_use_env_def)
   apply (auto)
   apply (rule_tac wtae_req_leq_use_env1)
   apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
    apply (simp)
   apply (rule_tac unroll_dcl_use_env)
   apply (rule_tac dist_diff_leq_use_env)
   apply (rule_tac dist_diff_leq_use_env_gen)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac pwrite_leq_use_env)
     apply (rule_tac r_s="r_s1" in sw_leq_use_env)
      apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
       apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (case_tac "pwrite_use_env (comp_use_env rx1 rx2) b \<noteq> comp_use_env rx1 rx2")
   apply (simp add: pwrite_use_env_def)
  apply (auto)
  apply (rule_tac pwrite_leq_use_env)
    apply (rule_tac sw_leq_use_env)
     apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
      apply (auto)
  apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac unroll_dcl_use_env)
  apply (rule_tac rhs_diff_rem_leq_use_env2)
   apply (rule_tac r_s="r_s1" in leq_use_no_own)
    apply (simp add: semi_weak_use_env_def)
    apply (erule_tac x="Loc b" in allE)
    apply (simp_all)
  apply (rule_tac dist_diff_leq_use_env)
  apply (rule_tac dist_diff_leq_use_env_gen)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac pwrite_leq_use_env)
    apply (rule_tac r_s="r_s1" in sw_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (auto)
  apply (rule_tac id_leq_use_env)
  done
 
lemma wt_read_value_ih: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; semi_weak_use_env r_s1; env (Loc b) = Some t; mem_ty t; mem_val_env env; rv_delta delta' e b \<rbrakk> \<Longrightarrow>
  well_typed env delta' (add_use_env r_s1 (Loc b) UsePerm) e tau (add_use_env r_s2 (Loc b) UsePerm) (pwrite_use_env rx b)"      
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
    (* const + op cases *)
          apply (rule_tac dist_add_leq_use_env)
          apply (auto)
         apply (rule_tac add_pwrite_leq_use_env)
          apply (rule_tac r_s="r_s1" in sw_leq_use_env)
           apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
            apply (auto)
         apply (rule_tac dist_add_leq_use_env)
         apply (auto)
        apply (rule_tac dist_add_leq_use_env)
        apply (auto)
       apply (rule_tac add_pwrite_leq_use_env)
        apply (rule_tac r_s="r_s1" in sw_leq_use_env)
         apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
          apply (auto)
       apply (rule_tac dist_add_leq_use_env)
       apply (auto)
    (* var case. *)
      apply (rule_tac water_var_case)
                 apply (auto)
    (* pair case. *)
     apply (rule_tac water_pair_case)
                      apply (auto)
    (* if case *)
    apply (rule_tac water_if_case)
                apply (auto)
    (* lam case *)
   apply (rule_tac water_lam_case)
               apply (auto)
    (* app case *)
  apply (rule_tac water_app_case)
                 apply (auto)
  done    
  
lemma wtae_diff_use_env: "\<lbrakk> strong_use_env r_s \<rbrakk> \<Longrightarrow> diff_use_env (add_use_env r_s x UsePerm) (rem_use_env r_s x) = one_use_env x UsePerm"    
  apply (case_tac "\<forall> y. diff_use_env (add_use_env r_s x UsePerm) (rem_use_env r_s x) y = one_use_env x UsePerm y")
   apply (auto)
  apply (simp add: one_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: strong_use_env_def)
  apply (case_tac "x = y")
   apply (auto)
  apply (erule_tac x="y" in allE)
  apply (case_tac "r_s y")
    apply (auto)
  done    
   
    (* if x is an owner var, then there is some delta mapping to it *)
lemma delta_res_vars: "\<lbrakk> Loc x \<in> res_vars delta e \<rbrakk> \<Longrightarrow> (\<exists> x'. delta x' = x \<and> x' \<in> ref_vars e)"  
  apply (induct e)
        apply (auto)
  apply (case_tac xa)
   apply (auto)
  done    
    
lemma wt_read_value: "\<lbrakk> well_typed env delta r_x v tau r_x r_x; is_value v; well_formed_delta env delta;
  env (Loc b) = Some t; mem_ty t; unlim tau; r_s (Loc b) \<noteq> NoPerm; mem_val_env env; sub_env s env; rv_delta delta' v b \<rbrakk> \<Longrightarrow>
  well_typed env delta' r_s v tau r_s (one_use_env (Loc b) UsePerm)"
    (* it suffices to prove for starting permissions of just x. *)
  apply (rule_tac r_s="one_use_env (Loc b) UsePerm" in well_typed_incr_simul_perm)
   apply (simp add: leq_use_env_def)
   apply (simp add: one_use_env_def)
   apply (case_tac "r_s (Loc b)")
     apply (auto)
    (* call the induction hypothesis *)
  apply (cut_tac env="env" and ?r_s1.0="drop_use_env r_x" and e="v" and tau="tau" and
        ?r_s2.0="drop_use_env r_x" and rx="drop_use_env r_x" and b="b" and
        t="t" in wt_read_value_ih)    
        apply (rule_tac wt_sexp_drop_all)
           apply (auto)
     apply (simp add: unlim_def)
    apply (rule_tac value_is_sexp)
    apply (simp)
   apply (rule_tac semi_weak_drop_use_env)
    (* to reduce r_x to just b, we must invoke the diff lemma *)
  apply (cut_tac eq_own)
  apply (auto)
  apply (rule_tac t="one_use_env (Loc b) UsePerm" and s="diff_use_env (add_use_env (lift_use_env r_x r) (Loc b) UsePerm)
    (rem_use_env (lift_use_env r_x r) (Loc b))" in subst)
   apply (rule_tac wtae_diff_use_env)
   apply (rule_tac strong_lift_use_env)
   apply (simp)
    (* permission manipulation *)
  apply (rule_tac well_typed_diff_perms)
   apply (rule_tac rx="pwrite_use_env (drop_use_env r_x) b" in well_typed_incr_req)
     apply (rule_tac r_s="add_use_env (drop_use_env r_x) (Loc b) UsePerm" in well_typed_incr_simul_perm)
      apply (rule_tac dist_add_leq_use_env)
      apply (rule_tac drop_leq_use_env)
      apply (rule_tac self_lift_leq_use_env)
     apply (simp)
    (* proving requirements change was valid *)
    apply (rule_tac add_pwrite_leq_use_env)
      apply (rule_tac semi_weak_drop_use_env)
     apply (auto)
    apply (rule_tac dist_add_leq_use_env)
    apply (rule_tac drop_leq_use_env)
    apply (rule_tac self_lift_leq_use_env)
   apply (rule_tac id_leq_use_env)
    (* proving that the diff was valid, which should be true since b is the only non-prim var. say that x \<noteq> b *)
  apply (case_tac "x \<noteq> Loc b")
   apply (auto)
   apply (case_tac x)
    apply (auto)
    (* - say that x is a var. then it must be in the env, which is impossible since env is under some s *)
    apply (simp add: non_prim_vars_def)
    apply (simp add: non_prim_entry_def)
    apply (simp add: sub_env_def)
    apply (erule_tac x="Var x1" in allE)
    apply (auto)
    (* - otherwise, x is a res var, which means it must be a delta, which is impossible by rv_delta *)
   apply (simp add: non_prim_vars_def)
   apply (auto)
   apply (cut_tac x="x2" and e="v" in delta_res_vars)
    apply (auto)
   apply (simp add: rv_delta_def)
    (* - then x = b, which is fine *)
  apply (simp add: own_env_vars_def)
  apply (simp add: rem_use_env_def)
  done
    
end