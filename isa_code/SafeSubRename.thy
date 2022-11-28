theory SafeSubRename
  imports WTLemma SubstExp
begin
  

definition rename_use_env where
  "rename_use_env r_s x y = (add_use_env (rem_use_env r_s x) y (r_s x))"  
  
lemma rename_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (rename_use_env r_x x y) (rename_use_env r_s x y)"
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: rem_use_env_def)
  done
  
lemma rename_ereq_use_env: "ereq_use_env y tau = rename_use_env (ereq_use_env x tau) x y"
  apply (case_tac "\<forall> x'. ereq_use_env y tau x' = rename_use_env (ereq_use_env x tau) x y x'")
   apply (auto)
  apply (simp add: ereq_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
 
lemma rename_ereq_use_env2: "\<lbrakk> z \<noteq> x ; z \<noteq> y\<rbrakk> \<Longrightarrow> ereq_use_env z tau = rename_use_env (ereq_use_env z tau) x y"    
  apply (case_tac "\<forall> x'. ereq_use_env z tau x' = rename_use_env (ereq_use_env z tau) x y x'")
   apply (auto)
  apply (simp add: ereq_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "z = x'")
   apply (auto)
   apply (simp add: rem_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done    
    
lemma rename_req_use_env: "req_use_env y tau = rename_use_env (req_use_env x tau) x y"
  apply (case_tac "\<forall> x'. req_use_env y tau x' = rename_use_env (req_use_env x tau) x y x'")
   apply (auto)
  apply (simp add: req_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
 
lemma rename_req_use_env2: "\<lbrakk> z \<noteq> x ; z \<noteq> y\<rbrakk> \<Longrightarrow> req_use_env z tau = rename_use_env (req_use_env z tau) x y"    
  apply (case_tac "\<forall> x'. req_use_env z tau x' = rename_use_env (req_use_env z tau) x y x'")
   apply (auto)
  apply (simp add: req_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "z = x'")
   apply (auto)
   apply (simp add: rem_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
    
lemma rename_add_use_env: "add_use_env (rename_use_env r_s x y) y r = rename_use_env (add_use_env r_s x r) x y"    
  apply (case_tac "\<forall> x'. add_use_env (rename_use_env r_s x y) y r x' = rename_use_env (add_use_env r_s x r) x y x'")
   apply (auto)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)  
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done

lemma rename_add_use_env2: "\<lbrakk> z \<noteq> x; z \<noteq> y \<rbrakk> \<Longrightarrow> add_use_env (rename_use_env r_s x y) z r = rename_use_env (add_use_env r_s z r) x y"    
  apply (case_tac "\<forall> x'. add_use_env (rename_use_env r_s x y) z r x' = rename_use_env (add_use_env r_s z r) x y x'")    
   apply (auto)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)  
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "z = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
 
lemma rename_add_use_env3: "\<lbrakk> r_s x = NoPerm \<rbrakk> \<Longrightarrow> add_use_env r_s y r = rename_use_env (add_use_env r_s x r) x y"
  apply (case_tac "\<forall> x'. add_use_env r_s y r x' = rename_use_env (add_use_env r_s x r) x y x'")
   apply (auto)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
  
lemma rename_comp_use_env: "comp_use_env (rename_use_env r_x x y) (rename_use_env r_s x y) = rename_use_env (comp_use_env r_x r_s) x y"    
  apply (case_tac "\<forall> x'. comp_use_env (rename_use_env r_x x y) (rename_use_env r_s x y) x' = rename_use_env (comp_use_env r_x r_s) x y x'")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
    
lemma rename_diff_use_env: "diff_use_env (rename_use_env r_x x y) (rename_use_env r_s x y) = rename_use_env (diff_use_env r_x r_s) x y"    
  apply (case_tac "\<forall> x'. diff_use_env (rename_use_env r_x x y) (rename_use_env r_s x y) x' = rename_use_env (diff_use_env r_x r_s) x y x'")
  apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
    
lemma rename_lift_use_env: "lift_use_env (rename_use_env r_s x y) r = rename_use_env (lift_use_env r_s r) x y"  
  apply (case_tac "\<forall> x'. lift_use_env (rename_use_env r_s x y) r x' = rename_use_env (lift_use_env r_s r) x y x'")
   apply (auto)
  apply (case_tac r)
    apply (auto)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac "y = x'")
   apply (auto)
   apply (simp add: rem_use_env_def)
   apply (case_tac "x = x'")
    apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
  
lemma aff_rename_use_env: "\<lbrakk> aff_use_env r_s a \<rbrakk> \<Longrightarrow> aff_use_env (rename_use_env r_s x y) a"    
  apply (simp add: aff_use_env_def)
  apply (case_tac a)
    apply (auto)
   apply (simp add: rename_use_env_def)
   apply (simp add: add_use_env_def)
   apply (simp add: weak_use_env_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (simp add: rem_use_env_def)
   apply (case_tac "x = xa")
    apply (auto)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: null_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (simp add: rem_use_env_def)
  done
  (*
lemma safe_lift_rename_use_env: "\<lbrakk> safe_use_lift r_s r \<rbrakk> \<Longrightarrow> safe_use_lift (rename_use_env r_s x y) r"
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac r)
    apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = xa")
   apply (auto)
  done*)

lemma disj_rename_use_env: "\<lbrakk> disj_use_env r_x r_s \<rbrakk> \<Longrightarrow> disj_use_env (rename_use_env r_x x y) (rename_use_env r_s x y)"
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
   apply (simp add: rename_use_env_def)
   apply (simp add: add_use_env_def)
   apply (auto)
   apply (simp add: rem_use_env_def)
   apply (auto)
  apply (simp add: rename_use_env_def)
  apply (simp add: add_use_env_def)
  apply (auto)
  apply (simp add: rem_use_env_def)
  apply (auto)
  done
    
    
lemma artp_var_case1: "\<lbrakk>y \<noteq> x; add_env env (Var x) t (Var x) = Some tau_x; leq_use_env (ereq_use_env (Var x) tau_x) r_s1;
        leq_use_env r_s2 (diff_use_env r_s1 (comp_use_env (ereq_use_env (Var x) tau_x) r_ex)); leq_use_env rx r_s2; leq_use_env r_ex r_s1;
        leq_use_env (diff_use_env (ereq_use_env (Var x) tau_x) (comp_use_env (ereq_use_env (Var x) tau_x) r_ex)) rx\<rbrakk>
       \<Longrightarrow> \<exists>r_ex tau_x.
              add_env env (Var y) t (Var y) = Some tau_x \<and>
              leq_use_env (ereq_use_env (Var y) tau_x) (rename_use_env r_s1 (Var x) (Var y)) \<and>
              leq_use_env (rename_use_env r_s2 (Var x) (Var y))
               (diff_use_env (rename_use_env r_s1 (Var x) (Var y)) (comp_use_env (ereq_use_env (Var y) tau_x) r_ex)) \<and>
              leq_use_env (rename_use_env rx (Var x) (Var y)) (rename_use_env r_s2 (Var x) (Var y)) \<and>
              leq_use_env r_ex (rename_use_env r_s1 (Var x) (Var y)) \<and>
              leq_use_env (diff_use_env (ereq_use_env (Var y) tau_x) (comp_use_env (ereq_use_env (Var y) tau_x) r_ex)) (rename_use_env rx (Var x) (Var y))"
  apply (simp add: add_env_def)
  apply (auto)
   apply (case_tac "\<not> leq_perm (end_req_perm tau_x) (r_s1 (Var x))")
    apply (cut_tac r_x="ereq_use_env (Var x) tau_x" and r_s="r_s1" and x="Var x" in spec_leq_perm)
     apply (simp)
    apply (simp add: ereq_use_env_def)
    apply (simp add: one_use_env_def)
   apply (simp add: leq_use_env_def)
   apply (simp add: ereq_use_env_def)
   apply (simp add: one_use_env_def)
   apply (simp add: rename_use_env_def)
   apply (simp add: add_use_env_def)
  apply (cut_tac x="Var x" and y="Var y" and tau="tau_x" in rename_ereq_use_env)
  apply (simp)
  apply (case_tac "\<not> comp_use_env (ereq_use_env (Var y) tau_x) (rename_use_env r_ex (Var x) (Var y)) =
    rename_use_env (comp_use_env (ereq_use_env (Var x) tau_x) r_ex) (Var x) (Var y)")
   apply (cut_tac r_x="ereq_use_env (Var x) tau_x" and r_s="r_ex" and x="Var x" and y="Var y" in rename_comp_use_env)
   apply (simp)
  apply (rule_tac x="rename_use_env r_ex (Var x) (Var y)" in exI)
  apply (auto)
     apply (cut_tac r_x="r_s1" and r_s="comp_use_env (ereq_use_env (Var x) tau_x) r_ex" and x="Var x" and y="Var y" in rename_diff_use_env)
     apply (simp)
     apply (rule_tac rename_leq_use_env)
     apply (simp)
    apply (rule_tac rename_leq_use_env)
    apply (simp)
   apply (rule_tac rename_leq_use_env)
   apply (simp)
  apply (cut_tac r_x="ereq_use_env (Var x) tau_x" and r_s="comp_use_env (ereq_use_env (Var x) tau_x) r_ex" and x="Var x" and y="Var y" in rename_diff_use_env)
  apply (simp)
  apply (rule_tac rename_leq_use_env)
  apply (simp)
  done

  
lemma artp_var_case2: "\<lbrakk>Var y \<noteq> xa; add_env env (Var x) t xa = Some tau_x; leq_use_env (ereq_use_env xa tau_x) r_s1;
        leq_use_env r_s2 (diff_use_env r_s1 (comp_use_env (ereq_use_env xa tau_x) r_ex)); leq_use_env rx r_s2; leq_use_env r_ex r_s1;
        leq_use_env (diff_use_env (ereq_use_env xa tau_x) (comp_use_env (ereq_use_env xa tau_x) r_ex)) rx; Var x \<noteq> xa\<rbrakk>
       \<Longrightarrow> leq_use_env (ereq_use_env xa tau_x) (rename_use_env r_s1 (Var x) (Var y)) \<and>
           (\<exists>r_ex. leq_use_env (rename_use_env r_s2 (Var x) (Var y))
                    (diff_use_env (rename_use_env r_s1 (Var x) (Var y)) (comp_use_env (ereq_use_env xa tau_x) r_ex)) \<and>
                   leq_use_env (rename_use_env rx (Var x) (Var y)) (rename_use_env r_s2 (Var x) (Var y)) \<and>
                   leq_use_env r_ex (rename_use_env r_s1 (Var x) (Var y)) \<and>
                   leq_use_env (diff_use_env (ereq_use_env xa tau_x) (comp_use_env (ereq_use_env xa tau_x) r_ex)) (rename_use_env rx (Var x) (Var y)))"
  apply (auto)
   apply (case_tac "\<not>  leq_use_env (ereq_use_env xa tau_x) (rename_use_env r_s1 (Var x) (Var y)) = 
    leq_use_env (rename_use_env (ereq_use_env xa tau_x) (Var x) (Var y)) (rename_use_env r_s1 (Var x) (Var y))")
    apply (cut_tac z="xa" and x="Var x" and y="Var y" and tau="tau_x" in rename_ereq_use_env2)
      apply (simp_all)
   apply (rule_tac rename_leq_use_env)
   apply (simp)
  apply (case_tac "\<not> rename_use_env (ereq_use_env xa tau_x) (Var x) (Var y) = ereq_use_env xa tau_x")
   apply (cut_tac z="xa" and x="Var x" and y="Var y" and tau="tau_x" in rename_ereq_use_env2)
  apply (simp_all)
  apply (cut_tac r_x="ereq_use_env xa tau_x" and r_s="r_ex" and x="Var x" and y="Var y" in rename_comp_use_env)
  apply (simp_all)
  apply (rule_tac x="rename_use_env r_ex (Var x) (Var y)" in exI)
  apply (auto)
     apply (cut_tac r_x="r_s1" and r_s="comp_use_env (ereq_use_env xa tau_x) r_ex" and x="Var x" and y="Var y" in rename_diff_use_env)
     apply (simp_all)
     apply (rule_tac rename_leq_use_env)
     apply (simp)
    apply (rule_tac rename_leq_use_env)
    apply (simp)
   apply (rule_tac rename_leq_use_env)
   apply (simp)
  apply (cut_tac r_x="ereq_use_env xa tau_x" and r_s="comp_use_env (ereq_use_env xa tau_x) r_ex" and x="Var x" and y="Var y" in rename_diff_use_env)
  apply (simp_all)
  apply (rule_tac rename_leq_use_env)
  apply (simp)
  done
    
lemma alpha_rename_type_preserve: "\<lbrakk> well_typed (add_env env (Var x) t) delta r_s1 e tau r_s2 rx; (*env x = None;*)
  y \<notin> free_vars e; y \<notin> lam_vars e \<rbrakk> \<Longrightarrow>
  well_typed (add_env env (Var y) t) delta (rename_use_env r_s1 (Var x) (Var y)) (deep_alpha_rename e x y) tau
    (rename_use_env r_s2 (Var x) (Var y)) (rename_use_env rx (Var x) (Var y))"
  apply (induct e arbitrary: env tau t r_s1 r_s2 rx)
        apply (auto)
    (* const + op cases *)
           apply (rule_tac x="Var x" in rename_leq_use_env)
           apply (simp_all)
          apply (rule_tac x="Var x" in rename_leq_use_env)
          apply (simp_all)
         apply (rule_tac x="Var x" in rename_leq_use_env)
         apply (simp_all)
        apply (rule_tac x="Var x" in rename_leq_use_env)
        apply (simp_all)
    (* var case. *)
       apply (case_tac "xa = VarType x")
        apply (auto)
         apply (simp add: add_env_def)
        apply (rule_tac artp_var_case1)
              apply (auto)
       apply (case_tac xa)
        apply (auto)
          apply (simp add: add_env_def)
         apply (simp add: add_env_def)
         apply (rule_tac artp_var_case2)
                apply (auto)
         apply (simp add: add_env_def)
        apply (simp add: add_env_def)
       apply (simp add: add_env_def)
       apply (rule_tac artp_var_case2)
              apply (auto)
       apply (simp add: add_env_def)
    (* pair case *)
        apply (cut_tac r_s="rx1" and x="Var x" and y="Var y" and r="r" in rename_lift_use_env)
        apply (cut_tac r_s="rx2" and x="Var x" and y="Var y" and r="r" in rename_lift_use_env)
        apply (rule_tac x="rename_use_env r_s2a (Var x) (Var y)" in exI)
        apply (rule_tac x="rename_use_env r_s3 (Var x) (Var y)" in exI)
        apply (rule_tac x="rename_use_env rx1 (Var x) (Var y)" in exI)
        apply (auto)
        apply (rule_tac x="rename_use_env rx2 (Var x) (Var y)" in exI)
        apply (auto)
             apply (rule_tac rename_leq_use_env)
             apply (simp)
            apply (rule_tac rename_leq_use_env)
            apply (simp)(*
           apply (rule_tac safe_lift_rename_use_env)
           apply (simp)
          apply (rule_tac safe_lift_rename_use_env)
          apply (simp)*)
         apply (rule_tac disj_rename_use_env)
         apply (simp)
        apply (cut_tac r_x="r_s3" and r_s="r_ex" and x="Var x" and y="Var y" in rename_diff_use_env)
        apply (rule_tac x="rename_use_env r_ex (Var x) (Var y)" in exI)
        apply (auto)
           apply (rule_tac rename_leq_use_env)
           apply (simp)
          apply (rule_tac rename_leq_use_env)
          apply (simp)
         apply (rule_tac rename_leq_use_env)
         apply (simp)
        apply (case_tac "req_type (PairTy t1 t2 r) = Prim")
         apply (simp add: pair_req_def)
         apply (rule_tac leq_empty_use_env)
        apply (simp add: pair_req_def)
        apply (simp add: rename_comp_use_env)
        apply (simp add: rename_diff_use_env)
        apply (rule_tac rename_leq_use_env)
        apply (simp)
    (* if case *)
       apply (rule_tac x="rename_use_env rx' (Var x) (Var y)" in exI)
       apply (rule_tac x="rename_use_env r_s2a (Var x) (Var y)" in exI)
       apply (auto)
       apply (rule_tac x="rename_use_env rx1 (Var x) (Var y)" in exI)
       apply (auto)
       apply (rule_tac x="rename_use_env rx2 (Var x) (Var y)" in exI)
       apply (auto)
       apply (cut_tac r_x="rx1" and r_s="rx2" and x="Var x" and y="Var y" in rename_comp_use_env)
       apply (auto)
    (* lam case p1. *)(*
      apply (cut_tac y="Var y" and x="Var x" and e="e" in rename_ref_vars2)
        apply (auto)*)
     apply (rule_tac x="rename_use_env rxa (Var x) (Var y)" in exI)
     apply (auto)
        apply (rule_tac x="rename_use_env r_end (Var x) (Var y)" in exI)
        apply (rule_tac x="rename_use_env r_s' (Var x) (Var y)" in exI)
        apply (cut_tac env="env" and x="Var x" and t="t" and t'="t1" in double_add_env)
        apply (cut_tac env="env" and x="Var y" and t="t" and t'="t1" in double_add_env)
        apply (cut_tac r_s="rxa" and x="Var x" and y="Var y" and r="r" in rename_add_use_env)
        apply (simp)
       apply (rule_tac aff_rename_use_env)
       apply (simp)
      apply (rule_tac rename_leq_use_env)
      apply (simp)
     apply (rule_tac x="rename_use_env r_ex (Var x) (Var y)" in exI)
     apply (auto)
        apply (cut_tac r_x="r_s1" and r_s="r_ex" and x="Var x" and y="Var y" in rename_diff_use_env)
        apply (simp)
        apply (rule_tac rename_leq_use_env)
        apply (simp)
       apply (rule_tac rename_leq_use_env)
       apply (simp)
      apply (rule_tac rename_leq_use_env)
      apply (simp)
     apply (cut_tac r_x="rxa" and r_s="r_ex" and x="Var x" and y="Var y" in rename_diff_use_env)
     apply (simp)
     apply (rule_tac rename_leq_use_env)
     apply (simp)
    (* lam case p2. *)(*
    apply (cut_tac z="x1a" and x="Var x" and y="Var y" and e="e" in rename_ref_vars1)
      apply (auto)*)
   apply (rule_tac x="rename_use_env rxa (Var x) (Var y)" in exI)
   apply (auto)
      apply (rule_tac x="rename_use_env r_end (Var x) (Var y)" in exI)
      apply (rule_tac x="rename_use_env r_s' (Var x) (Var y)" in exI)
      apply (cut_tac env="env" and x="Var x1a" and y="Var x" and t="t" and t'="t1" in almost_comm_add_env)
       apply (simp_all)
      apply (cut_tac env="env" and x="Var x1a" and y="Var y" and t="t" and t'="t1" in almost_comm_add_env)
       apply (simp_all)
      apply (cut_tac r_s="rxa" and x="Var x" and y="Var y" and z="Var x1a" and r="r" in rename_add_use_env2)
        apply (simp_all)
     apply (rule_tac aff_rename_use_env)
     apply (simp)
    apply (rule_tac rename_leq_use_env)
    apply (simp)
   apply (rule_tac x="rename_use_env r_ex (Var x) (Var y)" in exI)
   apply (auto)
      apply (cut_tac r_x="r_s1" and r_s="r_ex" and x="Var x" and y="Var y" in rename_diff_use_env)
      apply (simp)
      apply (rule_tac rename_leq_use_env)
      apply (simp)
     apply (rule_tac rename_leq_use_env)
     apply (simp)
    apply (rule_tac rename_leq_use_env)
    apply (simp)
   apply (cut_tac r_x="rxa" and r_s="r_ex" and x="Var x" and y="Var y" in rename_diff_use_env)
   apply (simp)
   apply (rule_tac rename_leq_use_env)
   apply (simp)
    (* app case *)
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="r" in exI)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="rename_use_env r_s2a (Var x) (Var y)" in exI)
  apply (rule_tac x="rename_use_env rx1 (Var x) (Var y)" in exI)
  apply (auto)
  apply (rule_tac x="rename_use_env rx2 (Var x) (Var y)" in exI)
  apply (rule_tac x="rename_use_env r_s3 (Var x) (Var y)" in exI)
  apply (auto)
  apply (cut_tac r_s="rx2" and x="Var x" and y="Var y" and r="r" in rename_lift_use_env)
  apply (simp)
  apply (cut_tac r_x="rx1" and r_s="lift_use_env rx2 r" and x="Var x" and y="Var y" in rename_comp_use_env)
  apply (cut_tac r_x="comp_use_env rx1 (lift_use_env rx2 r)" and r_s="r_ex" and x="Var x" and y="Var y" in rename_comp_use_env)
  apply (rule_tac x="rename_use_env r_ex (Var x) (Var y)" in exI)
  apply (auto)
        apply (cut_tac r_x="r_s3" and r_s="comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex" and x="Var x" and y="Var y" in rename_diff_use_env)
        apply (simp)
        apply (rule_tac rename_leq_use_env)
        apply (simp)(*
       apply (rule_tac safe_lift_rename_use_env)
       apply (simp)*)
      apply (rule_tac rename_leq_use_env)
      apply (simp)
     apply (rule_tac disj_rename_use_env)
     apply (simp)
    apply (rule_tac rename_leq_use_env)
    apply (simp)
   apply (rule_tac rename_leq_use_env)
   apply (simp)
  apply (simp add: app_req_def)
  apply (auto)
   apply (rule_tac leq_empty_use_env)
  apply (cut_tac r_x="rx1" and r_s="rx2" and x="Var x" and y="Var y" in rename_comp_use_env)
  apply (simp)
  apply (cut_tac r_x="comp_use_env rx1 rx2" and r_s="comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex" and x="Var x" and y="Var y" in rename_diff_use_env)
  apply (simp)
  apply (rule_tac rename_leq_use_env)
  apply (simp)
  done
    

lemma alpha_rename_free_var_id: "\<lbrakk> x \<noteq> y \<rbrakk> \<Longrightarrow> x \<notin> free_vars (deep_alpha_rename e x y)"
  apply (induct e)
        apply (auto)
  apply (case_tac xa)
   apply (auto)
  apply (case_tac "x = x1")
   apply (auto)
  done       

lemma alpha_rename_free_var_none: "\<lbrakk> a \<notin> free_vars e; a \<noteq> y \<rbrakk> \<Longrightarrow> a \<notin> free_vars (deep_alpha_rename e x y)"     
  apply (induction e)
        apply (auto)
   apply (case_tac xa)
    apply (auto)
   apply (case_tac "x = x1")
    apply (auto)
  apply (cut_tac e="e" and x="a" and y="y" in alpha_rename_free_var_id)
   apply (auto)
  done
    
lemma alpha_rename_lam_var_none: "\<lbrakk> a \<notin> lam_vars e; a \<noteq> y \<rbrakk> \<Longrightarrow> a \<notin> lam_vars (deep_alpha_rename e x y)"  
  apply (induct e)
       apply (auto)
  apply (case_tac xa)
   apply (auto)
  apply (case_tac "x = x1")
   apply (auto)
  done
  
lemma lam_var_remove_free_var_none: "\<lbrakk> x \<notin> free_vars e \<rbrakk> \<Longrightarrow> x \<notin> free_vars (lam_var_remove e a b)"    
  apply (induct e)
       apply (auto)
   apply (case_tac "x \<noteq> b")
    apply (cut_tac e="e" and a="x" and x="a" and y="b" in alpha_rename_free_var_none)
      apply (auto)
  apply (case_tac "x \<noteq> b")
   apply (cut_tac e="e" and x="x" and y="b" in alpha_rename_free_var_id)
    apply (auto)
  done

lemma lam_var_remove_lam_var_none: "\<lbrakk> x \<notin> lam_vars e; x \<noteq> b \<rbrakk> \<Longrightarrow> x \<notin> lam_vars (lam_var_remove e a b)"  
  apply (induct e)  
       apply (auto)
  apply (cut_tac a="x" and e="e" and x="a" and y="b" in alpha_rename_lam_var_none)
    apply (auto)
  done    
    
lemma lam_var_remove_type_preserve: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; y \<notin> free_vars e; y \<notin> lam_vars e \<rbrakk> \<Longrightarrow>
  well_typed env delta r_s1 (lam_var_remove e x y) tau r_s2 rx"
  apply (induct e arbitrary: env tau r_s1 r_s2 rx)
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
    (* lam case p1. *)
    apply (rule_tac x="rxa" in exI)
    apply (auto)
    apply (rule_tac x="rename_use_env r_end (Var x) (Var y)" in exI)
    apply (rule_tac x="rename_use_env r_s' (Var x) (Var y)" in exI)
    apply (rule_tac ?r_s1.0="rem_use_env (add_use_env rxa (Var y) r) (Var x)" in well_typed_incr_start_perm)
     apply (cut_tac r_s="rxa" and x="Var y" and y="Var x" and r="r" in almost_comm_rem_add_use_env)
      apply (simp_all)
     apply (case_tac "\<not> add_use_env (rem_use_env rxa (Var x)) (Var y) r = rename_use_env (add_use_env rxa (Var x) r) (Var x) (Var y)")
      apply (case_tac "\<not> (\<forall> x'. add_use_env (rem_use_env rxa (Var x)) (Var y) r x' = rename_use_env (add_use_env rxa (Var x) r) (Var x) (Var y) x')")
       apply (auto)
      apply (simp add: rename_use_env_def)
      apply (simp add: add_use_env_def)
      apply (case_tac "Var y = x'")
       apply (auto)
      apply (simp add: rem_use_env_def)
      apply (case_tac "Var x = x'")
       apply (auto)
     apply (rule_tac alpha_rename_type_preserve)
       apply (simp_all)
    apply (rule_tac self_rem_leq_use_env)
    (* lam case p2. *)
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
    
    (* basically, we want to make sure that when we replace a var, we dont end up with the post_vars of vl overlapping with
      any of the ref vars of e. in other words, that we arent changing any of the ref vars. now the thing is, when we do lam var remove,
      we dont expect any of the ref vars to change actually  *)
lemma lam_var_list_remove_type_preserve: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; unique_post_vars vl;(* pre_vars vl \<subseteq> lam_vars e;*)
  post_vars vl \<inter> (free_vars e \<union> lam_vars e) = {} \<rbrakk> \<Longrightarrow> well_typed env delta r_s1 (lam_var_list_remove e vl) tau r_s2 rx"
  apply (induct vl arbitrary: e)
   apply (auto)
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and e="e" and tau="tau" and ?r_s2.0="r_s2" and rx="rx" and x="a" and y="b" in lam_var_remove_type_preserve)
      apply (auto)
  apply (case_tac "\<not> post_vars vl \<inter> (free_vars (lam_var_remove e a b) \<union> lam_vars (lam_var_remove e a b)) = {}")
   apply (auto)
    apply (cut_tac e="e" and x="x" and a="a" and b="b" in lam_var_remove_free_var_none)
     apply (auto)
  apply (cut_tac e="e" and x="x" and a="a" and b="b" in lam_var_remove_lam_var_none)
    apply (auto)
  done         
    
 
lemma alpha_rename_free_var_some: "\<lbrakk> x \<in> free_vars e; x \<noteq> a; x \<noteq> b \<rbrakk> \<Longrightarrow> x \<in> free_vars (deep_alpha_rename e a b)"    
  apply (induct e)
        apply (auto)
  apply (case_tac xa)
   apply (auto)
  done
    
lemma lam_var_remove_free_var_some: "\<lbrakk> x \<in> free_vars e; x \<noteq> b \<rbrakk> \<Longrightarrow> x \<in> free_vars (lam_var_remove e a b)"    
  apply (induct e)
       apply (auto)
  apply (rule_tac alpha_rename_free_var_some)
    apply (auto)
  done    
    
lemma lam_var_list_remove_free_var_some: "\<lbrakk> x \<in> free_vars e; x \<notin> post_vars vl \<rbrakk> \<Longrightarrow> x \<in> free_vars (lam_var_list_remove e vl)"    
  apply (induct vl arbitrary: e)
   apply (auto)
  apply (cut_tac x="x" and e="e" and a="a" and b="b" in lam_var_remove_free_var_some)
    apply (auto)
  done        
    
lemma lam_var_list_remove_lam_var_none1: "\<lbrakk> x \<notin> lam_vars e; x \<notin> post_vars vl \<rbrakk> \<Longrightarrow> x \<notin> lam_vars (lam_var_list_remove e vl)"        
  apply (induct vl arbitrary: e)
   apply (auto)
  apply (cut_tac e="e" and x="x" and a="a" and b="b" in lam_var_remove_lam_var_none)
    apply (auto)
  done
    
lemma alpha_rename_lam_var_none2: "\<lbrakk> x \<noteq> b \<rbrakk> \<Longrightarrow> x \<notin> lam_vars (deep_alpha_rename e x b)"    
  apply (induct e)
        apply (auto)
  apply (case_tac xa)
   apply (auto)
  apply (case_tac "x = x1")
   apply (auto)
  done
    
lemma lam_var_remove_lam_var_none2: "\<lbrakk> x \<noteq> b \<rbrakk> \<Longrightarrow> x \<notin> lam_vars (lam_var_remove e x b)"    
  apply (induct e)
       apply (auto)
  apply (cut_tac e="e" and x="x" and b="b" in alpha_rename_lam_var_none2)
   apply (auto)
  done    
    
lemma lam_var_list_remove_lam_var_none2: "\<lbrakk> x \<in> pre_vars vl; x \<notin> post_vars vl \<rbrakk> \<Longrightarrow> x \<notin> lam_vars (lam_var_list_remove e vl)"    
  apply (induct vl arbitrary: e)
   apply (auto)
  apply (cut_tac e="e" and x="x" and b="b" in lam_var_remove_lam_var_none2)
   apply (auto)
  apply (cut_tac e="lam_var_remove e x b" and x="x" and vl="vl" in lam_var_list_remove_lam_var_none1)
    apply (auto)
  done        
    
lemma lam_var_list_remove_free_var_some_rev: "\<lbrakk> x \<in> free_vars (lam_var_list_remove e vl) \<rbrakk> \<Longrightarrow> x \<in> free_vars e"
  apply (induction vl arbitrary: e)
   apply (auto)
  apply (case_tac "x \<notin> free_vars e")
   apply (auto)
  apply (cut_tac x="x" and e="e" and a="a" and b="b" in lam_var_remove_free_var_none)
   apply (auto)
  done
 
lemma lam_var_list_remove_free_var_none: "\<lbrakk> x \<notin> free_vars e \<rbrakk> \<Longrightarrow> x \<notin> free_vars (lam_var_list_remove e vl)"    
  apply (case_tac "x \<in> free_vars (lam_var_list_remove e vl)")
   apply (auto)
  apply (cut_tac x="x" and e="e" and vl="vl" in lam_var_list_remove_free_var_some_rev)
   apply (auto)
  done        

    
end