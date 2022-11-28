theory AltCutEnv
  imports PermEnvMisc LiftEnv AltNormEnv
begin

  (* ##### cut-family lemmas *)  
    
definition cut_use_env where
  "cut_use_env r_s = (\<lambda> x. if r_s x = UsePerm then NoPerm else r_s x)"
    
lemma self_cut_leq_use_env: "leq_use_env (cut_use_env r_s) r_s"  
  apply (simp add: leq_use_env_def)
  apply (simp add: cut_use_env_def)
  apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done

lemma cut_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (cut_use_env r_x) r_s"      
  apply (rule_tac r_sb="r_x" in trans_leq_use_env)
   apply (auto)
  apply (rule_tac self_cut_leq_use_env)
  done
  
lemma strong_cut_use_env: "strong_use_env (cut_use_env r_s)"
  apply (simp add: strong_use_env_def)
  apply (simp add: cut_use_env_def)
  done
  
lemma mini_disj_strong_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env r_s r_ex); strong_use_env r_ex \<rbrakk> \<Longrightarrow> mini_disj_use_env r_x r_ex"  
  apply (simp add: leq_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: strong_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done
  
lemma diff_cut_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env r_x (cut_use_env r_ex)) (diff_use_env r_s r_ex)"
  apply (simp add: leq_use_env_def)
  apply (simp add: cut_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_ex x")
    apply (auto)
  done      
 
lemma dist_diff_leq_use_env_cut: "\<lbrakk> leq_use_env r_x r_s; leq_use_env (cut_use_env r_exb) r_exa \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env r_x r_exa) (diff_use_env r_s r_exb)"
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (simp add: diff_use_env_def)
  apply (simp add: cut_use_env_def)
  apply (case_tac "r_exa x")
    apply (auto)
   apply (case_tac "r_exb x")
     apply (auto)
  apply (case_tac "r_exb x")
    apply (auto)
  done    
    
lemma lhs_diff_leq_use_env: "\<lbrakk> leq_use_env (diff_use_env r_x r_ex) r_s; leq_use_env (cut_use_env r_ex) r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x r_s"    
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (simp add: diff_use_env_def)
  apply (simp add: cut_use_env_def)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)   
  done    
    
lemma lift_cut_leq_use_env: "\<lbrakk> is_own r; leq_use_env r_x (lift_use_env r_s r) \<rbrakk> \<Longrightarrow> leq_use_env r_x (cut_use_env (lift_use_env r_s r))"    
  apply (simp add: leq_use_env_def)
  apply (simp add: cut_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  apply (simp add: is_own_def)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
    (* -- unsorted *)
    
lemma strong_lift_use_env: "\<lbrakk> is_own r \<rbrakk> \<Longrightarrow> strong_use_env (lift_use_env r_s r)"    
  apply (simp add: is_own_def)
  apply (simp add: strong_use_env_def)
  done    
  
end