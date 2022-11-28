theory ResMapValid
  imports GenSubEnv AltNormEnv ResMapDisj
begin
 
definition super_drop_use_env where
  "super_drop_use_env r_s = (\<lambda> x. if r_s x = OwnPerm then NoPerm else r_s x)"  
  
lemma self_sdrop_leq_use_env: "leq_use_env (super_drop_use_env r_s) r_s"  
  apply (simp add: super_drop_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
lemma sdrop_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (super_drop_use_env r_x) r_s"    
  apply (rule_tac r_sb="r_x" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac self_sdrop_leq_use_env)
  done
    
lemma diff_sdrop_leq_use_env: "leq_use_env (diff_use_env r_s r_s) (super_drop_use_env r_s)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: super_drop_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
  

definition valid_use_entry where
  "valid_use_entry r_c r_s r_x = (leq_use_env r_x r_c \<and> strong_disj_use_env r_x r_s)"

    
    (* ######### NRES map validity *)
  
definition valid_nres_map where
  "valid_nres_map s s_map = (full_nres_map s s_map \<and> disj_nres_map s_map \<and> sub_nres_map s s_map)"
    
definition valid_exp_use_env where
  "valid_exp_use_env s s_map r_s = (sub_use_env s r_s \<and> sep_nres_map r_s s_map)"
  
end