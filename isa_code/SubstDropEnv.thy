theory SubstDropEnv
  imports AltFlatLemma SubstExp
begin
    
fun drop_use_env_ex where
  "drop_use_env_ex r_s OwnPerm = r_s"
| "drop_use_env_ex r_s r = drop_use_env r_s"

definition tau_drop_req where
  "tau_drop_req r tau = (if r = OwnPerm then True else req_type tau \<noteq> Aff)"
    
lemma wt_sexp_drop_all_ex: "\<lbrakk> well_typed env delta rx e tau rx rx; well_formed_delta env delta; tau_drop_req r tau; is_sexp e \<rbrakk> \<Longrightarrow>
  well_typed env delta (drop_use_env_ex rx r) e tau (drop_use_env_ex rx r) (drop_use_env_ex rx r)" 
  apply (simp add: tau_drop_req_def)
  apply (case_tac r)
    apply (auto)
   apply (rule_tac wt_sexp_drop_all)
     apply (auto)
  apply (rule_tac wt_sexp_drop_all)
    apply (auto)
  done
    
lemma dist_drop_leq_use_env_ex: "\<lbrakk> leq_perm q r \<rbrakk> \<Longrightarrow> leq_use_env (drop_use_env_ex r_s q) (drop_use_env_ex r_s r)"
  apply (case_tac "drop_use_env_ex r_s q = drop_use_env r_s")
   apply (case_tac r)
     apply (auto)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac self_drop_leq_use_env)
  apply (case_tac q)
    apply (auto)
  apply (case_tac r)
    apply (auto)
  apply (rule_tac id_leq_use_env)
  done    
    
lemma safe_lift_drop_use_env: "\<lbrakk> r \<noteq> NoPerm \<rbrakk> \<Longrightarrow> safe_use_lift (drop_use_env_ex r_s r) r"    
  apply (case_tac r)
    apply (auto)
  apply (simp add: drop_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
  done    
    
end