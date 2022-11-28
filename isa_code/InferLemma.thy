theory InferLemma
  imports InferDef FlatLemma
begin
  
lemma ifl_end_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (comp_use_env (drop_use_env r_x) rx) (comp_use_env (comp_use_env (drop_use_env r_s) (infl_use_env r_s r_x)) rx)"  
  apply (rule_tac dist_comp_leq_use_env)
   apply (rule_tac comp_leq_use_env1)
   apply (rule_tac comp_leq_use_env1)
   apply (rule_tac dist_drop_leq_use_env)
   apply (simp)
  apply (rule_tac self_comp_leq_use_env2)
  done
  
lemma cut_comp_leq_use_env: "leq_use_env (cut_use_env (comp_use_env r_s r_x)) (comp_use_env r_s (cut_use_env r_x))"    
  apply (simp add: leq_use_env_def)
  apply (simp add: cut_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma ifl_req_leq_use_env: "\<lbrakk> leq_use_env (diff_use_env r_s (comp_use_env r_x r_ex)) rx \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env r_s (comp_use_env r_x (cut_use_env r_ex))) rx"    
  apply (rule_tac r_sb="diff_use_env r_s (comp_use_env r_x r_ex)" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac dist_diff_leq_use_env_cut)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac cut_comp_leq_use_env)
  done   
    
lemma infl_leq_use_env_gen: "\<lbrakk> leq_use_env r_x (diff_use_env r_s r_ex); leq_use_env r_ex r_s \<rbrakk> \<Longrightarrow>
  leq_use_env r_ex (comp_use_env (drop_use_env r_s) (infl_use_env r_s r_x))"    
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)  
  apply (simp add: comp_use_env_def)
  apply (simp add: drop_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: infl_use_env_def)
  apply (auto)
    apply (case_tac "r_s x")
      apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
    
    (* the key that makes this lemma work is that if r_s1 = Own is necessary, but r_s2 = Own,
          then rx = Own as well. for instance, take the lhs of a pair. if the pair requires
          ownership, then normally rx = Own, or r_s2 = None. the only time this doesn't happen is
          when the lhs is primitive, and so it can be removed. however in this case, an
          application must have been performed, since all necessary permissions have been removed.

      so proving this lemma is probably more efficient if we do it with more concrete r_s1, r_s2.
 *)
    
lemma infer_flat_lemma: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx \<rbrakk> \<Longrightarrow>
  well_typed env (comp_use_env (comp_use_env (drop_use_env r_s1) (infl_use_env r_s1 r_s2)) rx) e tau
    (comp_use_env (drop_use_env r_s2) rx) rx"
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
    (* const case *)
           apply (rule_tac ifl_end_leq_use_env)
           apply (simp)
          apply (rule_tac self_comp_leq_use_env2)
    (* op case *)
         apply (rule_tac ifl_end_leq_use_env)
         apply (simp)
        apply (rule_tac self_comp_leq_use_env2)
    (* var case p1. *)
       apply (rule_tac r_sb="comp_use_env rx (infl_use_env r_s1 r_s2)" in trans_leq_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac self_comp_leq_use_env2)
        apply (rule_tac comp_leq_use_env1)
        apply (rule_tac self_comp_leq_use_env2)
       apply (rule_tac st_diff_comp_leq_use_env)
       apply (rule_tac r_sb="diff_use_env (ereq_use_env (owner_name x) tau_x) (comp_use_env (ereq_use_env (owner_name x) tau_x) r_ex)" in trans_leq_use_env)
        apply (simp)
       apply (rule_tac dist_diff_leq_use_env_cut)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac infl_leq_use_env)
        apply (simp)
       apply (rule_tac dist_comp_leq_use_env)
        apply (simp_all)
    (* var case p2. *)
      apply (rule_tac x="cut_use_env r_ex" in exI)
      apply (auto)
         apply (rule_tac mini_disj_diff_leq_use_env2)
          apply (rule_tac ifl_end_leq_use_env)
          apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env (owner_name x) tau_x) r_ex)" in trans_leq_use_env)
           apply (rule_tac self_diff_leq_use_env)
          apply (simp)
         apply (rule_tac r_s="comp_use_env (ereq_use_env (owner_name x) tau_x) r_ex" in mini_disj_leq_use_env1)
          apply (rule_tac r_s="diff_use_env r_s1 (comp_use_env (ereq_use_env (owner_name x) tau_x) r_ex)" in mini_disj_leq_use_env2)
           apply (rule_tac mini_disj_diff_use_env)
          apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
           apply (simp)
          apply (rule_tac dist_comp_leq_use_env)
           apply (rule_tac self_drop_leq_use_env)
          apply (simp)
         apply (rule_tac dist_comp_leq_use_env)
          apply (rule_tac self_comp_leq_use_env1)
         apply (rule_tac comp_leq_use_env2)
         apply (rule_tac self_cut_leq_use_env)
        apply (rule_tac self_comp_leq_use_env2)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac comp_leq_use_env2)
       apply (rule_tac infl_leq_use_env)
        apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env (owner_name x) tau_x) r_ex)" in trans_leq_use_env)
         apply (rule_tac dist_diff_leq_use_env_gen)
          apply (rule_tac id_leq_use_env)
         apply (rule_tac self_comp_leq_use_env2)
        apply (simp_all)
      apply (rule_tac ifl_req_leq_use_env)
      apply (simp)
    (* pair case *)
     apply (cut_tac r_sc="r_s3" and r_sb="r_s2a" and r_sa="r_s1" in trans_leq_use_env)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (rule_tac x="comp_use_env (drop_use_env r_s2a) rx1" in exI)
     apply (rule_tac x="comp_use_env (drop_use_env r_s3) rx2" in exI)
     apply (rule_tac x="rx1" in exI)
     apply (auto)
      apply (rule_tac ?r_s1.0="comp_use_env (comp_use_env (drop_use_env r_s1) (infl_use_env r_s1 r_s2a)) rx1" in well_typed_incr_start_perm)
       apply (simp)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac self_comp_leq_use_env1)
       apply (rule_tac comp_leq_use_env2)
       apply (rule_tac dist_infl_leq_use_env)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
        apply (rule_tac diff_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
      apply (rule_tac comp_leq_use_env1)
      apply (rule_tac infl_leq_use_env_gen)
    apply (rule_tac diff_
    
   
  
  
end