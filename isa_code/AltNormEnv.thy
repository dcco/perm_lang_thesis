theory AltNormEnv
  imports PermEnvLeq
begin
  
definition norm_use_env where
  "norm_use_env r_x r_s = (\<lambda> x. if r_s x = NoPerm then NoPerm else r_x x)"  
  
    (* - norm ordering lemmas *)
  
lemma self_norm_leq_use_env: "leq_use_env (norm_use_env r_x r_s) r_x"
  apply (simp add: norm_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done 
  
lemma norm_leq_use_env: "\<lbrakk> leq_use_env r_x r_c \<rbrakk> \<Longrightarrow> leq_use_env (norm_use_env r_x r_s) r_c"
  apply (simp add: norm_use_env_def)
  apply (simp add: leq_use_env_def)
  done

lemma dist_norm_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (norm_use_env r_ex r_x) (norm_use_env r_ex r_s)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: norm_use_env_def)
  apply (auto)
   apply (erule_tac x="x" in allE)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done    
    
lemma diff_norm_leq_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow> leq_use_env (norm_use_env r_s r_x) (diff_use_env r_s r_ex)"
  apply (simp add: diff_use_env_def)
  apply (simp add: norm_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done    
    
lemma diff_norm_leq_use_env_ex: "\<lbrakk> leq_use_env r_s r_c \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env r_s (norm_use_env r_x r_c)) (diff_use_env r_s r_x)"
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (simp add: norm_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (auto)  
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
lemma diff_norm_leq_use_env_gen: "\<lbrakk> leq_use_env r_sa r_c; leq_use_env r_sa r_sb \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env r_sa (norm_use_env r_x r_c)) (diff_use_env r_sb r_x)"    
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (simp add: norm_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (auto)
   apply (case_tac "r_sa x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)    
  done
 
lemma spec_norm_leq_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow> leq_use_env (norm_use_env r_c r_x) (diff_use_env (norm_use_env r_c r_s) r_ex)"    
  apply (simp add: diff_use_env_def)
  apply (simp add: norm_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
   apply (erule_tac x="x" in allE)
   apply (case_tac "r_x x")
     apply (auto)
    apply (case_tac "r_ex x")
      apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_ex x")
    apply (auto)
    apply (case_tac "r_c x")
      apply (auto)
   apply (case_tac "r_c x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done    

lemma rhs_self_norm_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x (norm_use_env r_s r_x)"
  apply (simp add: leq_use_env_def)
  apply (simp add: norm_use_env_def)
  done
    
lemma rhs_norm_leq_use_env: "\<lbrakk> leq_use_env r_x r_ex; leq_use_env r_ex r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x (norm_use_env r_s r_ex)"    
  apply (rule_tac r_sb="r_ex" in trans_leq_use_env)
   apply (rule_tac rhs_self_norm_leq_use_env)
   apply (auto)
  done    
    
    (* - norm equality lemmas *)
    
lemma sub_norm_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> norm_use_env (norm_use_env r_c r_s) r_x = norm_use_env r_c r_x"    
  apply (case_tac "\<forall> x. norm_use_env (norm_use_env r_c r_s) r_x x = norm_use_env r_c r_x x")
   apply (auto)
  apply (simp add: leq_use_env_def)
  apply (simp add: norm_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done    
 
lemma dist_norm_comp_use_env: "comp_use_env (norm_use_env r_s r_c) (norm_use_env r_x r_c) = norm_use_env (comp_use_env r_s r_x) r_c"    
  apply (case_tac "\<forall> x. comp_use_env (norm_use_env r_s r_c) (norm_use_env r_x r_c) x = norm_use_env (comp_use_env r_s r_x) r_c x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: norm_use_env_def)
  apply (auto)
  done     
    
    (* - norm disjointness lemmas *)
    
lemma mini_disj_norm_use_env1: "\<lbrakk> mini_disj_use_env r_x r_c \<rbrakk> \<Longrightarrow> mini_disj_use_env (norm_use_env r_x r_s) r_c"      
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (simp add: norm_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
  done

lemma mini_disj_norm_use_env2: "\<lbrakk> mini_disj_use_env r_c r_s \<rbrakk> \<Longrightarrow> mini_disj_use_env r_c (norm_use_env r_x r_s)"       
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (simp add: norm_use_env_def)
  done    
 
lemma disj_norm_use_env1: "\<lbrakk> mini_disj_use_env r_x r_c; disj_use_env r_s r_c \<rbrakk> \<Longrightarrow> disj_use_env (norm_use_env r_x r_s) r_c"    
  apply (simp add: disj_use_env_def)
  apply (auto)
   apply (rule_tac mini_disj_norm_use_env1)
    apply (auto)
  apply (rule_tac mini_disj_norm_use_env2)
   apply (auto)
  done

lemma disj_norm_use_env2: "\<lbrakk> mini_disj_use_env r_x r_c; disj_use_env r_c r_s \<rbrakk> \<Longrightarrow> disj_use_env r_c (norm_use_env r_x r_s)"    
  apply (simp add: disj_use_env_def)
  apply (auto)
   apply (rule_tac mini_disj_norm_use_env2)
    apply (auto)
  apply (rule_tac mini_disj_norm_use_env1)
   apply (auto)
  done     

definition strong_use_env where
  "strong_use_env r_s = (\<forall> x. r_s x \<noteq> UsePerm)"    
    
lemma ex_norm_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> (\<exists> r_ex. strong_use_env r_ex \<and> norm_use_env r_s r_x = diff_use_env r_s r_ex)"
  apply (rule_tac x="\<lambda> x. if r_s x \<noteq> NoPerm \<and> r_x x = NoPerm then OwnPerm else NoPerm" in exI)
  apply (auto)
   apply (simp add: strong_use_env_def)
  apply (case_tac "\<forall> x. norm_use_env r_s r_x x = diff_use_env r_s (\<lambda>x. if r_s x \<noteq> NoPerm \<and> r_x x = NoPerm then OwnPerm else NoPerm) x")
   apply (auto)
  apply (simp add: leq_use_env_def)
  apply (simp add: norm_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  done        
    
end