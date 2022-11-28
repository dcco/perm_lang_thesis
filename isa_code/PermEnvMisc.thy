theory PermEnvMisc
  imports PermEnvLeq
begin
  
    (* 
      ####################################
        P2. weak disjointness lemmas
      ####################################
    *)  

lemma mini_disj_leq_use_env1: "\<lbrakk> mini_disj_use_env r_s r_ex; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> mini_disj_use_env r_x r_ex"    
  apply (simp add: leq_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (rule_tac allI)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "r_s x")
     apply (auto)
  done

lemma mini_disj_leq_use_env2: "\<lbrakk> mini_disj_use_env r_ex r_s; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> mini_disj_use_env r_ex r_x"        
  apply (simp add: leq_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (rule_tac allI)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)  
  apply (case_tac "r_x x")
    apply (auto)
  done   

lemma mini_disj_comp_use_env: "\<lbrakk> mini_disj_use_env r_x r_ex; mini_disj_use_env r_s r_ex \<rbrakk> \<Longrightarrow> mini_disj_use_env (comp_use_env r_x r_s) r_ex"    
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)  
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
 
lemma mini_disj_comp_use_env_alt: "\<lbrakk> mini_disj_use_env r_ex r_x; mini_disj_use_env r_ex r_s \<rbrakk> \<Longrightarrow> mini_disj_use_env r_ex (comp_use_env r_x r_s)"       
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: comp_use_env_def)
  done    

lemma mini_disj_diff_use_env: "mini_disj_use_env r_x (diff_use_env r_s r_x)"
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: diff_use_env_def)
  done     

lemma swp_mini_disj_use_env: "\<lbrakk> leq_use_env rx_p (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow> mini_disj_use_env r_ex rx_p"    
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
  apply (rule_tac r_s="diff_use_env r_s r_ex" in leq_use_none)
   apply (auto)
  apply (rule_tac diff_use_none_ex)
  apply (auto)
  done    
    
lemma mini_disj_empty_use_env: "mini_disj_use_env empty_use_env r_s"
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: empty_use_env_def)
  done
  
    
    (* 
      ####################################
        P3. main disjointness lemmas
      ####################################
    *)    

lemma comm_disj_use_env: "\<lbrakk> disj_use_env r_s r_x \<rbrakk> \<Longrightarrow> disj_use_env r_x r_s"
  apply (simp add: disj_use_env_def)
  done        
    
    (* - ordering lemmas *)
    
lemma disj_leq_use_env1: "\<lbrakk> disj_use_env r_s r_ex; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> disj_use_env r_x r_ex"
  apply (simp add: disj_use_env_def)
  apply (auto)
   apply (rule_tac mini_disj_leq_use_env1)
    apply (auto)
  apply (rule_tac mini_disj_leq_use_env2)
   apply (auto)
  done

lemma disj_leq_use_env2: "\<lbrakk> disj_use_env r_ex r_s; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> disj_use_env r_ex r_x"
  apply (simp add: disj_use_env_def)
  apply (auto)
   apply (rule_tac mini_disj_leq_use_env2)
    apply (auto)
  apply (rule_tac mini_disj_leq_use_env1)
   apply (auto)
  done     
    
    (* - comp lemmas *)
    
lemma disj_comp_use_env1: "\<lbrakk> disj_use_env r_s1 r_ex; disj_use_env r_s2 r_ex \<rbrakk> \<Longrightarrow> disj_use_env (comp_use_env r_s1 r_s2) r_ex"
  apply (simp add: disj_use_env_def)
  apply (auto)
   apply (rule_tac mini_disj_comp_use_env)
    apply (auto)
  apply (rule_tac mini_disj_comp_use_env_alt)
   apply (auto)
  done

lemma disj_comp_use_env2: "\<lbrakk> disj_use_env r_ex r_s1; disj_use_env r_ex r_s2 \<rbrakk> \<Longrightarrow> disj_use_env r_ex (comp_use_env r_s1 r_s2)"    
  apply (simp add: disj_use_env_def)
  apply (auto)
   apply (rule_tac mini_disj_comp_use_env_alt)
    apply (auto)
  apply (rule_tac mini_disj_comp_use_env)
   apply (auto)
  done

    (* - lemmas TO BE SORTED *)    

lemma gen_mini_disj_use_env1: "\<lbrakk> disj_use_env r_x r_s \<rbrakk> \<Longrightarrow> mini_disj_use_env r_x r_s"    
  apply (simp add: disj_use_env_def)
  done
    
lemma gen_mini_disj_use_env2: "\<lbrakk> disj_use_env r_s r_x \<rbrakk> \<Longrightarrow> mini_disj_use_env r_x r_s"    
  apply (simp add: disj_use_env_def)
  done
    
lemma disj_add_use_env: "\<lbrakk> r_x x = NoPerm; disj_use_env r_s r_x \<rbrakk> \<Longrightarrow> disj_use_env (add_use_env r_s x r) r_x"    
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: add_use_env_def)
  done    
    
lemma disj_rem_use_env1: "\<lbrakk> disj_use_env r_s r_x \<rbrakk> \<Longrightarrow> disj_use_env r_s (rem_use_env r_x x)"      
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: rem_use_env_def)
  done
    
lemma disj_rem_use_envx: "\<lbrakk> disj_use_env r_s r_x \<rbrakk> \<Longrightarrow> disj_use_env  (rem_use_env r_s x) r_x"      
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: rem_use_env_def)
  done    
  
lemma disj_rem_use_env2: "\<lbrakk> r_s x = NoPerm; disj_use_env r_s (rem_use_env r_x x) \<rbrakk> \<Longrightarrow> disj_use_env r_s r_x"    
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (auto)
   apply (case_tac "x = xa")
    apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (erule_tac x="xa" in allE)
  apply (auto)
   apply (case_tac "x = xa")
    apply (auto)
  apply (case_tac "x = xa")
   apply (auto)
  done

lemma disj_add_rem_use_env: "\<lbrakk> r_s x = NoPerm; disj_use_env r_s r_x \<rbrakk> \<Longrightarrow> disj_use_env (add_use_env r_s x r) (rem_use_env r_x x)"
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: rem_use_env_def)
  done

lemma double_weak_disj_use_env: "\<lbrakk> weak_use_env r_x; weak_use_env r_s \<rbrakk> \<Longrightarrow> disj_use_env r_x r_s"
  apply (simp add: weak_use_env_def)
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  done
lemma lease_mini_disj_use_env: "\<lbrakk> mini_disj_use_env r_s (diff_use_env r_x r_ex); mini_disj_use_env r_ex r_s \<rbrakk> \<Longrightarrow> mini_disj_use_env r_s r_x"    
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done  
  
lemma lease_disj_use_env1: "\<lbrakk> disj_use_env r_s (diff_use_env r_x r_ex); mini_disj_use_env r_ex r_s \<rbrakk> \<Longrightarrow> disj_use_env r_s r_x"    
  apply (simp add: disj_use_env_def)
  apply (auto)
   apply (rule_tac lease_mini_disj_use_env)
    apply (auto)
    (* we expect a similar formulation to exist using this logic
      rx2a | rx2 + [infl r_s2a - r_s3], rx2a |> rx2 + [infl r_s2a - r_s3], rx2a |> r_s3 - EX, EX |> r_s3 - EX
      rx2 + [infl r_s2a - r_s3] |> rx2a - EX
          apply (rule_tac r_s="diff_use_env r_s r_ex" in mini_disj_leq_use_env2)
    *)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done
 
lemma lease_disj_use_env2: "\<lbrakk> disj_use_env (diff_use_env r_x r_ex) r_s; mini_disj_use_env r_ex r_s \<rbrakk> \<Longrightarrow> disj_use_env r_x r_s"
  apply (rule_tac comm_disj_use_env)
  apply (rule_tac r_ex="r_ex" in lease_disj_use_env1)
   apply (rule_tac comm_disj_use_env)
   apply (auto)
  done    
    
    (* - empty lemmas *)
    
lemma disj_empty_use_env1: "disj_use_env r_s empty_use_env"
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: empty_use_env_def)
  done

lemma disj_empty_use_env2: "disj_use_env empty_use_env r_s"
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: empty_use_env_def)
  done
    
    (* - singleton lemmas *)
    
lemma disj_one_use_env: "\<lbrakk> r_s x = NoPerm \<rbrakk> \<Longrightarrow> disj_use_env r_s (one_use_env x OwnPerm)"    
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: one_use_env_def)
  done  
    
    (* 
      ####################################
        P3. weakness lemmas
      ####################################
    *)        
  
lemma leq_weak_use_env: "\<lbrakk> weak_use_env r_s; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> weak_use_env r_x"    
  apply (simp add: weak_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_s x")
    apply (auto)
  done    
    
lemma weak_comp_use_env1: "\<lbrakk> weak_use_env (comp_use_env r_sa r_sb) \<rbrakk> \<Longrightarrow> weak_use_env r_sa"    
  apply (simp add: weak_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_sb x")
    apply (auto)
  done
 
lemma weak_comp_use_env2: "\<lbrakk> weak_use_env (comp_use_env r_sa r_sb) \<rbrakk> \<Longrightarrow> weak_use_env r_sb"    
  apply (simp add: weak_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_sa x")
    apply (auto)
  done    
 
lemma dist_weak_comp_use_env: "\<lbrakk> weak_use_env r_sa; weak_use_env r_sb \<rbrakk> \<Longrightarrow> weak_use_env (comp_use_env r_sa r_sb)"    
  apply (simp add: weak_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_sa x")
    apply (auto)
   apply (case_tac "r_sb x")
     apply (auto)
  apply (case_tac "r_sb x")
    apply (auto)
  done       
    
lemma weak_diff_use_env: "\<lbrakk> weak_use_env r_s \<rbrakk> \<Longrightarrow> weak_use_env (diff_use_env r_s r_x)"     
  apply (simp add: weak_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done        

    
end