theory ResMapDisj
  imports ResMap AltNormEnv
begin
  
lemma lift_sub_use_env: "\<lbrakk> sub_use_env s r_s \<rbrakk> \<Longrightarrow> sub_use_env s (lift_use_env r_s r)"   
  apply (simp add: sub_use_env_def)
  apply (case_tac r)
    apply (auto)
  done
  
    (* strong disjointness *)
  
definition strong_disj_use_env where
  "strong_disj_use_env r_x r_s = (\<forall> x. r_x x = NoPerm \<or> r_s x = NoPerm)"  
    
lemma empty_strong_disj_use_env1: "strong_disj_use_env empty_use_env r_s"
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: empty_use_env_def)
  done

lemma empty_strong_disj_use_env2: "strong_disj_use_env r_s empty_use_env"
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: empty_use_env_def)
  done    
  
lemma comm_strong_disj_use_env: "\<lbrakk> strong_disj_use_env r_s r_x \<rbrakk> \<Longrightarrow> strong_disj_use_env r_x r_s"    
  apply (simp add: strong_disj_use_env_def)
  apply (auto)
  done        
    
lemma strong_disj_leq_use_env1: "\<lbrakk> strong_disj_use_env r_s r_ex; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> strong_disj_use_env r_x r_ex"
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  done        

lemma strong_disj_leq_use_env2: "\<lbrakk> strong_disj_use_env r_ex r_s; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> strong_disj_use_env r_ex r_x"
  apply (rule_tac comm_strong_disj_use_env)  
  apply (rule_tac r_s="r_s" in strong_disj_leq_use_env1)
   apply (rule_tac comm_strong_disj_use_env)
   apply (auto)
  done
    
lemma reduce_strong_disj_use_env: "\<lbrakk> disj_use_env r_s r_x; strong_use_env r_x \<rbrakk> \<Longrightarrow> strong_disj_use_env r_s r_x"
  apply (simp add: disj_use_env_def)
  apply (simp add: strong_use_env_def)
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma add_strong_disj_use_env: "\<lbrakk> strong_disj_use_env r_x r_s; r_s x = NoPerm \<rbrakk> \<Longrightarrow> strong_disj_use_env (add_use_env r_x x r) r_s"
  apply (simp add: strong_disj_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  apply (simp add: add_use_env_def)
  apply (auto)
  done
    
lemma diff_strong_disj_use_env: "\<lbrakk> strong_use_env r_x \<rbrakk> \<Longrightarrow> strong_disj_use_env (diff_use_env r_s r_x) r_x"    
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: strong_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  done    
 
lemma strong_disj_comp_use_env1: "\<lbrakk> strong_disj_use_env r_ex r_x; strong_disj_use_env r_ex r_s \<rbrakk> \<Longrightarrow> strong_disj_use_env r_ex (comp_use_env r_x r_s)"    
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done
 
lemma strong_disj_comp_use_env2: "\<lbrakk> strong_disj_use_env r_x r_ex; strong_disj_use_env r_s r_ex \<rbrakk> \<Longrightarrow> strong_disj_use_env (comp_use_env r_x r_s) r_ex"     
  apply (rule_tac comm_strong_disj_use_env)
  apply (rule_tac strong_disj_comp_use_env1)
   apply (simp_all add: comm_strong_disj_use_env)
  done 
    
    (* ### NEW DISJOINTNESS *)

    
definition disj_nres_map where
  "disj_nres_map rs_map = (\<forall> x y. x \<noteq> y \<longrightarrow> strong_disj_use_env (nres_lookup rs_map x) (nres_lookup rs_map y))"  
  
  
  
definition sep_nres_map where
  "sep_nres_map r_s rs_map = (\<forall> x. strong_disj_use_env r_s (nres_lookup rs_map x))"     
    
lemma add_sep_nres_map: "\<lbrakk> sep_nres_map r_x rs_map; strong_disj_use_env r_x r_s \<rbrakk> \<Longrightarrow> sep_nres_map r_x (add_env rs_map x r_s)"    
  apply (simp add: sep_nres_map_def)
  apply (simp add: nres_lookup_def)
  apply (simp add: add_env_def)
  done  
  
lemma leq_sep_nres_map: "\<lbrakk> leq_use_env r_x r_s; sep_nres_map r_s rs_map \<rbrakk> \<Longrightarrow> sep_nres_map r_x rs_map"      
  apply (simp add: sep_nres_map_def)
  apply (auto)
  apply (rule_tac r_s="r_s" in strong_disj_leq_use_env1)
   apply (auto)
  done
    
lemma comp_sep_nres_map: "\<lbrakk> sep_nres_map r_s rs_map; sep_nres_map r_x rs_map \<rbrakk> \<Longrightarrow> sep_nres_map (comp_use_env r_s r_x) rs_map"    
  apply (simp add: sep_nres_map_def)
  apply (auto)
  apply (rule_tac strong_disj_comp_use_env2)
   apply (auto)
  done    
    
lemma disj_add_nres_map: "\<lbrakk> disj_nres_map rs_map;
  sep_nres_map r_s (rem_env rs_map x) \<rbrakk> \<Longrightarrow> disj_nres_map (add_env rs_map x r_s)"
  apply (simp add: disj_nres_map_def)
  apply (auto)
  apply (case_tac "x = xa")
   apply (auto)
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" and y="y" in nres_add_diff)
    apply (auto)
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" in nres_add_same)
   apply (auto)
    apply (simp add: sep_nres_map_def)
   apply (erule_tac x="x" in allE)
   apply (erule_tac x="y" in allE)
   apply (cut_tac rs_map="rs_map" and x="x" and y="y" in nres_rem_diff)
    apply (auto)
  apply (case_tac "x = y")
   apply (auto)
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" and y="xa" in nres_add_diff)
    apply (auto)
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" in nres_add_same)
   apply (auto)
   apply (rule_tac comm_strong_disj_use_env)
   apply (simp add: sep_nres_map_def)
   apply (erule_tac x="x" in allE)
   apply (erule_tac x="xa" in allE)
   apply (cut_tac rs_map="rs_map" and x="x" and y="xa" in nres_rem_diff)  
    apply (auto)
  apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" and y="xa" in nres_add_diff)
  apply (auto)
  apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" and y="y" in nres_add_diff)
  apply (auto)
  done    
    
end