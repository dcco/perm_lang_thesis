theory PermEnvLeq
  imports PermEnvEq
begin

    (* 
      ####################################
        P1. main ordering lemmas
      ####################################
    *)  
  
    (* - fundamental lemmas *)
  
lemma trans_leq_use_env: "\<lbrakk> leq_use_env r_sb r_sa; leq_use_env r_sc r_sb \<rbrakk> \<Longrightarrow> leq_use_env r_sc r_sa"
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_sa x")
    apply (auto)
   apply (case_tac "r_sb x")
     apply (auto)
  apply (case_tac "r_sb x")
    apply (auto)
  apply (case_tac "r_sc x")
    apply (auto)
  done   
    
lemma id_leq_use_env: "leq_use_env r r"    
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (case_tac "r x")
    apply (auto)
  done  
    
    (* - add / rem lemmas *)  
    
lemma add_leq_use_env: "\<lbrakk> leq_use_env r_x r_s; leq_perm r (r_s x) \<rbrakk> \<Longrightarrow> leq_use_env (add_use_env r_x x r) r_s"
  apply (simp add: leq_use_env_def)
  apply (simp add: add_use_env_def)
  done    
    
lemma add_leq_use_env_rev: "\<lbrakk> leq_use_env r_x (add_use_env r_s x r); r_x x = NoPerm \<rbrakk> \<Longrightarrow> leq_use_env r_x r_s"      
  apply (simp add: leq_use_env_def)
  apply (simp add: add_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (case_tac "x = xa")
   apply (auto)
  done

lemma self_add_leq_use_env: "\<lbrakk> leq_perm (r_s x) r \<rbrakk> \<Longrightarrow> leq_use_env r_s (add_use_env r_s x r)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: add_use_env_def)
  apply (auto)
  apply (case_tac "r_s xa")
    apply (auto)
  done

lemma rhs_add_leq_use_env: "\<lbrakk> leq_use_env r_x r_s; leq_perm (r_x x) r \<rbrakk> \<Longrightarrow> leq_use_env r_x (add_use_env r_s x r)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: add_use_env_def)
  done
    
lemma dist_add_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (add_use_env r_x x r) (add_use_env r_s x r)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: add_use_env_def)
  apply (case_tac r)
    apply (auto)
  done    
    
lemma dist_add_leq_use_env_gen: "\<lbrakk> leq_use_env r_x r_s; leq_perm r r' \<rbrakk> \<Longrightarrow> leq_use_env (add_use_env r_x x r) (add_use_env r_s x r')"
  apply (simp add: leq_use_env_def)
  apply (simp add: add_use_env_def)
  done
    
lemma self_rem_leq_use_env: "leq_use_env (rem_use_env r_s x) r_s"    
  apply (simp add: leq_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (auto)
  apply (case_tac "r_s xa")
    apply (auto)
  done    

lemma rem_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (rem_use_env r_x x) r_s"    
  apply (rule_tac r_sb="r_x" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac self_rem_leq_use_env)
  done
 
lemma rhs_rem_leq_use_env: "\<lbrakk> r_x x = NoPerm; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x (rem_use_env r_s x)"  
  apply (simp add: leq_use_env_def)
  apply (simp add: rem_use_env_def)
  done         
    
lemma rem_leq_use_env_rev: "\<lbrakk> leq_use_env (rem_use_env r_x x) r_s \<rbrakk> \<Longrightarrow> leq_use_env (rem_use_env r_x x) (rem_use_env r_s x)"  
  apply (simp add: rem_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  done    

lemma dist_rem_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (rem_use_env r_x x) (rem_use_env r_s x)"    
  apply (rule_tac rem_leq_use_env_rev)
  apply (rule_tac rem_leq_use_env)
  apply (simp)
  done       
    
lemma self_rem_add_leq_use_env: "leq_use_env (rem_use_env r_s x) (add_use_env r_s x r)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (simp add: add_use_env_def)
  apply (auto)
  apply (case_tac "r_s xa")
    apply (auto)
  done

lemma rem_add_leq_use_env: "\<lbrakk> leq_use_env r_x (add_use_env r_s x r) \<rbrakk> \<Longrightarrow> leq_use_env (rem_use_env r_x x) r_s"    
  apply (simp add: add_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  done    
    
lemma cancel_rem_add_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (rem_use_env r_x x) (add_use_env r_s x r)"
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (simp add: rem_use_env_def)
  apply (simp add: add_use_env_def)
  done        

lemma lhs_rem_leq_use_env: "\<lbrakk> leq_use_env (rem_use_env r_x x) r_s; leq_use_env (one_use_env x OwnPerm) r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x r_s"    
  apply (simp add: leq_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (simp add: one_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (erule_tac x="xa" in allE)
  apply (case_tac "x = xa")
   apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
    (* - diff lemmas *) 
    
lemma self_diff_leq_use_env: "leq_use_env (diff_use_env r_s r_x) r_s"
  apply (simp add: diff_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done    
    
lemma diff_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env r_x r_ex) r_s"
  apply (simp add: diff_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done

lemma rhs_weak_leq_use_env: "\<lbrakk> weak_use_env r_x; leq_use_env r_ex r_s \<rbrakk> \<Longrightarrow> leq_use_env r_ex (diff_use_env r_s r_x)"    
  apply (cut_tac r_x="r_x" and r_s="r_s" in weak_diff_use_env) 
   apply (auto)
  done    

lemma dist_diff_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env r_x r_ex) (diff_use_env r_s r_ex)"
  apply (simp add: diff_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done    
    
lemma dist_diff_leq_use_env_gen: "\<lbrakk> leq_use_env r_sa r_sb; leq_use_env r_xb r_xa \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env r_sa r_xa) (diff_use_env r_sb r_xb)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_xa x")
    apply (auto)
   apply (case_tac "r_xb x")
     apply (auto)
  apply (case_tac "r_xb x")
    apply (auto)
  done    
   
lemma rhs_diff_leq_use_env: "\<lbrakk> leq_use_env (diff_use_env r_x r_ex) r_s \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env r_x r_ex) (diff_use_env r_s r_ex)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_ex x")
    apply (auto)
  done    
   
lemma rhs_self_diff_leq_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow> leq_use_env r_x (diff_use_env r_x r_ex)"
  apply (simp add: diff_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done        
    
    (* - add / rem / diff lemmas *)
    
lemma add_diff_leq_use_env: "leq_use_env (diff_use_env (add_use_env r_s x r) r_x) (add_use_env (diff_use_env r_s r_x) x r)"
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: add_use_env_def)
  apply (auto)
   apply (case_tac "r")
     apply (auto)
    apply (case_tac "r_x x")
      apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x xa")
    apply (auto)
   apply (case_tac "r_s xa")
     apply (auto)
  apply (case_tac "r_s xa")
    apply (auto)
  done    
    
lemma rhs_diff_rem_leq_use_env: "\<lbrakk> r_x x = NoPerm; leq_use_env (diff_use_env r_x r_ex) (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env r_x (rem_use_env r_ex x)) (diff_use_env r_s r_ex)"  
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: rem_use_env_def)
  done
  
lemma rhs_diff_rem_leq_use_env2: "\<lbrakk> r_ex x \<noteq> OwnPerm; leq_use_env (diff_use_env r_x r_ex) (diff_use_env r_s r_ex) \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env r_x (rem_use_env r_ex x)) (diff_use_env r_s r_ex)"  
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_ex x")
    apply (auto)
  done    
    
    (* - comp lemmas *)
   
lemma self_comp_leq_use_env1: "leq_use_env r_s (comp_use_env r_s r_x)"
  apply (simp add: leq_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma self_comp_leq_use_env2: "leq_use_env r_s (comp_use_env r_x r_s)"
  apply (simp add: leq_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma comp_leq_use_env1: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x (comp_use_env r_s r_ex)"    
  apply (rule_tac r_sb="r_s" in trans_leq_use_env)
   apply (rule_tac self_comp_leq_use_env1)
  apply (simp)
  done    
    
lemma comp_leq_use_env2: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x (comp_use_env r_ex r_s)"    
  apply (rule_tac r_sb="r_s" in trans_leq_use_env)
   apply (rule_tac self_comp_leq_use_env2)
  apply (simp)
  done    
    
lemma dist_comp_leq_use_env: "\<lbrakk> leq_use_env r_xa r_s; leq_use_env r_xb r_s \<rbrakk> \<Longrightarrow> leq_use_env (comp_use_env r_xa r_xb) r_s"    
  apply (simp add: leq_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_xa x")
    apply (auto)
   apply (case_tac "r_xb x")
     apply (auto)
  apply (case_tac "r_xb x")
    apply (auto)
  done
    
    (* - comp / diff lemmas *)
    
lemma diff_comp_leq_use_env1: "leq_use_env (diff_use_env (diff_use_env r_s r_x) r_ex) (diff_use_env r_s (comp_use_env r_x r_ex))"
  apply (cut_tac r_s="r_s" and r_x="r_x" and r_ex="r_ex" in diff_comp_use_env)
  apply (auto)
  apply (rule_tac id_leq_use_env)
  done
    
lemma diff_comp_leq_use_env2: "leq_use_env (diff_use_env r_s (comp_use_env r_x r_ex)) (diff_use_env (diff_use_env r_s r_x) r_ex)"
  apply (cut_tac r_s="r_s" and r_x="r_x" and r_ex="r_ex" in diff_comp_use_env)
  apply (auto)
  apply (rule_tac id_leq_use_env)
  done

lemma st_diff_comp_leq_use_env: "leq_use_env (diff_use_env r_x r_ex) r_s \<Longrightarrow> leq_use_env r_x (comp_use_env r_s r_ex)"
  apply (simp add: comp_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
    apply (case_tac "r_ex x")
      apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done
  
lemma prec_diff_leq_use_env: "\<lbrakk> leq_use_env (diff_use_env r_s r_xa) (diff_use_env r_s r_xb); leq_use_env (diff_use_env r_s r_xa) (diff_use_env r_s r_xc) \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env r_s r_xa) (diff_use_env r_s (comp_use_env r_xb r_xc))"
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_s x")
    apply (auto)
    apply (case_tac "r_xa x")
      apply (auto)
   apply (case_tac "r_xb x")
     apply (auto)
    apply (case_tac "r_xc x")
      apply (auto)
   apply (case_tac "r_xc x")
     apply (auto)
  apply (case_tac "r_xb x")
    apply (auto)
   apply (case_tac "r_xc x")
     apply (auto)
  apply (case_tac "r_xc x")
    apply (auto)
  done    
    
    (* - empty lemmas *)
    
lemma leq_empty_use_env: "leq_use_env empty_use_env r"
  apply (simp add: leq_use_env_def)
  apply (simp add: empty_use_env_def)
  done    

lemma empty_diff_leq_use_env: "leq_use_env (diff_use_env empty_use_env r_x) r_s"
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: empty_use_env_def)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
    (* 
      ####################################
        P2. disjoint-ness based ordering lemmas
      ####################################
    *)  
    
lemma mini_disj_diff_leq_use_env: "\<lbrakk> leq_use_env r_x r_s; mini_disj_use_env r_ex r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x (diff_use_env r_s r_ex)"  
  apply (simp add: diff_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (simp add: mini_disj_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done        

lemma mini_disj_diff_leq_use_env2: "\<lbrakk>leq_use_env r_x r_s; mini_disj_use_env r_ex r_x\<rbrakk> \<Longrightarrow> leq_use_env r_x (diff_use_env r_s r_ex)"  
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (simp add: diff_use_env_def)
  apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done      
    
lemma self_disj_diff_leq_use_env: "\<lbrakk> disj_use_env r_s r_x \<rbrakk> \<Longrightarrow> leq_use_env r_s (diff_use_env r_s r_x)"    
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done    
    
lemma disj_diff_leq_use_env: "\<lbrakk> disj_use_env r_ex r_x; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x (diff_use_env r_s r_ex)"
  apply (rule_tac r_sb="diff_use_env r_x r_ex" in trans_leq_use_env)
   apply (rule_tac dist_diff_leq_use_env)
   apply (simp)
  apply (rule_tac mini_disj_diff_leq_use_env)
   apply (rule_tac id_leq_use_env)
  apply (simp add: disj_use_env_def)
  done     

lemma lhs_ddl_use_env: "\<lbrakk> disj_use_env r_s r_x \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env r_s (diff_use_env r_ex r_x)) (diff_use_env r_s r_ex)"
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "diff_perm (r_s x) (r_ex x)")
     apply (auto)
  apply (case_tac "diff_perm (r_s x) (r_ex x)")
    apply (auto)
  done    
    
    (* 
      ####################################
        P3. differential ordering lemmas
      ####################################
    *)  
    
lemma rhs_fold_dcl_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env r_s (comp_use_env r_sa r_sb)) \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (diff_use_env (diff_use_env r_s r_sa) r_sb)"
  apply (cut_tac r_s="r_s" and r_x="r_sa" and r_ex="r_sb" in diff_comp_use_env)
  apply (auto)
  done    
 
lemma lhs_fold_dcl_use_env: "\<lbrakk> leq_use_env (diff_use_env r_x (comp_use_env r_xa r_xb)) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env (diff_use_env r_x r_xa) r_xb) r_s"
  apply (cut_tac r_s="r_x" and r_x="r_xa" and r_ex="r_xb" in diff_comp_use_env)
  apply (auto)
  done      

lemma fold_dcl_use_env: "\<lbrakk> leq_use_env (diff_use_env r_x (comp_use_env r_xa r_xb)) (diff_use_env r_s (comp_use_env r_sa r_sb)) \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env (diff_use_env r_x r_xa) r_xb) (diff_use_env (diff_use_env r_s r_sa) r_sb)"
  apply (cut_tac r_s="r_x" and r_x="r_xa" and r_ex="r_xb" in diff_comp_use_env)
  apply (cut_tac r_s="r_s" and r_x="r_sa" and r_ex="r_sb" in diff_comp_use_env)
  apply (auto)
  done    
    
lemma rhs_unroll_dcl_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env (diff_use_env r_s r_sa) r_sb) \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (diff_use_env r_s (comp_use_env r_sa r_sb))"
  apply (cut_tac r_s="r_s" and r_x="r_sa" and r_ex="r_sb" in diff_comp_use_env)
  apply (auto)
  done    
 
lemma lhs_unroll_dcl_use_env: "\<lbrakk> leq_use_env (diff_use_env (diff_use_env r_x r_xa) r_xb) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env r_x (comp_use_env r_xa r_xb)) r_s"
  apply (cut_tac r_s="r_x" and r_x="r_xa" and r_ex="r_xb" in diff_comp_use_env)
  apply (auto)
  done       
    
lemma unroll_dcl_use_env: "\<lbrakk> leq_use_env (diff_use_env (diff_use_env r_x r_xa) r_xb) (diff_use_env (diff_use_env r_s r_sa) r_sb) \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env r_x (comp_use_env r_xa r_xb)) (diff_use_env r_s (comp_use_env r_sa r_sb))"
  apply (cut_tac r_s="r_x" and r_x="r_xa" and r_ex="r_xb" in diff_comp_use_env)
  apply (cut_tac r_s="r_s" and r_x="r_sa" and r_ex="r_sb" in diff_comp_use_env)
  apply (auto)
  done    
    
lemma lhs_dist_dcl_use_env: "\<lbrakk> leq_use_env (comp_use_env (diff_use_env r_sa r_sx) (diff_use_env r_sb r_sx)) r_x \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env (comp_use_env r_sa r_sb) r_sx) r_x"
  apply (cut_tac r_s="r_sa" and r_x="r_sb" and r_ex="r_sx" in dist_diff_comp_use_env)
  apply (auto)
  done

lemma rhs_dist_dcl_use_env: "\<lbrakk> leq_use_env r_x (comp_use_env (diff_use_env r_sa r_sx) (diff_use_env r_sb r_sx)) \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (diff_use_env (comp_use_env r_sa r_sb) r_sx)"
  apply (cut_tac r_s="r_sa" and r_x="r_sb" and r_ex="r_sx" in dist_diff_comp_use_env)
  apply (auto)
  done     

lemma rhs_flip_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env r_s (comp_use_env r_sb r_sa)) \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (diff_use_env r_s (comp_use_env r_sa r_sb))"
  apply (cut_tac r_s="r_sa"and r_x="r_sb" in comm_comp_use_env)
  apply (auto)
  done

lemma lhs_flip_use_env: "\<lbrakk> leq_use_env (diff_use_env r_x (comp_use_env r_xb r_xa)) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env r_x (comp_use_env r_xa r_xb)) r_s"
  apply (cut_tac r_s="r_xa"and r_x="r_xb" in comm_comp_use_env)
  apply (auto)
  done

lemma rhs_pull_comp_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env r_s (comp_use_env r_sa (comp_use_env r_sb r_sc))) \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (diff_use_env r_s (comp_use_env (comp_use_env r_sa r_sb) r_sc))"
  apply (cut_tac r_ex="r_sa" and r_s="r_sb"and r_x="r_sc" in assoc_comp_use_env)
  apply (auto)
  done    

lemma lhs_pull_comp_use_env: "\<lbrakk> leq_use_env (diff_use_env r_x (comp_use_env r_xa (comp_use_env r_xb r_xc))) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env r_x (comp_use_env (comp_use_env r_xa r_xb) r_xc)) r_s"
  apply (cut_tac r_ex="r_xa" and r_s="r_xb"and r_x="r_xc" in assoc_comp_use_env)
  apply (auto)
  done    

lemma rhs_rotate_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env r_s (comp_use_env (comp_use_env r_sb r_sa) r_sc)) \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (diff_use_env r_s (comp_use_env (comp_use_env r_sa r_sb) r_sc))"
  apply (cut_tac r_s="r_sa" and r_x="r_sb" in comm_comp_use_env)
  apply (auto)
  done    
    
lemma lhs_rotate_use_env: "\<lbrakk> leq_use_env (diff_use_env r_x (comp_use_env (comp_use_env r_xb r_xa) r_xc)) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env r_x (comp_use_env (comp_use_env r_xa r_xb) r_xc)) r_s"
  apply (cut_tac r_s="r_xa" and r_x="r_xb" in comm_comp_use_env)
  apply (auto)
  done    
 
lemma rhs_unroll_rem_use_env: "\<lbrakk> leq_use_env r_x (rem_use_env r_s x) \<rbrakk> \<Longrightarrow> leq_use_env r_x (diff_use_env r_s (one_use_env x OwnPerm))"    
  apply (cut_tac r_s="r_s" and x="x" in diff_rem_use_env)  
  apply (auto)
  done
 
lemma lhs_unroll_rem_use_env: "\<lbrakk> leq_use_env (rem_use_env r_x x) r_s \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env r_x (one_use_env x OwnPerm)) r_s"    
  apply (cut_tac r_s="r_x" and x="x" in diff_rem_use_env)  
  apply (auto)
  done 
 
lemma rhs_fold_rem_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env (diff_use_env r_s (one_use_env x OwnPerm)) r_ex) \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (diff_use_env (rem_use_env r_s x) r_ex)"    
  apply (cut_tac r_s="r_s" and x="x" in diff_rem_use_env)  
  apply (auto)
  done
 
lemma lhs_fold_rem_use_env: "\<lbrakk> leq_use_env (diff_use_env (diff_use_env r_x (one_use_env x OwnPerm)) r_ex) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env (rem_use_env r_x x) r_ex) r_s"    
  apply (cut_tac r_s="r_x" and x="x" in diff_rem_use_env)  
  apply (auto)
  done       
    
end