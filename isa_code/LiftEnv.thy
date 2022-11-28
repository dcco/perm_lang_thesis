theory LiftEnv
  imports PermEnvMisc
begin
  
fun lift_use_env where
  "lift_use_env env NoPerm = env"
| "lift_use_env env UsePerm = env"
| "lift_use_env env OwnPerm = (\<lambda> x. if env x = NoPerm then NoPerm else OwnPerm)"
  
  (*
      only value types can be sent with no permission.
      function types may only be sent with ownership if they themselves do not
      require ownership.
      array types may use onwership if they are sent with ownership
   *)

fun safe_use_lift where
  "safe_use_lift env UsePerm = (\<forall> x. env x \<noteq> OwnPerm)"
| "safe_use_lift env NoPerm = (\<forall> x. env x = NoPerm)"
| "safe_use_lift env OwnPerm = True"  
 
lemma lift_use_none: "\<lbrakk> r_s x = NoPerm \<rbrakk> \<Longrightarrow> lift_use_env r_s r x = NoPerm"
  apply (case_tac r)
    apply (auto)
  done  

lemma lift_use_own: "\<lbrakk> r_s x = OwnPerm; safe_use_lift r_s r \<rbrakk> \<Longrightarrow> lift_use_env r_s r x = OwnPerm"    
  apply (case_tac r)
    apply (auto)
  done       
    
    (* 
      ####################################
        P1. lift equality lemmas
      ####################################
    *)     
    
    (* - simple lift lemmas *)

lemma cancel_lift_use_env_gen: "\<lbrakk> leq_perm r' r \<rbrakk> \<Longrightarrow> lift_use_env (lift_use_env r_s r') r = lift_use_env r_s r"    
  apply (case_tac "\<forall> x. lift_use_env (lift_use_env r_s r') r x = lift_use_env r_s r x")
   apply (auto)
  apply (case_tac r')
    apply (auto)
  apply (case_tac r)
    apply (auto)
  done

lemma cancel_lift_use_env: "lift_use_env (lift_use_env r_s r) r = lift_use_env r_s r" 
  apply (rule_tac cancel_lift_use_env_gen)
  apply (case_tac r)
    apply (auto)
  done    

lemma ann_lift_use_env: "\<lbrakk> r = OwnPerm \<rbrakk> \<Longrightarrow> diff_use_env (lift_use_env r_s q) (lift_use_env r_s r) = empty_use_env"  
  apply (case_tac "\<forall> x. diff_use_env (lift_use_env r_s q) (lift_use_env r_s r) x = empty_use_env x")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: empty_use_env_def)
  apply (case_tac q)
    apply (auto)
    apply (case_tac "r_s x")
      apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
lemma lift_rem_use_env: "lift_use_env (rem_use_env r_s x) r = rem_use_env (lift_use_env r_s r) x"
  apply (case_tac "\<forall> x'. lift_use_env (rem_use_env r_s x) r x' = rem_use_env (lift_use_env r_s r) x x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  apply (case_tac r)
    apply (auto)
  done        

lemma lift_empty_use_env: "lift_use_env empty_use_env r = empty_use_env"
  apply (case_tac "\<forall> x. lift_use_env empty_use_env r x = empty_use_env x")
   apply (auto)
  apply (case_tac r)
    apply (auto)
  apply (simp add: empty_use_env_def)
  done        
    
    (* - diff / lift lemmas *)

lemma lift_diff_use_env: "diff_use_env (lift_use_env r_s r) r_x = lift_use_env (diff_use_env r_s r_x) r"
  apply (case_tac "\<forall> x. diff_use_env (lift_use_env r_s r) r_x x = lift_use_env (diff_use_env r_s r_x) r x")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (case_tac r)
    apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
 
lemma cancel_diff_lift_use_env: "\<lbrakk> is_own r \<rbrakk> \<Longrightarrow> diff_use_env (lift_use_env r_x q) (lift_use_env r_x r) = empty_use_env"
  apply (case_tac "\<forall> x. diff_use_env (lift_use_env r_x q) (lift_use_env r_x r) x = empty_use_env x")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: empty_use_env_def)
  apply (simp add: is_own_def)
  apply (case_tac q)
    apply (auto)
    apply (case_tac "r_x x")
      apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done    

lemma lhs_lift_diff_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> diff_use_env r_x (lift_use_env r_s r) = diff_use_env (lift_use_env r_x r) (lift_use_env r_s r)"
  apply (case_tac "\<forall> x. diff_use_env r_x (lift_use_env r_s r) x = diff_use_env (lift_use_env r_x r) (lift_use_env r_s r) x")
   apply (auto)
  apply (simp add: leq_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (simp add: diff_use_env_def)
  apply (case_tac r)
    apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done    
(*
lemma comm_lift_diff_use_env: "diff_use_env (lift_use_env r_s r) r_x = lift_use_env (diff_use_env r_s r_x) r"
  apply (case_tac "\<forall> x. lift_use_env (diff_use_env r_s r_x) r x = diff_use_env (lift_use_env r_s r) r_x x")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: minus_use_env_def)
  apply (simp add: neg_use_env_def)
  apply (case_tac r)
    apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done*)

lemma outer_lift_diff_use_env: "lift_use_env (diff_use_env r_s r_x) r = diff_use_env (lift_use_env r_s r) r_x"
  apply (case_tac "\<forall> x. lift_use_env (diff_use_env r_s r_x) r x = diff_use_env (lift_use_env r_s r) r_x x")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (case_tac r)
    apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done

        (* - comp / lift lemmas *)
    
lemma lift_comp_use_env: "lift_use_env (comp_use_env r_s r_x) r = comp_use_env (lift_use_env r_s r) (lift_use_env r_x r)"
  apply (case_tac "\<forall> x. lift_use_env (comp_use_env r_s r_x) r x = comp_use_env (lift_use_env r_s r) (lift_use_env r_x r) x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (case_tac "r")
    apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done    

lemma foil_comp_lift_use_env: "lift_use_env r_s (comp_use_env r_xa r_xb x) = comp_use_env (lift_use_env r_s (r_xa x)) (lift_use_env r_s (r_xb x))"    
  apply (case_tac "\<not> (\<forall> x'. lift_use_env r_s (comp_use_env r_xa r_xb x) x' = comp_use_env (lift_use_env r_s (r_xa x)) (lift_use_env r_s (r_xb x)) x')")  
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (case_tac "r_xa x")
    apply (auto)
    apply (case_tac "r_xb x")
      apply (auto)
      apply (case_tac "r_s x'")
        apply (auto)
     apply (case_tac "r_s x'")
       apply (auto)
    apply (case_tac "r_s x'")
      apply (auto)
   apply (case_tac "r_xb x")
     apply (auto)
     apply (case_tac "r_s x'")
       apply (auto)
    apply (case_tac "r_s x'")
      apply (auto)
   apply (case_tac "r_s x'")
     apply (auto)
  apply (case_tac "r_s x'")
    apply (auto)
  apply (case_tac "r_xb x")
    apply (auto)
  done        
    
    (* 
      ####################################
        P1. lift ordering lemmas
      ####################################
    *)  
    
lemma self_lift_leq_use_env: "leq_use_env r_s (lift_use_env r_s r)"
  apply (simp add: leq_use_env_def)
  apply (case_tac r)
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
lemma lift_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x (lift_use_env r_s r)"    
  apply (rule_tac r_sb="r_s" in trans_leq_use_env)
   apply (rule_tac self_lift_leq_use_env)
  apply (simp)
  done    
    
lemma lift_leq_use_env_rev: "\<lbrakk> leq_use_env (lift_use_env r_x r) r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x r_s"    
  apply (rule_tac r_sb="lift_use_env r_x r" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac self_lift_leq_use_env)
  done    

lemma dist_lift_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (lift_use_env r_x r) (lift_use_env r_s r)"
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac r)
    apply (auto)
  apply (case_tac "r_x x")
  apply (auto)
  done
    
lemma dist_lift_leq_use_env_gen: "\<lbrakk> leq_perm q r \<rbrakk> \<Longrightarrow> leq_use_env (lift_use_env r_s q) (lift_use_env r_s r)"
  apply (case_tac q)
    apply (auto)
    apply (rule_tac self_lift_leq_use_env)
   apply (rule_tac self_lift_leq_use_env)
  apply (case_tac r)
    apply (auto)
  apply (simp add: leq_use_env_def)
  done     

lemma lhs_lift_leq_use_env: "\<lbrakk> leq_use_env r_x (lift_use_env r_s r); is_own r \<rbrakk> \<Longrightarrow> leq_use_env (lift_use_env r_x q) (lift_use_env r_s r)"    
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (simp add: is_own_def)
  apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  apply (case_tac q)
    apply (auto)
  done    
    
lemma lhs_lift_leq_use_env_gen: "\<lbrakk> leq_use_env r_x (lift_use_env r_s r); leq_perm q r \<rbrakk> \<Longrightarrow> leq_use_env (lift_use_env r_x q) (lift_use_env r_s r)"    
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac r)
    apply (auto)
    apply (case_tac q)
      apply (auto)
   apply (case_tac q)
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  apply (case_tac q)
    apply (auto)
  done    

    (* - diff / lift lemmas *)
    
lemma spec_diff_lift_leq_use_env: "leq_use_env (diff_use_env (lift_use_env r_s r) (lift_use_env r_s r)) (diff_use_env r_s (lift_use_env r_s r))"
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (case_tac r)
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done

lemma spec_diff_lift_leq_use_env_gen: "\<lbrakk> leq_perm q r \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env (lift_use_env r_s q) (lift_use_env r_s r)) (diff_use_env r_s (lift_use_env r_s r))"
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (case_tac q)
    apply (auto)
     apply (case_tac r)
       apply (auto)
      apply (case_tac "r_s x")
        apply (auto)
     apply (case_tac "r_s x")
       apply (auto)
    apply (case_tac r)
      apply (auto)
    apply (case_tac "r_s x")
      apply (auto)
      apply (case_tac "r_s x")
        apply (auto)
   apply (case_tac r)
     apply (auto)
  apply (case_tac r)
    apply (auto)
  done
    
lemma cancel_lift_leq_use_env: "\<lbrakk> is_own r \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env (lift_use_env r_s r) (lift_use_env r_s r)) r_ex"    
  apply (simp add: is_own_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: leq_use_env_def)
  done    
 
    (* 
      ####################################
        P1. misc lift lemmas
      ####################################
    *)      
  
lemma disj_lift_use_envr: "\<lbrakk> disj_use_env r_s (lift_use_env r_x r) \<rbrakk> \<Longrightarrow> disj_use_env r_s r_x"
  apply (rule_tac r_s="lift_use_env r_x r" in disj_leq_use_env2)
   apply (auto)
  apply (rule_tac self_lift_leq_use_env)
  done        
 
lemma weak_lift_use_env: "\<lbrakk> weak_use_env r_s; r \<noteq> OwnPerm \<rbrakk> \<Longrightarrow> weak_use_env (lift_use_env r_s r)"    
  apply (simp add: weak_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac r)
    apply (auto)
  done    
    
lemma weak_lift_empty_use_env: "weak_use_env (lift_use_env empty_use_env r)"    
  apply (simp add: weak_use_env_def)
  apply (auto)
  apply (case_tac r)
    apply (auto)
    apply (simp add: empty_use_env_def)
   apply (simp add: empty_use_env_def)
  apply (simp add: empty_use_env_def)
  done
    
    (* 
      ####################################
        P1. lift safety lemmas
      ####################################
    *)  
    
lemma self_safe_leq_perm: "\<lbrakk> safe_use_lift r_s r \<rbrakk> \<Longrightarrow> leq_perm (r_s x) r"
  apply (case_tac r)
    apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done    
    
lemma safe_lift_leq_use_env: "\<lbrakk> leq_use_env r_x r_s; safe_use_lift r_s r \<rbrakk> \<Longrightarrow> safe_use_lift r_x r"
  apply (simp add: leq_use_env_def)
  apply (case_tac r)
    apply (auto)
   apply (erule_tac x="x" in allE)
   apply (case_tac "r_x x")
    apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_s x")
    apply (auto)
  done    
 
lemma safe_lift_empty_use_env: "\<lbrakk> safe_use_lift r_s r \<rbrakk> \<Longrightarrow> safe_use_lift empty_use_env r" 
  apply (case_tac r)
    apply (simp_all add: empty_use_env_def)
  done    
    
lemma safe_lift_rem_use_env: "\<lbrakk> safe_use_lift r_s r \<rbrakk> \<Longrightarrow> safe_use_lift (rem_use_env r_s x) r"
  apply (simp add: rem_use_env_def)
  apply (case_tac r)
    apply (auto)
  done        

lemma safe_lift_leq_perm: "\<lbrakk> safe_use_lift r_s r'; leq_perm r' r \<rbrakk> \<Longrightarrow> safe_use_lift r_s r"    
  apply (case_tac r)
    apply (auto)
   apply (case_tac r')
     apply (auto)
  apply (case_tac r')
    apply (auto)
  done

lemma safe_lift_comp_use_env: "\<lbrakk> safe_use_lift r_s r; safe_use_lift r_x r \<rbrakk> \<Longrightarrow> safe_use_lift (comp_use_env r_s r_x) r"
  apply (case_tac r)
    apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (simp add: comp_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
(*
lemma safe_lift_perm_use_env: "\<lbrakk> leq_perm q r; safe_use_lift r_s q \<rbrakk> \<Longrightarrow> safe_use_lift r_s r"
  apply (case_tac q)
    apply (auto)
   apply (case_tac r)
     apply (auto)
  apply (case_tac r)
    apply (auto)
  done*)

lemma safe_lift_cancel_use_env: "\<lbrakk> safe_use_lift r_x q; r = OwnPerm \<rbrakk> \<Longrightarrow> safe_use_lift (diff_use_env r_s (lift_use_env r_s r)) q"    
  apply (auto)
  apply (simp add: diff_use_env_def)
  apply (case_tac q)
    apply (auto)
  done

lemma safe_lift_diff_use_env: "\<lbrakk> safe_use_lift r_s r \<rbrakk> \<Longrightarrow> safe_use_lift (diff_use_env r_s r_x) r"    
  apply (case_tac r)
    apply (auto)
   apply (simp add: diff_use_env_def)
   apply (case_tac "r_x x")
     apply (auto)
  apply (simp add: diff_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  done
  
lemma safe_lift_twice_use_env: "\<lbrakk> safe_use_lift r_s q; leq_perm q r \<rbrakk> \<Longrightarrow> safe_use_lift (lift_use_env r_s q) r"    
  apply (case_tac q)
    apply (auto)
   apply (case_tac r)
     apply (auto)
  apply (case_tac r)
    apply (auto)
  apply (case_tac r)
    apply (auto)
  done  
  
end