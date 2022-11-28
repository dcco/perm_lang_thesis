theory GenSubEnv
  imports GenEnv PermEnv
begin
  
    (* ##### sub env lemmas *)

definition sub_env :: "'a state_env \<Rightarrow> 'b res_env \<Rightarrow> bool" where
  "sub_env s env = (\<forall> x. env x \<noteq> None \<longrightarrow> (\<exists> y. x = Loc y \<and> s y \<noteq> None))"  
  
definition sub_use_env :: "'a state_env \<Rightarrow> perm_use_env \<Rightarrow> bool" where
  "sub_use_env s r_s = (\<forall> x. r_s x \<noteq>  NoPerm \<longrightarrow> (\<exists> y. x = Loc y \<and> s y \<noteq> None))"

definition contain_env :: "('a, 'b) gen_env \<Rightarrow> ('a, 'b) gen_env \<Rightarrow> bool" where
  "contain_env env env' = (\<forall> x. case env' x of None \<Rightarrow> True | Some tau \<Rightarrow> env x = Some tau)"  
  
    (* - sub env lemmas *)

lemma add_sub_env: "\<lbrakk> sub_env s env \<rbrakk> \<Longrightarrow> sub_env (add_env s x v) env"   
  apply (simp add: sub_env_def)
  apply (simp add: add_env_def)
  apply (auto)
  done  

lemma dist_add_sub_env: "\<lbrakk> sub_env s env \<rbrakk> \<Longrightarrow> sub_env (add_env s x v) (add_env env (Loc x) tau)"    
  apply (simp add: sub_env_def)
  apply (simp add: add_env_def)
  apply (auto)
  done  

lemma rhs_add_sub_env: "\<lbrakk> sub_env s env; s x \<noteq> None \<rbrakk> \<Longrightarrow> sub_env s (add_env env (Loc x) tau)"        
  apply (simp add: sub_env_def)
  apply (simp add: add_env_def)
  done  
    
lemma rem_sub_env: "\<lbrakk> sub_env s env \<rbrakk> \<Longrightarrow> sub_env s (rem_env env x)"
  apply (simp add: sub_env_def)
  apply (simp add: rem_env_def)
  done

lemma add_rem_sub_env: "\<lbrakk> sub_env (add_env s x v) env \<rbrakk> \<Longrightarrow> sub_env s (rem_env env (Loc x))"    
  apply (simp add: sub_env_def)
  apply (simp add: add_env_def)
  apply (simp add: rem_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  done

    (* - sub use env lemmas *)
  
lemma add_sub_use_env: "\<lbrakk> sub_use_env s r_s \<rbrakk> \<Longrightarrow> sub_use_env (add_env s x v) r_s"    
  apply (simp add: sub_use_env_def)
  apply (simp add: add_env_def)
  apply (auto)
  done
    
lemma rhs_add_sub_use_env: "\<lbrakk> sub_use_env s r_s; s x \<noteq> None \<rbrakk> \<Longrightarrow> sub_use_env s (add_use_env r_s (Loc x) r)"    
  apply (simp add: sub_use_env_def)
  apply (simp add: add_use_env_def)
  done

lemma rem_sub_use_env: "\<lbrakk> sub_use_env s r_s \<rbrakk> \<Longrightarrow> sub_use_env s (rem_use_env r_s x)"
  apply (simp add: sub_use_env_def)
  apply (simp add: rem_use_env_def)
  done

lemma add_rem_sub_use_env: "\<lbrakk> sub_use_env (add_env s x v) r_s \<rbrakk> \<Longrightarrow> sub_use_env s (rem_use_env r_s (Loc x))"    
  apply (simp add: sub_use_env_def)
  apply (simp add: add_env_def)
  apply (simp add: rem_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  done
    
lemma contain_sub_use_env: "\<lbrakk> sub_use_env s r_s; contain_env s' s \<rbrakk> \<Longrightarrow> sub_use_env s' r_s"    
  apply (simp add: sub_use_env_def)  
  apply (simp add: contain_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (erule_tac x="y" in allE)
  apply (auto)
  done
    
lemma empty_sub_use_env: "sub_use_env s empty_use_env"
  apply (simp add: sub_use_env_def)
  apply (simp add: empty_use_env_def)
  done  
  
lemma comp_sub_use_env: "\<lbrakk> sub_use_env s r_x; sub_use_env s r_s \<rbrakk> \<Longrightarrow> sub_use_env s (comp_use_env r_x r_s)"    
  apply (simp add: sub_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done   

    (* contain lemmas *)    
    
lemma trans_contain_env: "\<lbrakk> contain_env env_a env_b; contain_env env_b env_c \<rbrakk> \<Longrightarrow> contain_env env_a env_c"
  apply (simp add: contain_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "env_c x")
   apply (auto)
  done
        
lemma id_contain_env: "contain_env r_s r_s"    
  apply (simp add: contain_env_def)
  apply (auto)
  apply (case_tac "r_s x")
   apply (auto)
  done
  
lemma self_rem_contain_env: "contain_env env (rem_env env x)"    
  apply (simp add: contain_env_def)
  apply (simp add: rem_env_def)
  apply (auto)
  apply (case_tac "env xa")
   apply (auto)
  done
    
lemma rem_contain_env: "\<lbrakk> contain_env env' env \<rbrakk> \<Longrightarrow> contain_env env' (rem_env env x)"    
  apply (rule_tac env_b="env" in trans_contain_env)
   apply (simp)
  apply (rule_tac self_rem_contain_env)
  done
  
lemma add_contain_env: "\<lbrakk> env x = None \<rbrakk> \<Longrightarrow> contain_env (add_env env x tau) env"    
  apply (simp add: contain_env_def)
  apply (auto)
  apply (case_tac "env xa")
   apply (auto)
  apply (simp add: add_env_def)
  apply (auto)
  done    
    
lemma dist_add_contain_env: "\<lbrakk> contain_env r_s r_x \<rbrakk> \<Longrightarrow> contain_env (add_env r_s x t) (add_env r_x x t)"    
  apply (simp add: add_env_def)
  apply (simp add: contain_env_def)
  done    
  
lemma rem_add_contain_env: "\<lbrakk> contain_env r_s r_x \<rbrakk> \<Longrightarrow> contain_env (add_env r_s x t) (rem_env r_x x)"        
  apply (simp add: contain_env_def)
  apply (auto)
  apply (simp add: rem_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (case_tac "r_x xa")
   apply (auto)
  apply (simp add: add_env_def)
  done        
    
end