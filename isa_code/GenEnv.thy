theory GenEnv
  imports Main
begin

datatype res_id = Var string | Loc string  
  
type_synonym ('a, 'b) gen_env = "'b \<Rightarrow> 'a option"
  
type_synonym 'a res_env = "('a, res_id) gen_env"
  
type_synonym 'a state_env = "('a, string) gen_env"
 
definition empty_env where
  "empty_env x = None"  
  
definition add_env where
  "add_env env x t = (\<lambda> x'. if x = x' then Some t else env x')"  
    
definition rem_env where
  "rem_env env x = (\<lambda> x'. if x = x' then None else env x')"
  
definition fresh_var where
  "fresh_var s y = (s y = None)"      
  
    (* #### basic add/rem lemmas #### *)
  
lemma almost_comm_add_env: "\<lbrakk> x \<noteq> y \<rbrakk> \<Longrightarrow> add_env (add_env env y t) x t' = add_env (add_env env x t') y t"
  apply (simp add: add_env_def)
  apply (auto)
  done
    
lemma double_add_env: "add_env (add_env env x t) x t' = add_env env x t'"
  apply (simp add: add_env_def)
  apply (auto)
  done
  
lemma ignore_rem_env: "\<lbrakk> env x = None \<rbrakk> \<Longrightarrow> env = rem_env env x"    
  apply (case_tac "\<forall> x'. env x' = rem_env env x x'")
   apply (auto)
  apply (simp add: rem_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
  
lemma cancel_rem_add_env: "\<lbrakk> env x = None \<rbrakk> \<Longrightarrow> env = rem_env (add_env env x t) x"
  apply (case_tac "\<forall> x'. env x' = rem_env (add_env env x t) x x'")
   apply (auto)
  apply (simp add: add_env_def)
  apply (simp add: rem_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
    
lemma partial_add_rem_env: "add_env (rem_env env x) x t = add_env env x t"
  apply (case_tac "\<forall> x'. add_env (rem_env env x) x t x' = add_env env x t x'")
   apply (auto)
  apply (simp add: add_env_def)
  apply (case_tac "x = x'")
   apply (auto)  
  apply (simp add: rem_env_def)
  done
   
    
lemma cancel_add_rem_env: "\<lbrakk> env x = Some y \<rbrakk> \<Longrightarrow> env = add_env (rem_env env x) x y"
  apply (case_tac "\<forall> x'. env x' = add_env (rem_env env x) x y x'")
   apply (auto)
  apply (simp add: add_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  apply (simp add: rem_env_def)
  done

lemma partial_rem_add_env: "rem_env (add_env env x y) x = rem_env env x"    
  apply (case_tac "\<forall> x'. rem_env (add_env env x y) x x' = rem_env env x x'")
   apply (auto)
  apply (simp add: rem_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  apply (simp add: add_env_def)
  done    
    
lemma almost_comm_add_rem_env: "\<lbrakk> x \<noteq> y \<rbrakk> \<Longrightarrow> add_env (rem_env env x) y t = rem_env (add_env env y t) x"
  apply (case_tac "\<forall> x'. add_env (rem_env env x) y t x' = rem_env (add_env env y t) x x'")
   apply (auto)
  apply (simp add: add_env_def)
  apply (simp add: rem_env_def)
  apply (case_tac "y = x'")
   apply (auto)
  apply (simp add: rem_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done  
  

lemma double_rem_env: "rem_env (rem_env env x) x = rem_env env x"  
  apply (case_tac "\<forall> y. rem_env (rem_env env x) x y = rem_env env x y")
   apply (auto)
  apply (simp add: rem_env_def)
  apply (auto)
  done
    
lemma almost_comm_rem_env: "\<lbrakk> x \<noteq> y \<rbrakk> \<Longrightarrow> rem_env (rem_env env x) y = rem_env (rem_env env y) x"   
  apply (case_tac "\<forall> z. rem_env (rem_env env x) y z = rem_env (rem_env env y) x z")
   apply (auto)
  apply (simp add: rem_env_def)
  apply (auto)
  done
    
end