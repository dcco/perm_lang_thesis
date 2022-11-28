theory InferVar
  imports WTLemma
begin
  
    (* ##### TO MOVE *)
  
lemma add_rem_use_env: "add_use_env (rem_use_env r_s x) x (r_s x) = r_s"    
  apply (case_tac "\<forall> x'. add_use_env (rem_use_env r_s x) x (r_s x) x' = r_s x'")  
   apply (auto)
  apply (simp add: add_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  apply (simp add: rem_use_env_def)
  done  
  
lemma max_aff_leq: "\<lbrakk> aff_leq a1 ax; aff_leq a2 ax \<rbrakk> \<Longrightarrow> aff_leq (max_aff a1 a2) ax"    
  apply (case_tac a1)
    apply (auto)
   apply (case_tac a2)
     apply (auto)
  apply (case_tac a2)
    apply (auto)
  done  
  
    (* ##### extended environment definitions *)
    (* schema types *)
  
type_synonym p_var = nat
type_synonym t_var = nat

datatype s_perm = SPerm p_perm | SVar p_var
  
datatype s_aff = AffConst p_aff | AffVar p_var

datatype x_perm = XPerm s_perm | XType nat | XComp x_perm x_perm | XLift x_perm s_perm | XIfZero x_perm x_perm
  
datatype s_type =
   IntScheme | UnitScheme | BoolScheme
  | VarScheme t_var
  | ArrayScheme s_type  
  | PairScheme s_type s_type s_perm
  | FunScheme s_type s_type s_perm s_aff
  | ChanScheme s_type c_end

definition pure_fun_s where
  "pure_fun_s t1 t2 a = FunScheme t1 t2 (SPerm UsePerm) a"
  
    (* schema perm envs *)

type_synonym perm_var_env = "res_id \<Rightarrow> x_perm"      
    
definition empty_var_env where
  "empty_var_env = (\<lambda> x. XPerm (SPerm NoPerm))"  
  
definition one_var_env where
  "one_var_env x q = (\<lambda> x'. if x' = x then q else XPerm (SPerm NoPerm))" 
  
definition add_var_env where
  "add_var_env r_s x q = (\<lambda> x'. if x' = x then q else r_s x)"
  
definition rem_var_env where
  "rem_var_env r_s x = (\<lambda> x'. if x' = x then XPerm (SPerm NoPerm) else r_s x')"  
  
definition comp_var_env where
  "comp_var_env r_s r_x = (\<lambda> x. if r_s x = XPerm (SPerm NoPerm) \<and> r_x x = XPerm (SPerm NoPerm) then XPerm (SPerm NoPerm) else XComp (r_s x) (r_x x))"

definition lift_var_env where
  "lift_var_env r_s r = (\<lambda> x. if r_s x = XPerm (SPerm NoPerm) then r_s x else XLift (r_s x) r)"
  
definition ifz_var_env where
  "ifz_var_env r r_s = (\<lambda> x. if r_s x = XPerm (SPerm NoPerm) then XPerm (SPerm NoPerm) else XIfZero r (r_s x))"

    (* solution substitution *)
  
type_synonym 'a subst_env = "('a, nat) gen_env"  
  
type_synonym type_subst = "s_type subst_env"
type_synonym dir_type_subst = "p_type subst_env"  
  
type_synonym perm_subst = "nat \<Rightarrow> p_perm"  

fun sol_subst_aff where
  "sol_subst_aff p_sub (AffConst a) = a"
| "sol_subst_aff p_sub (AffVar x) = as_aff (p_sub x)"  
  
fun sol_subst_perm :: "perm_subst \<Rightarrow> s_perm \<Rightarrow> p_perm" where
  "sol_subst_perm p_sub (SPerm p) = p"  
| "sol_subst_perm p_sub (SVar x) = p_sub x"
  
fun dir_subst_permx :: "dir_type_subst \<Rightarrow> perm_subst \<Rightarrow> x_perm \<Rightarrow> p_perm" where
  "dir_subst_permx t_sub p_sub (XPerm p) = (sol_subst_perm p_sub p)"
| "dir_subst_permx t_sub p_sub (XType a) = (case t_sub a of
    None \<Rightarrow> NoPerm
    | Some tau \<Rightarrow> as_perm (req_type tau))"
| "dir_subst_permx t_sub p_sub (XComp p1 p2) = union_perm (dir_subst_permx t_sub p_sub p1) (dir_subst_permx t_sub p_sub p2)"
| "dir_subst_permx t_sub p_sub (XLift p q) = (if sol_subst_perm p_sub q = OwnPerm \<and>
  dir_subst_permx t_sub p_sub p \<noteq> NoPerm then OwnPerm else dir_subst_permx t_sub p_sub p)"
| "dir_subst_permx t_sub p_sub (XIfZero p q) = (if dir_subst_permx t_sub p_sub p = NoPerm then NoPerm else dir_subst_permx t_sub p_sub q)"  

definition dir_subst_penv :: "dir_type_subst \<Rightarrow> perm_subst \<Rightarrow> perm_var_env \<Rightarrow> perm_use_env" where
  "dir_subst_penv t_sub p_sub r_s = (\<lambda> x. dir_subst_permx t_sub p_sub (r_s x))"    
  
fun dir_subst_type :: "dir_type_subst \<Rightarrow> perm_subst \<Rightarrow> s_type \<Rightarrow> p_type \<Rightarrow> bool" where
  "dir_subst_type t_sub p_sub IntScheme tau' = (tau' = IntTy)"  
| "dir_subst_type t_sub p_sub UnitScheme tau' = (tau' = UnitTy)"
| "dir_subst_type t_sub p_sub BoolScheme tau' = (tau' = BoolTy)"
| "dir_subst_type t_sub p_sub (VarScheme a) tau' = (t_sub a = Some tau')"
| "dir_subst_type t_sub p_sub (ArrayScheme tau) tau' = (\<exists> tau_x.
  dir_subst_type t_sub p_sub tau tau_x \<and> tau' = ArrayTy tau_x)"
| "dir_subst_type t_sub p_sub (PairScheme t1 t2 p) tau' = (\<exists> t1_x t2_x.
  dir_subst_type t_sub p_sub t1 t1_x \<and> dir_subst_type t_sub p_sub t2 t2_x \<and>
  tau' = PairTy t1_x t2_x (sol_subst_perm p_sub p))"
| "dir_subst_type t_sub p_sub (FunScheme t1 t2 p q) tau' = (\<exists> t1_x t2_x.
  dir_subst_type t_sub p_sub t1 t1_x \<and> dir_subst_type t_sub p_sub t2 t2_x \<and>
  tau' = FunTy t1_x t2_x (sol_subst_perm p_sub p) (sol_subst_aff p_sub q))"
| "dir_subst_type t_sub p_sub (ChanScheme tau c_end) tau' = (\<exists> tau_x.
  dir_subst_type t_sub p_sub tau tau_x \<and> tau' = ChanTy tau_x c_end)"   
  
definition dir_subst_tenv :: "dir_type_subst \<Rightarrow> nat res_env => pt_env" where
  "dir_subst_tenv t_sub env_v = (\<lambda> x. case env_v x of
    None \<Rightarrow> None
    | Some a \<Rightarrow> t_sub a)"
  
fun full_subst_type_f :: "dir_type_subst \<Rightarrow> perm_subst \<Rightarrow> p_type \<Rightarrow> s_type \<Rightarrow> p_type" where
  "full_subst_type_f t_sub p_sub tau_n IntScheme = IntTy"
| "full_subst_type_f t_sub p_sub tau_n UnitScheme = UnitTy"  
| "full_subst_type_f t_sub p_sub tau_n BoolScheme = BoolTy"
| "full_subst_type_f t_sub p_sub tau_n (VarScheme x) = (case t_sub x of
    None \<Rightarrow> tau_n
    | Some tau \<Rightarrow> tau
  )"
| "full_subst_type_f t_sub p_sub tau_n (ArrayScheme tau) = ArrayTy (full_subst_type_f t_sub p_sub tau_n tau)"  
| "full_subst_type_f t_sub p_sub tau_n (PairScheme t1 t2 p) =
    PairTy (full_subst_type_f t_sub p_sub tau_n t1) (full_subst_type_f t_sub p_sub tau_n t2) (sol_subst_perm p_sub p)"
| "full_subst_type_f t_sub p_sub tau_n (FunScheme t1 t2 p q) = FunTy (full_subst_type_f t_sub p_sub tau_n t1)
  (full_subst_type_f t_sub p_sub tau_n t2) (sol_subst_perm p_sub p) (sol_subst_aff p_sub q)"  
| "full_subst_type_f t_sub p_sub tau_n (ChanScheme tau c_end) = ChanTy (full_subst_type_f t_sub p_sub tau_n tau) c_end"  
  
definition full_subst_type where
  "full_subst_type t_sub p_sub tau_n tau_v = full_subst_type_f t_sub p_sub tau_n tau_v"  
  
definition fill_tsub :: "dir_type_subst \<Rightarrow> p_type \<Rightarrow> dir_type_subst" where  
  "fill_tsub t_sub tau_n = (\<lambda> x. case t_sub x of None \<Rightarrow> Some tau_n | Some tau \<Rightarrow> Some tau)"
  
    (* ##### lemmas *)
  
lemma subst_empty_var_env: "dir_subst_penv t_sub p_sub empty_var_env = empty_use_env"  
  apply (case_tac "\<forall> x. dir_subst_penv t_sub p_sub empty_var_env x = empty_use_env x")
   apply (auto)
  apply (simp add: empty_var_env_def)
  apply (simp add: empty_use_env_def)
  apply (simp add: dir_subst_penv_def)
  done
  
    
lemma end_req_aff_leq_perm: "\<lbrakk> aff_leq (req_type tau) (sol_subst_perm p_sub (SVar p)) \<rbrakk> \<Longrightarrow>
  leq_perm (end_req_perm tau) (dir_subst_permx t_sub p_sub (one_var_env x (XPerm (SVar p)) x))"    
  apply (simp add: one_var_env_def)
  apply (simp add: end_req_perm_def)
  apply (case_tac "req_type tau")
    apply (auto)
   apply (case_tac "sol_subst_perm p_sub (SVar p)")
     apply (auto)
  apply (case_tac "sol_subst_perm p_sub (SVar p)")
    apply (auto)
  done
    
lemma lift_sol_subst_penv: "lift_use_env (dir_subst_penv t_sub p_sub r_s) (sol_subst_perm p_sub r) = dir_subst_penv t_sub p_sub (lift_var_env r_s r)"     
  apply (case_tac "\<forall> x. lift_use_env (dir_subst_penv t_sub p_sub r_s) (sol_subst_perm p_sub r) x = dir_subst_penv t_sub p_sub (lift_var_env r_s r) x")
  apply (auto)
  apply (simp add: dir_subst_penv_def)
  apply (simp add: lift_var_env_def)
  apply (case_tac "sol_subst_perm p_sub r")
    apply (auto)
  done
 
lemma lift_sol_subst_penvx: "lift_use_env (dir_subst_penv t_sub p_sub r_s) (p_sub r) = dir_subst_penv t_sub p_sub (lift_var_env r_s (SVar r))"     
  apply (case_tac "\<forall> x. lift_use_env (dir_subst_penv t_sub p_sub r_s) (p_sub r) x = dir_subst_penv t_sub p_sub (lift_var_env r_s (SVar r)) x")
  apply (auto)
  apply (simp add: dir_subst_penv_def)
  apply (simp add: lift_var_env_def)
  apply (case_tac "p_sub r")
    apply (auto)
  done    
    
lemma comp_sol_subst_penv: "dir_subst_penv t_sub p_sub (comp_var_env r_s r_x) = comp_use_env (dir_subst_penv t_sub p_sub r_s) (dir_subst_penv t_sub p_sub r_x)"    
  apply (case_tac "\<forall> x. dir_subst_penv t_sub p_sub (comp_var_env r_s r_x) x = comp_use_env (dir_subst_penv t_sub p_sub r_s) (dir_subst_penv t_sub p_sub r_x) x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: comp_var_env_def)
  apply (simp add: dir_subst_penv_def)
  apply (case_tac "r_s x = XPerm (SPerm NoPerm) \<and> r_x x = XPerm (SPerm NoPerm)")
   apply (auto)
  done
    
lemma dist_comp_leq_var_env: "\<lbrakk> leq_use_env (dir_subst_penv t_sub p_sub r_x1) r_s;
  leq_use_env (dir_subst_penv t_sub p_sub r_x2) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (dir_subst_penv t_sub p_sub (comp_var_env r_x1 r_x2)) r_s"
  apply (simp add: comp_sol_subst_penv)
  apply (rule_tac dist_comp_leq_use_env)
   apply (simp_all)
  done

lemma comp_leq_var_env1: "\<lbrakk> leq_use_env r_x (dir_subst_penv t_sub p_sub r_s1) \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (dir_subst_penv t_sub p_sub (comp_var_env r_s1 r_s2))"    
  apply (simp add: comp_sol_subst_penv)
  apply (rule_tac comp_leq_use_env1)
  apply (simp)
  done
    
lemma comp_leq_var_env2: "\<lbrakk> leq_use_env r_x (dir_subst_penv t_sub p_sub r_s2) \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (dir_subst_penv t_sub p_sub (comp_var_env r_s1 r_s2))"    
  apply (simp add: comp_sol_subst_penv)
  apply (rule_tac comp_leq_use_env2)
  apply (simp)
  done

lemma lift_leq_var_env: "\<lbrakk> leq_use_env (dir_subst_penv t_sub p_sub r_x) (dir_subst_penv t_sub p_sub r_s) \<rbrakk> \<Longrightarrow>
  leq_use_env (dir_subst_penv t_sub p_sub r_x) (dir_subst_penv t_sub p_sub (lift_var_env r_s r))"        
  apply (rule_tac t="dir_subst_penv t_sub p_sub (lift_var_env r_s r)" and s="lift_use_env (dir_subst_penv t_sub p_sub r_s) (sol_subst_perm p_sub r)" in subst)
   apply (rule_tac lift_sol_subst_penv)
  apply (rule_tac lift_leq_use_env)
  apply (simp)
  done
 
lemma dist_lift_leq_var_env: "\<lbrakk> leq_use_env (dir_subst_penv t_sub p_sub r_x) (dir_subst_penv t_sub p_sub r_s) \<rbrakk> \<Longrightarrow>
  leq_use_env (dir_subst_penv t_sub p_sub (lift_var_env r_x r)) (dir_subst_penv t_sub p_sub (lift_var_env r_s r))"
  apply (rule_tac t="dir_subst_penv t_sub p_sub (lift_var_env r_s r)" and s="lift_use_env (dir_subst_penv t_sub p_sub r_s) (sol_subst_perm p_sub r)" in subst)
   apply (rule_tac lift_sol_subst_penv)
  apply (rule_tac t="dir_subst_penv t_sub p_sub (lift_var_env r_x r)" and s="lift_use_env (dir_subst_penv t_sub p_sub r_x) (sol_subst_perm p_sub r)" in subst)
   apply (rule_tac lift_sol_subst_penv)
  apply (rule_tac dist_lift_leq_use_env)
  apply (simp)
  done
  
lemma empty_leq_var_env: "leq_use_env (dir_subst_penv t_sub p_sub empty_var_env) r_s"    
  apply (simp add: dir_subst_penv_def)
  apply (simp add: empty_var_env_def)
  apply (simp add: leq_use_env_def)
  done

lemma if_zero_leq_var_env: "\<lbrakk> leq_use_env (dir_subst_penv t_sub p_sub r_x) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (dir_subst_penv t_sub p_sub (ifz_var_env q r_x)) r_s"
  apply (simp add: leq_use_env_def)
  apply (simp add: dir_subst_penv_def)
  apply (simp add: ifz_var_env_def)
  done   
    
lemma if_zero_pos_var_env: "\<lbrakk> dir_subst_permx t_sub p_sub r \<noteq> NoPerm \<rbrakk> \<Longrightarrow> dir_subst_penv t_sub p_sub (ifz_var_env r r_s) = dir_subst_penv t_sub p_sub r_s"    
  apply (case_tac "\<forall> x. dir_subst_penv t_sub p_sub (ifz_var_env r r_s) x = dir_subst_penv t_sub p_sub r_s x")
   apply (auto)
  apply (simp add: ifz_var_env_def)
  apply (simp add: dir_subst_penv_def)
  apply (auto)
  done
    
lemma rem_sol_subst_penv: "dir_subst_penv t_sub p_sub (rem_var_env r_s x) = rem_use_env (dir_subst_penv t_sub p_sub r_s) x"    
  apply (case_tac "\<forall> x'. dir_subst_penv t_sub p_sub (rem_var_env r_s x) x' = rem_use_env (dir_subst_penv t_sub p_sub r_s) x x'")  
   apply (auto)
  apply (simp add: dir_subst_penv_def)
  apply (simp add: rem_var_env_def)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done

    (* variable type environment lemmas *)    

lemma add_sol_subst_tenv: "add_env (dir_subst_tenv (fill_tsub t_sub tau_n) env) (Var x) (full_subst_type t_sub p_sub tau_n (VarScheme a)) =
  dir_subst_tenv (fill_tsub t_sub tau_n) (add_env env (Var x) a)"    
  apply (case_tac "\<forall> y. add_env (dir_subst_tenv (fill_tsub t_sub tau_n) env) (Var x) (full_subst_type t_sub p_sub tau_n (VarScheme a)) y =
  dir_subst_tenv (fill_tsub t_sub tau_n) (add_env env (Var x) a) y")
   apply (auto)
  apply (simp add: full_subst_type_def)
  apply (simp add: fill_tsub_def)
  apply (simp add: add_env_def)
  apply (simp add: dir_subst_tenv_def)
  apply (case_tac "Var x = y")
   apply (auto)
   apply (case_tac "t_sub a")
    apply (auto)
  apply (case_tac "env y")
   apply (auto)
   apply (simp add: dir_subst_tenv_def)
  apply (simp add: dir_subst_tenv_def)
  done        
    
end