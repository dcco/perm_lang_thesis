theory WTMiscEnv
  imports TypeEnv LiftEnv
begin
  
fun fun_ty where
  "fun_ty (FunTy t1 t2 r a) = True"
| "fun_ty tau = False"      
  
fun max_aff where
  "max_aff Aff a = Aff"
| "max_aff a Aff = Aff"
| "max_aff Prim Prim = Prim"
| "max_aff a1 a2 = Ref"  
  
fun as_aff where
  "as_aff OwnPerm = Aff"  
| "as_aff UsePerm = Ref"  
| "as_aff NoPerm = Prim"  
  
fun req_type where
  "req_type (FunTy t1 t2 r a) = a"
| "req_type (ArrayTy tau) = Ref"
| "req_type (PairTy t1 t2 r) = as_aff r(*(if r = OwnPerm then Aff else max_aff (req_type t1) (req_type t2))*)"
  (*if req_type t1 = Aff \<or> req_type t2 = Aff then Aff else Ref*)
| "req_type (ChanTy tau c) = Ref"  
| "req_type tau = Prim"
  
definition unlim where
  "unlim tau = (req_type tau \<noteq> Aff)"  
  
definition non_prim_entry where
  "non_prim_entry env x = (\<exists> tau. env x = Some tau \<and> req_type tau \<noteq> Prim)"  
  
  
definition np_use_env where
  "np_use_env env r_s = (\<lambda> x. if non_prim_entry env x then r_s x else NoPerm)"  
  
definition null_use_env where
  "null_use_env r_s = (\<forall> x. r_s x = NoPerm)"  
  
definition aff_use_env where
  "aff_use_env r_s a = (case a of
    Aff \<Rightarrow> True
    | Ref \<Rightarrow> weak_use_env r_s
    | Prim \<Rightarrow> null_use_env r_s
  )" 
  
definition start_req_perm where
  "start_req_perm tau = (case req_type tau of
    Aff \<Rightarrow> OwnPerm
  | other \<Rightarrow> UsePerm)"

definition end_req_perm where
  "end_req_perm tau = (case req_type tau of
    Aff \<Rightarrow> OwnPerm
  | Ref \<Rightarrow> UsePerm
  | other \<Rightarrow> NoPerm)"
  
definition req_use_env where
  "req_use_env x tau = one_use_env x (start_req_perm tau)"    

definition ereq_use_env where
  "ereq_use_env x tau = one_use_env x (end_req_perm tau)"    

  
    (* 
      ####################################
        P1. specialized perm-env lemmas
      ####################################
    *)  

    (* - basic perm lemmas *)
  
lemma req_use_none: "req_use_env x tau x \<noteq> NoPerm"
  apply (simp add: req_use_env_def)
  apply (simp add: start_req_perm_def)
  apply (simp add: one_use_env_def)
  apply (case_tac "req_type tau")
    apply (auto)
  done      
  
lemma req_use_none_alt: "\<lbrakk> x \<noteq> y \<rbrakk> \<Longrightarrow> req_use_env x tau y = NoPerm"    
  apply (simp add: req_use_env_def)
  apply (simp add: one_use_env_def)
  done    

lemma ereq_use_none: "\<lbrakk> req_type tau \<noteq> Prim \<rbrakk> \<Longrightarrow> ereq_use_env x tau x \<noteq> NoPerm"
  apply (simp add: ereq_use_env_def)
  apply (simp add: end_req_perm_def)
  apply (simp add: one_use_env_def)
  apply (case_tac "req_type tau")
    apply (auto)
  done
 
lemma ereq_use_none_alt: "\<lbrakk> x \<noteq> y \<rbrakk> \<Longrightarrow> ereq_use_env x tau y = NoPerm"
  apply (simp add: ereq_use_env_def)
  apply (simp add: one_use_env_def)
  done    
    
    (* - affinity lemmas *)
    
lemma max_aff_prim: "\<lbrakk> max_aff a1 a2 = Prim \<rbrakk> \<Longrightarrow> a1 = Prim \<and> a2 = Prim"    
  apply (case_tac a1)
    apply (auto)
   apply (case_tac a2)
     apply (auto)
  apply (case_tac a2)
    apply (auto)
  done    
    
    (* - ordering lemmas *)
  
lemma req_leq_use_env: "\<lbrakk> leq_use_env (req_use_env x tau) r_s; r_s x = r_x x \<rbrakk> \<Longrightarrow> leq_use_env (req_use_env x tau) r_x"
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (simp add: req_use_env_def)
  apply (simp add: one_use_env_def)
  apply (case_tac "x = xa")
   apply (auto)
  done
    
lemma req_leq_use_envx: "\<lbrakk> leq_perm (start_req_perm tau) (r_s x) \<rbrakk> \<Longrightarrow> leq_use_env (req_use_env x tau) r_s"  
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (simp add: req_use_env_def)
  apply (simp add: one_use_env_def)
  apply (auto)
  done      
    
    (* - disjointness lemmas *)
    
lemma disj_req_use_env1: "\<lbrakk> r_s x = NoPerm \<rbrakk> \<Longrightarrow> disj_use_env (req_use_env x tau) r_s"
  apply (simp add: req_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  done    
    
lemma disj_req_use_env2: "\<lbrakk> r_s x = NoPerm \<rbrakk> \<Longrightarrow> disj_use_env r_s (req_use_env x tau)"
  apply (simp add: req_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  done    
    
    (* - affine env lemmas *)
 
lemma leq_null_use_env: "\<lbrakk> null_use_env r_s; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> null_use_env r_x"    
  apply (simp add: null_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  done
  
lemma dist_np_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (np_use_env env r_x) (np_use_env env r_s)"
  apply (simp add: leq_use_env_def)
  apply (simp add: np_use_env_def)
  done
    
lemma aff_leq_use_env: "\<lbrakk> aff_use_env r_s a; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> aff_use_env r_x a"    
  apply (simp add: aff_use_env_def)
  apply (case_tac a)
    apply (auto)
   apply (rule_tac r_s="r_s" in leq_weak_use_env)
    apply (simp_all)
  apply (rule_tac r_s="r_s" in leq_null_use_env)
   apply (simp_all)
  done
  
lemma aff_diff_use_env: "\<lbrakk> aff_use_env r_s a \<rbrakk> \<Longrightarrow> aff_use_env (diff_use_env r_s r_x) a"
  apply (rule_tac r_s="r_s" in aff_leq_use_env)
   apply (auto)
  apply (rule_tac self_diff_leq_use_env)
  done    

lemma aff_rem_use_env: "\<lbrakk> aff_use_env r_s a \<rbrakk> \<Longrightarrow> aff_use_env (rem_use_env r_s x) a"
  apply (rule_tac r_s="r_s" in aff_leq_use_env)
   apply (auto)
  apply (rule_tac self_rem_leq_use_env)
  done   

lemma aff_comp_use_env: "\<lbrakk> aff_use_env r_x a; aff_use_env r_s a \<rbrakk> \<Longrightarrow> aff_use_env (comp_use_env r_x r_s) a"
  apply (simp add: aff_use_env_def)
  apply (case_tac a)
    apply (auto)
   apply (simp add: comp_use_env_def)
   apply (simp add: weak_use_env_def)
   apply (auto)
   apply (erule_tac x="x" in allE)
   apply (erule_tac x="x" in allE)
   apply (case_tac "r_x x")
     apply (auto)
    apply (case_tac "r_s x")
      apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: null_use_env_def)
  done

lemma aff_empty_use_env: "aff_use_env empty_use_env a"
  apply (simp add: aff_use_env_def)
  apply (case_tac a)
    apply (auto)
   apply (simp add: weak_use_env_def)
   apply (auto)
   apply (simp add: empty_use_env_def)
  apply (simp add: null_use_env_def)
  apply (auto)
  apply (simp add: empty_use_env_def)
  done
    
(*
lemma aff_comp_use_env: "\<lbrakk> aff_use_env r_x a; aff_use_env r_s a \<rbrakk> \<Longrightarrow> aff_use_env (comp_use_env r_x r_s) a"
  apply (simp add: comp_use_env_def)
  apply (simp add: aff_use_env_def)
  apply (case_tac a)
   apply (auto)
  apply (simp add: weak_use_env_def)
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

lemma aff_empty_use_env: "aff_use_env empty_use_env a"
  apply (simp add: aff_use_env_def)
  apply (auto)
  apply (simp add: weak_use_env_def)
  apply (simp add: empty_use_env_def)
  done    *)
 
    (* ################# UNSORTED *)

lemma weak_ereq_use_env: "\<lbrakk> unlim tau \<rbrakk> \<Longrightarrow> weak_use_env (ereq_use_env x tau)"    
  apply (simp add: weak_use_env_def)
  apply (simp add: ereq_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: end_req_perm_def)
  apply (case_tac "req_type tau")
    apply (auto)
  apply (simp add: unlim_def)
  done     
    
(*  
lemma weak_req_use_env: "\<lbrakk> unlim tau \<rbrakk> \<Longrightarrow> weak_use_env (req_use_env x tau)"    
  apply (simp add: weak_use_env_def)
  apply (simp add: req_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: start_req_perm_def)
  apply (simp add: aff_fun_ty_def)
  done    *)

lemma self_ereq_leq_use_env: "leq_use_env (ereq_use_env x tau) (req_use_env x tau)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: ereq_use_env_def)
  apply (simp add: req_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: end_req_perm_def)
  apply (simp add: start_req_perm_def)
  apply (case_tac "req_type tau")
    apply (auto)
  done
    
lemma ereq_leq_use_env: "\<lbrakk> leq_use_env (req_use_env x tau) r_s \<rbrakk> \<Longrightarrow> leq_use_env (ereq_use_env x tau) r_s"    
  apply (rule_tac r_sb="req_use_env x tau" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac self_ereq_leq_use_env)
  done
    
lemma ereq_leq_use_envx: "\<lbrakk> leq_perm (end_req_perm tau) (r_s x) \<rbrakk> \<Longrightarrow> leq_use_env (ereq_use_env x tau) r_s"    
  apply (simp add: leq_use_env_def)
  apply (simp add: ereq_use_env_def)
  apply (simp add: one_use_env_def)
  done
    
lemma one_mini_disj_use_env1: "\<lbrakk> r_x x \<noteq> OwnPerm \<or> r = NoPerm \<or> r_ex x = OwnPerm \<rbrakk> \<Longrightarrow> mini_disj_use_env r_x (diff_use_env (one_use_env x r) r_ex)"    
  apply (simp add: diff_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
     apply (case_tac "r_ex xa")
       apply (auto)
    apply (case_tac "r_ex x")
      apply (auto)
   apply (case_tac "r_ex xa")
     apply (auto)
  apply (case_tac "r_ex xa")
    apply (auto)
  done

lemma one_mini_disj_use_env2: "\<lbrakk> r \<noteq> OwnPerm \<or> r_ex x = OwnPerm \<or> r_x x = NoPerm \<rbrakk> \<Longrightarrow> mini_disj_use_env (diff_use_env (one_use_env x r) r_ex) r_x"     
apply (simp add: diff_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
     apply (case_tac "r_ex x")
       apply (auto)
    apply (case_tac "r_ex xa")
      apply (auto)
   apply (case_tac "r_ex xa")
     apply (auto)
  apply (case_tac "r_ex xa")
    apply (auto)
  done
  
lemma diff_one_leq_use_env: "leq_use_env (diff_use_env (one_use_env x r) (one_use_env x OwnPerm)) r_s"    
  apply (simp add: diff_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (simp add: one_use_env_def)
  done      
    
end