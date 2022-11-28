theory ProcHoleVars
  imports RedSafeHoleLemma
begin

fun hole_free_vars :: "p_hole \<Rightarrow> string set" where
  "hole_free_vars ExpHole = {}"
| "hole_free_vars (AppHole1 h e) = (hole_free_vars h \<union> free_vars e)"    
| "hole_free_vars (AppHole2 v h) = (free_vars v \<union> hole_free_vars h)"    
| "hole_free_vars (IfHole h e1 e2) = (hole_free_vars h \<union> free_vars e1 \<union> free_vars e2)"
| "hole_free_vars (PairHole1 h e) = (hole_free_vars h \<union> free_vars e)"  
| "hole_free_vars (PairHole2 e h) = (free_vars e \<union> hole_free_vars h)"  
(*| "hole_free_vars (UnpackHole e h) = (free_vars e \<union> hole_free_vars h)"    *)

fun hole_res_vars :: "owner_env \<Rightarrow> p_hole \<Rightarrow> res_id set" where
  "hole_res_vars delta ExpHole = {}"
| "hole_res_vars delta (AppHole1 h e) = (hole_res_vars delta h \<union> res_vars delta e)"    
| "hole_res_vars delta (AppHole2 v h) = (res_vars delta v \<union> hole_res_vars delta h)"    
| "hole_res_vars delta (IfHole h e1 e2) = (hole_res_vars delta h \<union> res_vars delta e1 \<union> res_vars delta e2)"
| "hole_res_vars delta (PairHole1 h e) = (hole_res_vars delta h \<union> res_vars delta e)"  
| "hole_res_vars delta (PairHole2 e h) = (res_vars delta e \<union> hole_res_vars delta h)"    
  
lemma app_hole_free_vars: "\<lbrakk> x \<in> free_vars e \<rbrakk> \<Longrightarrow> x \<in> free_vars (app_hole h e)"    
  apply (induct h)
    apply (auto)
  done  
    
lemma app_hole_free_vars2: "\<lbrakk> x \<in> hole_free_vars h \<rbrakk> \<Longrightarrow> x \<in> free_vars (app_hole h e)"    
  apply (induct h)
    apply (auto)
  done    
    
lemma app_hole_free_vars_rev: "\<lbrakk> x \<in> free_vars (app_hole h e) \<rbrakk> \<Longrightarrow> x \<in> hole_free_vars h \<or> x \<in> free_vars e"    
  apply (induct h)
    apply (auto)
  done 

lemma app_hole_res_vars: "\<lbrakk> x \<in> res_vars delta e \<rbrakk> \<Longrightarrow> x \<in> res_vars delta (app_hole h e)"    
  apply (induct h)
    apply (auto)
  done  
    
lemma app_hole_res_vars2: "\<lbrakk> x \<in> hole_res_vars delta h \<rbrakk> \<Longrightarrow> x \<in> res_vars delta (app_hole h e)"    
  apply (induct h)
    apply (auto)
  done    
    
lemma app_hole_res_vars_rev: "\<lbrakk> x \<in> res_vars delta (app_hole h e) \<rbrakk> \<Longrightarrow> x \<in> hole_res_vars delta h \<or> x \<in> res_vars delta e"    
  apply (induct h)
    apply (auto)
  done 
    
    (* ##### states that if x is a non-prim var in 'e', it will not be a free var in 'h' if 'h (fork e)' is well-typed.  ##### *)
  
fun strong_fun_ty where
  "strong_fun_ty (FunTy t1 t2 r a) = (r = OwnPerm)"
| "strong_fun_ty tau = False"
  
fun strong_fun_ty2 where
  "strong_fun_ty2 (FunTy t1 (FunTy t2 t3 r a) rx ax) = (r = OwnPerm)"  
| "strong_fun_ty2 tau = False"  
  
fun strong_fun where
  "strong_fun (ConstExp c) = (\<forall> tau. tau \<in> const_type c \<longrightarrow> strong_fun_ty tau)"
| "strong_fun (AppExp (ConstExp c) v) = (\<forall> tau. tau \<in> const_type c \<longrightarrow> strong_fun_ty2 tau)"  
| "strong_fun e = False"    
  
lemma strong_fun_own: "\<lbrakk>  well_typed env delta r_s1 f (FunTy t1 t2 r a) r_s2 rx; strong_fun f \<rbrakk> \<Longrightarrow> is_own r"  
  apply (case_tac f)
        apply (auto)
   apply (simp add: is_own_def)
   apply (auto)
  apply (simp add: is_own_def)
  apply (case_tac x71)
        apply (auto)
  done
  
lemma safe_hole_npv_use_ih: "\<lbrakk> well_typed env delta r_s1 (app_hole h (AppExp f e)) tau r_s2 rx; well_formed_delta env delta;
  is_value f; strong_fun f; is_value e; x \<in> non_prim_vars env delta e \<rbrakk> \<Longrightarrow> r_s2 x = NoPerm"
  apply (induct h arbitrary: env r_s1 r_s2 tau rx)
       apply (auto)
    (* base case. x is subtracted out in the lifting of the inflected rx2 *)
       apply (cut_tac env="env" and ?r_s1.0="r_s2a" and e="e" and tau="t1" and ?r_s2.0="r_s3" and rx="rx2" in infl_sexp_wp)
         apply (auto)
        apply (rule_tac value_is_sexp)
        apply (simp)
    (* - r_s3 x has a value since otherwise it would be trivial *)
       apply (case_tac "r_s3 x = NoPerm")
        apply (rule_tac r_s="r_s3" in leq_use_none)
         apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
          apply (rule_tac self_diff_leq_use_env)
         apply (auto)
    (* - we know that rx2 has a value, because otherwise rx2 + [r_s2a - r_s3] would not have a value, altho it is the start perms of e *)
       apply (case_tac "rx2 x = NoPerm")
        apply (cut_tac r_sa="rx2" and r_sb="infl_use_env r_s2a r_s3" and x="x" in comp_use_none)
          apply (simp)
         apply (simp add: infl_use_env_def)
        apply (cut_tac env="env" and ?r_s1.0="comp_use_env rx2 (infl_use_env r_s2a r_s3)" and x="x" in well_typed_no_npv_use)
          apply (auto)
    (* - by construction of strong functions, we also know that r = OwnPerm *)
       apply (cut_tac f="f" and r="r" in strong_fun_own)
         apply (auto)
    (* - from here we can deduce EX x = Own *)
        apply (rule_tac r_s="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in leq_use_none)
         apply (auto)
        apply (rule_tac diff_use_none_ex)
        apply (rule_tac r_x="lift_use_env rx2 r" in leq_use_own)
         apply (simp add: is_own_def)
        apply (rule_tac comp_leq_use_env1)
        apply (rule_tac self_comp_leq_use_env2)
    (* lhs induct. *)
      apply (rule_tac r_s="r_s2a" in leq_use_none)
       apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
        apply (rule_tac diff_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
    (* rhs induct. *)
     apply (rule_tac r_s="r_s3" in leq_use_none)
      apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
       apply (rule_tac self_diff_leq_use_env)
      apply (auto)
    (* if case. *)
    apply (rule_tac r_s="r_s2a" in leq_use_none)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    (* pair case 1. *)
   apply (rule_tac r_s="r_s2a" in leq_use_none)
    apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
     apply (rule_tac diff_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    (* pair case 2. *)
  apply (rule_tac r_s="r_s3" in leq_use_none)
   apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
    apply (rule_tac self_diff_leq_use_env)
   apply (auto)
  done        
    
lemma safe_hole_npv_use_st: "\<lbrakk> well_typed env delta r_s1 (app_hole h (AppExp f e)) tau r_s2 rx; well_formed_delta env delta; is_value f; strong_fun f;
 wf_hole h; is_value e \<rbrakk> \<Longrightarrow> x \<notin> non_prim_vars env delta e \<or> x \<notin> hole_res_vars delta h"
  apply (induct h arbitrary: env r_s1 tau r_s2 rx)
       apply (auto)
    (* lhs induct. since r_s2a x = None, it cannot be in e2 *)
       apply (cut_tac h="h" and e="e" and ?r_s2.0="r_s2a" and x="x" in safe_hole_npv_use_ih)
            apply (auto)
       apply (cut_tac ?r_s1.0="r_s2a" and e="x2" and x="x" in well_typed_no_npv_use)
         apply (auto)
       apply (simp add: non_prim_vars_def)
    (* rhs induct. r_s2a x has a value. since x is in e2. *)
      apply (case_tac "r_s2a x = NoPerm")
       apply (cut_tac ?r_s1.0="r_s2a" and x="x" and e="app_hole h (AppExp f e)" in well_typed_no_npv_use)
         apply (auto)
       apply (cut_tac h="h" and e="AppExp f e" and x="x" and delta="delta" in app_hole_res_vars)
        apply (simp add: non_prim_vars_def)
       apply (simp add: non_prim_vars_def)
    (* - by lemma, rx1 x has a value as well. *)
      apply (cut_tac env="env" and e="x1" and tau="FunTy t1 tau r a" and ?r_s2.0="r_s2a" and rx="rx1" in wt_sexp_req_use)
          apply (auto)
        apply (rule_tac value_is_sexp)
        apply (auto)
       apply (simp add: non_prim_vars_def)
    (* - this is a contradiction, since r_s3 x = None, and rx1 is contained by it *)
      apply (cut_tac r_x="rx1" and r_s="r_s3" and x="x" in leq_use_none)
        apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
         apply (simp)
        apply (rule_tac self_comp_leq_use_env1)
       apply (rule_tac safe_hole_npv_use_ih)
           apply (auto)
    (* lhs if case. since r_s2a x = None, it cannot be in e2 *)
     apply (cut_tac h="h" and e="e" and ?r_s2.0="r_s2a" and x="x" in safe_hole_npv_use_ih)
          apply (auto)
     apply (cut_tac ?r_s1.0="r_s2a" and e="x2" and x="x" in well_typed_no_npv_use)
       apply (auto)
     apply (simp add: non_prim_vars_def)
    (* rhs if case. since r_s2a x = None, it cannot be in e2 *)
    apply (cut_tac h="h" and e="e" and ?r_s2.0="r_s2a" and x="x" in safe_hole_npv_use_ih)
         apply (auto)
    apply (cut_tac ?r_s1.0="r_s2a" and e="x3" and x="x" in well_typed_no_npv_use)
      apply (auto)
    apply (simp add: non_prim_vars_def)
    (* lhs pair case. same for lhs induct *)
   apply (cut_tac h="h" and e="e" and ?r_s2.0="r_s2a" and x="x" in safe_hole_npv_use_ih)
        apply (auto)
   apply (cut_tac ?r_s1.0="r_s2a" and e="x2" and x="x" in well_typed_no_npv_use)
     apply (auto)
   apply (simp add: non_prim_vars_def)
    (* rhs pair case. same for rhs induct *)
    (* - r_s2a x has a value. since x is in e2 *)
  apply (case_tac "r_s2a x = NoPerm")
   apply (cut_tac ?r_s1.0="r_s2a" and x="x" and e="app_hole h (AppExp f e)" in well_typed_no_npv_use)
     apply (auto)
   apply (cut_tac h="h" and e="AppExp f e" and x="x" and delta="delta" in app_hole_res_vars)
    apply (auto)
    apply (simp add: non_prim_vars_def)
   apply (simp add: non_prim_vars_def)
    (* - then rx1 x has a value *)
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and e="x1" and tau="t1" and ?r_s2.0="r_s2a" and rx="rx1" in wt_sexp_req_use)
      apply (auto)
    apply (rule_tac value_is_sexp)
    apply (auto)
   apply (simp add: non_prim_vars_def)
    (* - this is a contradiction, since r_s3 x = None, and rx1 is contained by it *)
  apply (cut_tac r_x="rx1" and r_s="r_s3" and x="x" in leq_use_none)
    apply (rule_tac r_sb="lift_use_env rx1 r" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac self_lift_leq_use_env)
   apply (rule_tac safe_hole_npv_use_ih)
       apply (auto)
  done    
    
lemma safe_fork_hole_npv_use: "\<lbrakk> well_typed env delta r_s1 (app_hole h (AppExp (ConstExp ForkConst) e)) tau r_s2 rx; well_formed_delta env delta;
 wf_hole h; is_value e; x \<in> non_prim_vars env delta e \<rbrakk> \<Longrightarrow> x \<notin> hole_res_vars delta h"
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and h="h" and e="e" and f="ConstExp ForkConst" and x="x" in safe_hole_npv_use_st)
       apply (auto)
  apply (simp add: is_own_def)
  done        
   
lemma safe_send_hole_npv_use: "\<lbrakk> well_typed env delta r_s1 (app_hole h (AppExp (AppExp (ConstExp SendConst) v) e)) tau r_s2 rx;
  well_formed_delta env delta; wf_hole h; is_value v; is_value e; x \<in> non_prim_vars env delta e \<rbrakk> \<Longrightarrow> x \<notin> hole_res_vars delta h"
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and h="h" and e="e" and f="AppExp (ConstExp SendConst) v" and x="x" and delta="delta" in safe_hole_npv_use_st)
       apply (auto)
  apply (simp add: pure_fun_def)
  apply (simp add: is_own_def)
  done     
    
end