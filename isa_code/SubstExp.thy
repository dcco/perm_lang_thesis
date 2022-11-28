theory SubstExp
  imports WellTypedExp
begin    
  
    (* 
      ####################################
        P2. variables in expressions
      ####################################
    *)  
  
fun lam_vars :: "p_exp \<Rightarrow> string set" where
  "lam_vars (ConstExp c) = {}"
| "lam_vars (OpExp xop) = {}"
| "lam_vars (VarExp v) = {}"
| "lam_vars (PairExp e1 e2) = lam_vars e1 \<union> lam_vars e2"
| "lam_vars (IfExp e1 e2 e3) = lam_vars e1 \<union> lam_vars e2 \<union> lam_vars e3"  
| "lam_vars (LamExp x e) = lam_vars e \<union> {x}"
| "lam_vars (AppExp e1 e2) = lam_vars e1 \<union> lam_vars e2"  
  
  (*
definition subst_name_match where  
  "subst_name_match x x' v = (x = x' \<and> v = NoRef)"
  *)
fun subst_exp :: "p_exp \<Rightarrow> string \<Rightarrow> p_exp \<Rightarrow> p_exp" where
  "subst_exp (ConstExp c) x e = ConstExp c"
| "subst_exp (OpExp xop) x e = OpExp xop"
| "subst_exp (VarExp (VarType x')) x e = (if x = x' then e else VarExp (VarType x'))"
| "subst_exp (VarExp v) x e = VarExp v"
| "subst_exp (PairExp e1 e2) x e = (PairExp (subst_exp e1 x e) (subst_exp e2 x e))"
| "subst_exp (IfExp e1 e2 e3) x e = (IfExp (subst_exp e1 x e) (subst_exp e2 x e) (subst_exp e3 x e))"
| "subst_exp (LamExp x' e') x e = (if x = x' then LamExp x' e' else LamExp x' (subst_exp e' x e))"
| "subst_exp (AppExp e1 e2) x e = (AppExp (subst_exp e1 x e) (subst_exp e2 x e))"
 
fun deep_alpha_rename :: "p_exp \<Rightarrow> string \<Rightarrow> string \<Rightarrow> p_exp" where
  "deep_alpha_rename (ConstExp c) x y = ConstExp c"
| "deep_alpha_rename (OpExp xop) x y = OpExp xop"
| "deep_alpha_rename (VarExp (VarType x')) x y = (if x = x' then VarExp (VarType y) else VarExp (VarType x'))"
| "deep_alpha_rename (VarExp v) x y = VarExp v"
| "deep_alpha_rename (PairExp e1 e2) x y = PairExp (deep_alpha_rename e1 x y) (deep_alpha_rename e2 x y)"
| "deep_alpha_rename (IfExp e1 e2 e3) x y =
  IfExp (deep_alpha_rename e1 x y) (deep_alpha_rename e2 x y) (deep_alpha_rename e3 x y)"
| "deep_alpha_rename (LamExp x' e) x y = (if x = x' then LamExp y (deep_alpha_rename e x y)
  else LamExp x' (deep_alpha_rename e x y))"
| "deep_alpha_rename (AppExp e1 e2) x y = AppExp (deep_alpha_rename e1 x y) (deep_alpha_rename e2 x y)"

fun lam_var_remove :: "p_exp \<Rightarrow> string \<Rightarrow> string \<Rightarrow> p_exp" where
  "lam_var_remove (ConstExp c) x y = ConstExp c"
| "lam_var_remove (OpExp xop) x y = OpExp xop"
| "lam_var_remove (VarExp v) x y = VarExp v"
| "lam_var_remove (PairExp e1 e2) x y = PairExp (lam_var_remove e1 x y) (lam_var_remove e2 x y)"
| "lam_var_remove (IfExp e1 e2 e3) x y = IfExp (lam_var_remove e1 x y) (lam_var_remove e2 x y) (lam_var_remove e3 x y)"
| "lam_var_remove (LamExp x' e) x y = (if x = x' then LamExp y (deep_alpha_rename e x y)
  else LamExp x' (lam_var_remove e x y))"
| "lam_var_remove (AppExp e1 e2) x y = AppExp (lam_var_remove e1 x y) (lam_var_remove e2 x y)"

fun pre_vars :: "('a * 'a) list \<Rightarrow> 'a set" where
  "pre_vars Nil = {}"
| "pre_vars ((x, y) # t) = {x} \<union> pre_vars t"  
 
fun post_vars :: "('a * 'a) list \<Rightarrow> 'a set" where
  "post_vars Nil = {}"
| "post_vars ((x, y) # t) = {y} \<union> post_vars t"
  
fun unique_post_vars :: "('a * 'a) list \<Rightarrow> bool" where
  "unique_post_vars Nil = True"
| "unique_post_vars ((x, y) # t) = (y \<notin> post_vars t \<and> unique_post_vars t)"
  
fun lam_var_list_remove :: "p_exp \<Rightarrow> (string * string) list \<Rightarrow> p_exp" where
  "lam_var_list_remove e Nil = e"
| "lam_var_list_remove e ((x, y) # t) = lam_var_list_remove (lam_var_remove e x y) t"

  
  (***** a valid substitution must rename all lambdas in e to avoid the free variables of e' ****)  
  
definition safe_subst_exp :: "p_exp \<Rightarrow> string \<Rightarrow> p_exp \<Rightarrow> p_exp \<Rightarrow> bool" where
  "safe_subst_exp e x e' e_f = (\<exists> vl. unique_post_vars vl \<and> pre_vars vl = lam_vars e \<and>
    x \<notin> ref_vars e \<and> post_vars vl \<inter> (lam_vars e \<union> free_vars e \<union> free_vars e' \<union> ref_vars e \<union> ref_vars e') = {} \<and>
    subst_exp (lam_var_list_remove e vl) x e' = e_f)"      

lemma eq_own: "\<exists> r. is_own r"    
  apply (rule_tac x="OwnPerm" in exI)
  apply (simp add: is_own_def)
  done
  
    (* 
      ####################################
        P11. start for substitution type preservation
      ####################################
    *)        
  
lemma subst_free_vars: "\<lbrakk> x \<in> free_vars (subst_exp e y e') \<rbrakk> \<Longrightarrow> (x \<in> free_vars e \<and> x \<noteq> y) \<or> x \<in> free_vars e'"    
  apply (induct e)
        apply (auto)
      apply (case_tac xa)
       apply (auto)
      apply (case_tac "y = x1")
       apply (auto)
     apply (case_tac xa)
      apply (auto)
     apply (case_tac "y = x1")
      apply (auto)
    apply (case_tac "y = x1a")
     apply (auto)
   apply (case_tac "y = x")
    apply (auto)
  apply (case_tac "y = x1a")
   apply (auto)
  done
 
lemma free_res_vars: "\<lbrakk> Var x \<in> res_vars delta e \<rbrakk> \<Longrightarrow> x \<in> free_vars e"    
  apply (induct e)
        apply (auto)
  apply (case_tac xa)
   apply (auto)
  done
  
lemma free_res_vars_rev: "\<lbrakk> x \<in> free_vars e \<rbrakk> \<Longrightarrow> Var x \<in> res_vars delta e"      
  apply (induct e)
        apply (auto)
  apply (case_tac xa)
   apply (auto)
  done
    
lemma subst_res_vars: "\<lbrakk> x \<in> res_vars delta (subst_exp e y e') \<rbrakk> \<Longrightarrow> (x \<in> res_vars delta e \<and> x \<noteq> Var y) \<or> x \<in> res_vars delta e'"    
  apply (induct e)
        apply (auto)
      apply (case_tac xa)
       apply (auto)
      apply (case_tac "y = x1")
       apply (auto)
     apply (case_tac xa)
      apply (auto)
     apply (case_tac "y = x1")
      apply (auto)
    apply (case_tac "y = x1a")
     apply (auto)
   apply (case_tac "y = x1a")
    apply (auto)
  apply (case_tac "y = x1a")
   apply (auto)
  done    
    
lemma subst_np_vars: "\<lbrakk> x \<in> non_prim_vars env delta (subst_exp e y e') \<rbrakk> \<Longrightarrow> (x \<in> non_prim_vars env delta e \<and> x \<noteq> Var y) \<or> x \<in> non_prim_vars env delta e'"    
  apply (simp add: non_prim_vars_def)
  apply (auto)
   apply (cut_tac x="x" and y="y" and e="e" and e'="e'" in subst_res_vars)
    apply (auto)
  apply (cut_tac x="x" and y="y" and e="e" and e'="e'" in subst_res_vars)
   apply (auto)
  done      
    (*
lemma no_subst_ref_vars: "\<lbrakk> x \<notin> free_vars e; y \<notin> ref_vars e \<rbrakk> \<Longrightarrow> y \<notin> ref_vars (subst_exp e x e')"  
  apply (induct e)
        apply (auto)
 (* apply (simp add: subst_name_match_def)*)
  done  
  
lemma subst_ref_vars: "\<lbrakk> y \<notin> ref_vars e; y \<notin> ref_vars e' \<rbrakk> \<Longrightarrow> y \<notin> ref_vars (subst_exp e x e')"  
  apply (induct e)
        apply (auto)
  done*)
      
lemma subst_type_preserve_no_fv: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; x \<notin> free_vars e \<rbrakk> \<Longrightarrow> well_typed env delta r_s1 (subst_exp e x e') tau r_s2 rx"
  apply (induction e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
    (* var case *)
      apply (case_tac xa)
       apply (auto)
     (*  apply (simp add: subst_name_match_def)*)
    (* pair case *)
      apply (rule_tac x="r_s2a" in exI)
      apply (rule_tac x="r_s3" in exI)
      apply (rule_tac x="rx1" in exI)
      apply (auto)
      apply (rule_tac x="rx2" in exI)
      apply (auto)
    (* if case *)
     apply (rule_tac x="rx'" in exI)
     apply (rule_tac x="r_s2a" in exI)
     apply (auto)
     apply (rule_tac x="rx1" in exI)
     apply (auto)
     apply (rule_tac x="rx2" in exI)
     apply (auto)
    (* lambda case *)
   apply (rule_tac x="rxa" in exI)
   apply (auto)
   apply (rule_tac x="r_end" in exI)
   apply (rule_tac x="r_s'" in exI)
   apply (auto)
    (* app case *)
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="r" in exI)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="r_s2a" in exI)
  apply (rule_tac x="rx1" in exI)
  apply (auto)
  apply (rule_tac x="rx2" in exI)
  apply (rule_tac x="r_s3" in exI)
  apply (auto)
  done        
  
end