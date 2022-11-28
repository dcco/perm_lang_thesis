theory ReduceProper
  imports SafeSubRename ResMapValid
begin
  
fun path_lookup :: "nres_map \<Rightarrow> string \<Rightarrow> string list \<Rightarrow> string \<Rightarrow> bool" where
  "path_lookup rs_map z Nil x = (z = x)"
| "path_lookup rs_map z (y # t) x = (case rs_map z of
    None \<Rightarrow> False
    | Some r_s \<Rightarrow> r_s (Loc y) \<noteq> NoPerm \<and> path_lookup rs_map y t x
  )"    

lemma path_lookup_parent: "\<lbrakk> l \<noteq> Nil; path_lookup rs_map z l x; valid_nres_map s rs_map \<rbrakk> \<Longrightarrow>
  (\<exists> l' y r_s. path_lookup rs_map z l' y \<and> rs_map y = Some r_s \<and> r_s (Loc x) \<noteq> NoPerm )"
  apply (induct l arbitrary: z)
   apply (auto)
  apply (case_tac "rs_map z")
   apply (auto)
    (* case where we have reached x *)
  apply (case_tac "a = x")
   apply (rule_tac x="Nil" in exI)
   apply (auto)
    (* otherwise, induct *)
  apply (case_tac "l = []")
   apply (auto)
  apply (case_tac "\<exists>l' y. path_lookup rs_map a l' y \<and> (\<exists>r_s. rs_map y = Some r_s \<and> r_s (Loc x) \<noteq> NoPerm)")
   apply (erule_tac exE)
   apply (auto)
  apply (rule_tac x="a # l'" in exI)
  apply (auto)
  done
    
lemma path_lookup_append: "\<lbrakk> path_lookup rs_map x l y; path_lookup rs_map y m z \<rbrakk> \<Longrightarrow> path_lookup rs_map x (l @ m) z"    
  apply (induct l arbitrary: x)
   apply (auto)
  apply (case_tac "rs_map x")
   apply (auto)
  done   
    
lemma add_path_lookup: "\<lbrakk> path_lookup rs_map x l y; rs_map z = None; x \<noteq> z \<rbrakk> \<Longrightarrow> path_lookup (add_env rs_map z r_s) x l y"    
  apply (induct l arbitrary: x)
   apply (auto)
  apply (simp add: add_env_def)
  apply (case_tac "rs_map x")
   apply (auto)
  apply (case_tac "a = z")
   apply (case_tac l)
    apply (auto)
  apply (simp add: add_env_def)
  done  
  
(*
fun own_pairs where
  "own_pairs (ConstExp c) = {}"
| "own_pairs (OpExp xop) = {}"
| "own_pairs (VarExp v) = (case v of
    VarType x \<Rightarrow> {}
    | LocType x y \<Rightarrow> {(y, x)}
  )"  
| "own_pairs (PairExp e1 e2) = (own_pairs e1 \<union> own_pairs e2)"
| "own_pairs (IfExp e1 e2 e3) = (own_pairs e1 \<union> own_pairs e2 \<union> own_pairs e3)"
| "own_pairs (LamExp x e) = own_pairs e"  
| "own_pairs (AppExp e1 e2) = (own_pairs e1 \<union> own_pairs e2)"  
  
    (* ##### given a perm set, we derive its "resource completion" by taking all of the resources that are reachable from it.
        in other words, for each permission z in s, we lookup its resource map, and take all of the resources in it, as well
        as recursing on each resource. #####
     *)  
  
 
    
    (* ##### proper expressions ##### *)
  
definition proper_exp :: "nres_map \<Rightarrow> p_exp \<Rightarrow> bool" where
  "proper_exp rs_map e = (\<forall> x y. (x, y) \<in> own_pairs e \<longrightarrow> (\<exists> l. path_lookup rs_map x l y))"

lemma proper_pair: "\<lbrakk> proper_exp rs_map (PairExp e1 e2) \<rbrakk> \<Longrightarrow> proper_exp rs_map e1 \<and> proper_exp rs_map e2"  
  apply (simp add: proper_exp_def)
  done

lemma proper_if: "\<lbrakk> proper_exp rs_map (IfExp e1 e2 e3) \<rbrakk> \<Longrightarrow> proper_exp rs_map e1 \<and> proper_exp rs_map e2 \<and> proper_exp rs_map e3"  
  apply (simp add: proper_exp_def)
  done    

lemma proper_app: "\<lbrakk> proper_exp rs_map (AppExp e1 e2) \<rbrakk> \<Longrightarrow> proper_exp rs_map e1 \<and> proper_exp rs_map e2"  
  apply (simp add: proper_exp_def)
  done
    
lemma proper_subst_exp: "\<lbrakk> proper_exp rs_map e; proper_exp rs_map e' \<rbrakk> \<Longrightarrow> proper_exp rs_map (subst_exp e x e')"
  apply (induct e)
        apply (auto)
      apply (case_tac xa)
       apply (auto)
     apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_pair)
      apply (auto)
     apply (simp add: proper_exp_def)
    apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" and ?e3.0="e3" in proper_if)
     apply (auto)
    apply (simp add: proper_exp_def)
   apply (simp add: proper_exp_def)
  apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_app)
   apply (auto)
  apply (simp add: proper_exp_def)
  done
 
lemma proper_alpha_rename: "\<lbrakk> proper_exp rs_map e \<rbrakk> \<Longrightarrow> proper_exp rs_map (deep_alpha_rename e a b)"    
  apply (induct e)
        apply (auto)
       apply (simp add: proper_exp_def)
       apply (auto)
       apply (case_tac x)
        apply (auto)
       apply (case_tac "a = x1")
        apply (auto)
      apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_pair)
       apply (auto)
      apply (simp add: proper_exp_def)
     apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" and ?e3.0="e3" in proper_if)
      apply (auto)
     apply (simp add: proper_exp_def)
    apply (simp add: proper_exp_def)
   apply (simp add: proper_exp_def)
  apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_app)
   apply (auto)
  apply (simp add: proper_exp_def)
  done
    
lemma proper_lam_var_remove_ex: "\<lbrakk> proper_exp rs_map e; well_typed env r_s1 e tau r_s2 rx \<rbrakk> \<Longrightarrow> proper_exp rs_map (lam_var_remove e a b)"      
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
      apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_pair)
       apply (auto)
      apply (simp add: proper_exp_def)
     apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" and ?e3.0="e3" in proper_if)
      apply (auto)
     apply (simp add: proper_exp_def)
    apply (cut_tac rs_map="rs_map" and e="e" and a="a" and b="b" in proper_alpha_rename)
     apply (simp add: proper_exp_def)
    apply (simp add: proper_exp_def)
   apply (simp add: proper_exp_def)
  apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_app)
   apply (auto)
  apply (simp add: proper_exp_def)
  done
    
lemma proper_lam_var_remove: "\<lbrakk> proper_exp rs_map e \<rbrakk> \<Longrightarrow> proper_exp rs_map (lam_var_remove e a b)"   
  apply (induct e)
        apply (auto)
      apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_pair)
       apply (auto)
      apply (simp add: proper_exp_def)
     apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" and ?e3.0="e3" in proper_if)
      apply (auto)
     apply (simp add: proper_exp_def)
    apply (cut_tac rs_map="rs_map" and e="e" and a="a" and b="b" in proper_alpha_rename)
     apply (simp add: proper_exp_def)
    apply (simp add: proper_exp_def)
   apply (simp add: proper_exp_def)
  apply (cut_tac rs_map="rs_map" and ?e1.0="e1" and ?e2.0="e2" in proper_app)
   apply (auto)
  apply (simp add: proper_exp_def)
  done
      
lemma lam_var_remove_eq: "\<lbrakk> a \<notin> lam_vars e \<rbrakk> \<Longrightarrow> lam_var_remove e a b = e"    
  apply (induct e)
        apply (auto)
  done
  
lemma proper_lvlr_ex: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; proper_exp rs_map e; unique_post_vars vl;
  post_vars vl \<inter> (free_vars e \<union> lam_vars e) = {} \<rbrakk> \<Longrightarrow> proper_exp rs_map (lam_var_list_remove e vl)"   
  apply (induct vl arbitrary: e)
   apply (auto)
  (*apply (case_tac "a \<notin> lam_vars e")
   apply (simp add: lam_var_remove_eq)*)
  apply (cut_tac rs_map="rs_map" and e="e" and a="a" and b="b" in proper_lam_var_remove_ex)
    apply (auto)
    (* we have to prove that the post vars are still disjoint from the lam_vars / ref_vars, which is true since
        the only new lam_var is b, which must be disjoint from the rest of the post_var list *)
  apply (case_tac "post_vars vl \<inter> (free_vars (lam_var_remove e a b) \<union> lam_vars (lam_var_remove e a b)) \<noteq> {}")
   apply (auto)
    apply (cut_tac x="x" and e="e" and a="a" and b="b" in lam_var_remove_free_var_none)
     apply (auto)
   apply (case_tac "x = b")
    apply (auto)
   apply (cut_tac x="x" and e="e" and a="a" and b="b" in lam_var_remove_lam_var_none)
     apply (auto)
    (* the last part of the induction is to prove that e is still well-typed *)
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and e="e" and x="a" and y="b" in lam_var_remove_type_preserve)
      apply (auto)
  done
  
lemma proper_safe_subst_exp: "\<lbrakk> proper_exp rs_map e; well_typed env r_s1 e tau r_s2 rx;
  proper_exp rs_map e'; safe_subst_exp e x e' e_f \<rbrakk> \<Longrightarrow> proper_exp rs_map e_f"    
  apply (simp add: safe_subst_exp_def)
  apply (auto)
  apply (rule_tac proper_subst_exp)
   apply (rule_tac proper_lvlr_ex)
      apply (auto)
  done*)


  
definition ext_delta :: "owner_env \<Rightarrow> string \<Rightarrow> perm_use_env \<Rightarrow> owner_env" where
  "ext_delta delta x r_s = (\<lambda> y. if r_s (Loc (delta y)) \<noteq> NoPerm then x else delta y)"      
    
end