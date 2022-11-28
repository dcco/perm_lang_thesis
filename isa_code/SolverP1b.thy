theory SolverP1b
  imports SolverP1
begin
  
fun perm_subst_perm where
  "perm_subst_perm rho (SPerm p) = SPerm p"  
| "perm_subst_perm rho (SVar r) = (case rho r of
    None \<Rightarrow> SVar r
    | Some p \<Rightarrow> p
  )"  
  
fun perm_subst_aff where  
  "perm_subst_aff rho (AffConst a) = SPerm (as_perm a)"
| "perm_subst_aff rho (AffVar a) = (case rho a of
    None \<Rightarrow> SVar a
    | Some p \<Rightarrow> p
  )"
  
fun perm_subst_eq_list where
  "perm_subst_eq_list rho [] = []"  
| "perm_subst_eq_list rho ((p1, p2) # p_t) = (perm_subst_perm rho p1, perm_subst_perm rho p2) # (perm_subst_eq_list rho p_t)"

fun pvar_perm_l where
  "pvar_perm_l (SVar r) = [r]"
  | "pvar_perm_l (SPerm p) = []"

fun pvar_eq_list where
  "pvar_eq_list [] = []"
| "pvar_eq_list ((p1, p2) # p_t) = union_list (union_list (pvar_perm_l p1) (pvar_perm_l p2)) (pvar_eq_list p_t)"

definition pvar_total where  
  "pvar_total c_list = length (pvar_eq_list c_list)"  
  
fun perm_cons :: "s_perm \<Rightarrow> nat" where
  "perm_cons (SPerm p) = 1"
| "perm_cons (SVar r) = 0"
  
fun pcons_list where
  "pcons_list [] = 0"
| "pcons_list ((p1, p2) # p_t) = (perm_cons p1) + (pcons_list p_t)"  
  
definition p_unify_rel where
  "p_unify_rel = measures [pvar_total, pcons_list, length]"

lemma pvar_perm_fresh_list: "fresh_in_list (pvar_perm_l p)"    
  apply (induct p)
   apply (auto)
  done
  
lemma pvar_eq_fresh_list: "fresh_in_list (pvar_eq_list p_list)"    
  apply (induct p_list)
   apply (auto)
  apply (rule_tac union_fresh_list)
  apply (rule_tac union_fresh_list)
    apply (rule_tac pvar_perm_fresh_list)
   apply (rule_tac pvar_perm_fresh_list)
  apply (simp)
  done

lemma cons_less_pvar_total: "pvar_total p_list \<le> pvar_total (p # p_list)"  
  apply (simp add: pvar_total_def)
  apply (case_tac p)
  apply (auto)
  apply (rule_tac sub_list_less_length)
   apply (rule_tac pvar_eq_fresh_list)
  apply (rule_tac union_sub_list2)
  apply (rule_tac id_sub_list)
  done  
  
lemma simp_p_unify_rel: "(p_list, (x, y) # p_list) \<in> p_unify_rel"
  apply (simp add: p_unify_rel_def)
  apply (auto)
  apply (cut_tac p_list="p_list" and p="(x, y)" in cons_less_pvar_total)
  apply (auto)
  done
    
lemma orient_less_pvar_total: "pvar_total ((q, p) # p_list) \<le> pvar_total ((p, q) # p_list)"      
  apply (simp add: pvar_total_def)
  apply (rule_tac sub_list_less_length)
   apply (rule_tac union_fresh_list)
    apply (rule_tac union_fresh_list)
     apply (rule_tac pvar_perm_fresh_list)
    apply (rule_tac pvar_perm_fresh_list)
   apply (rule_tac pvar_eq_fresh_list)
  apply (rule_tac dist_union_sub_list)
   apply (rule_tac union_sub_list1)
   apply (rule_tac dist_union_sub_list)
    apply (rule_tac union_sub_list2)
    apply (rule_tac id_sub_list)
   apply (rule_tac union_sub_list1)
   apply (rule_tac id_sub_list)
  apply (rule_tac union_sub_list2)
  apply (rule_tac id_sub_list)
  done    
  
lemma orient_p_unify_rel: "\<lbrakk> \<forall> q. p \<noteq> SVar q \<rbrakk> \<Longrightarrow> ((SVar r, p) # p_list, (p, SVar r) # p_list) \<in> p_unify_rel"   
  apply (simp add: p_unify_rel_def)
  apply (auto)
   apply (cut_tac q="SVar r" and p="p" and p_list="p_list" in orient_less_pvar_total)
   apply (auto)
  apply (case_tac p)
   apply (auto)
  done
    
lemma perm_subst_perm_sub_list: "\<lbrakk> sub_list (pvar_perm_l p) l; sub_list (pvar_perm_l q) l \<rbrakk> \<Longrightarrow>
  sub_list (pvar_perm_l (perm_subst_perm (add_env empty_env x q) p)) l"
  apply (induct p)
   apply (auto)
  apply (simp add: add_env_def)
  apply (simp add: empty_env_def)
  done
    
lemma perm_subst_sub_list: "\<lbrakk> sub_list (pvar_perm_l p) l; sub_list (pvar_eq_list p_list) l \<rbrakk> \<Longrightarrow>
  sub_list (pvar_eq_list (perm_subst_eq_list (add_env empty_env r p) p_list)) l"   
  apply (induct p_list arbitrary: l)
   apply (auto)
  apply (cut_tac la="union_list (pvar_perm_l a) (pvar_perm_l b)" and lb="pvar_eq_list p_list" and lc="l" in union_sub_list_rev)
   apply (auto)
  apply (cut_tac la="pvar_perm_l a" and lb="pvar_perm_l b" and lc="l" in union_sub_list_rev)
   apply (auto)
  apply (rule_tac dist_union_sub_list)
   apply (rule_tac dist_union_sub_list)
    apply (rule_tac perm_subst_perm_sub_list)
     apply (auto)
  apply (rule_tac perm_subst_perm_sub_list)
   apply (auto)
  done
    
lemma perm_subst_perm_list_contain: "\<lbrakk> SVar r \<noteq> p \<rbrakk> \<Longrightarrow>
  \<not> list_contain (pvar_perm_l (perm_subst_perm (add_env empty_env r p) q)) r"
  apply (induct q)
   apply (auto)
  apply (simp add: add_env_def)
  apply (case_tac "r = x")
   apply (auto)
   apply (case_tac p)
    apply (auto)
  apply (simp add: empty_env_def)
  done
    
lemma perm_subst_list_contain: "\<lbrakk> SVar r \<noteq> p \<rbrakk> \<Longrightarrow>
  \<not> list_contain (pvar_eq_list (perm_subst_eq_list (add_env empty_env r p) p_list)) r"    
  apply (induct p_list)
   apply (auto)
  apply (cut_tac ?l1.0="union_list (pvar_perm_l (perm_subst_perm (add_env empty_env r p) a)) (pvar_perm_l (perm_subst_perm (add_env empty_env r p) b))"
      and ?l2.0="pvar_eq_list (perm_subst_eq_list (add_env empty_env r p) p_list)" and x="r" in dist_union_list_contain)
   apply (auto)
  apply (cut_tac ?l1.0="pvar_perm_l (perm_subst_perm (add_env empty_env r p) a)"
      and ?l2.0="pvar_perm_l (perm_subst_perm (add_env empty_env r p) b)" and x="r" in dist_union_list_contain)
   apply (auto)
   apply (cut_tac p="p" and q="a" and r="r" in perm_subst_perm_list_contain)
    apply (auto)
  apply (cut_tac p="p" and q="b" and r="r" in perm_subst_perm_list_contain)
   apply (auto)
  done    
    
lemma epur_less_pvar_total: "\<lbrakk> SVar r \<noteq> p \<rbrakk> \<Longrightarrow>
  length (pvar_eq_list (perm_subst_eq_list (add_env empty_env r p) p_list)) \<le>
  length (rem_list (union_list (add_list (pvar_perm_l p) r) (pvar_eq_list p_list)) r)"    
  apply (rule_tac sub_list_less_length)
   apply (rule_tac pvar_eq_fresh_list)
  apply (rule_tac rem_sub_list)
   apply (rule_tac perm_subst_sub_list)
    apply (rule_tac union_sub_list1)
    apply (rule_tac add_sub_list)
    apply (rule_tac id_sub_list)    
   apply (rule_tac union_sub_list2)
   apply (rule_tac id_sub_list)
  apply (rule_tac perm_subst_list_contain)
  apply (simp)
  done    
    
lemma elim_p_unify_rel: "\<lbrakk> SVar r \<noteq> p \<rbrakk> \<Longrightarrow>
  (perm_subst_eq_list (add_env empty_env r p) p_list, (SVar r, p) # p_list) \<in> p_unify_rel"
  apply (case_tac "\<not> length (pvar_eq_list (perm_subst_eq_list (add_env empty_env r p) p_list))
     < length (union_list (add_list (pvar_perm_l p) r) (pvar_eq_list p_list))")
   apply (cut_tac r="r" and p="p" and p_list="p_list" in epur_less_pvar_total)
    apply (simp)
   apply (cut_tac l="union_list (add_list (pvar_perm_l p) r) (pvar_eq_list p_list)" and x="r" in contain_rem_list_length)
    apply (rule_tac union_list_contain1)
    apply (simp add: add_list_def)
   apply (auto)
  apply (simp add: p_unify_rel_def)
  apply (auto)
    apply (simp_all add: pvar_total_def)
  done

lemma perm_subst_perm_eq: "\<lbrakk> p_sub r = sol_subst_perm p_sub p \<rbrakk> \<Longrightarrow>
 sol_subst_perm p_sub (perm_subst_perm (add_env empty_env r p) a) = sol_subst_perm p_sub a"    
  apply (case_tac a)
   apply (auto)
  apply (simp add: add_env_def)
  apply (simp add: empty_env_def)
  apply (auto)
  done

lemma perm_subst_perm_eq_sat: "\<lbrakk> perm_eq_sat_f p_sub p_list; p_sub r = sol_subst_perm p_sub p \<rbrakk> \<Longrightarrow>
  perm_eq_sat_f p_sub (perm_subst_eq_list (add_env empty_env r p) p_list)"
  apply (induct p_list)
   apply (auto)
  apply (simp add: perm_subst_perm_eq)
  done    
  
lemma perm_subst_perm_eq_sat_rev: "\<lbrakk> perm_eq_sat_f p_sub (perm_subst_eq_list (add_env empty_env r p) p_list);
  p_sub r = sol_subst_perm p_sub p \<rbrakk> \<Longrightarrow> perm_eq_sat_f p_sub p_list"
  apply (induct p_list)
   apply (auto)
  apply (simp add: perm_subst_perm_eq)
  done        
    
function unify_perm where
  "unify_perm [] = Some empty_env"
| "unify_perm ((p1, p2) # p_t) = (case (p1, p2) of
    (SVar r, p) \<Rightarrow>
      if p = SVar r then unify_perm p_t
      else (case unify_perm (perm_subst_eq_list (add_env empty_env r p) p_t) of
        None \<Rightarrow> None
        | Some rho \<Rightarrow> Some (add_env rho r (perm_subst_perm rho p))
      )
    | (p, SVar r) \<Rightarrow> unify_perm ((SVar r, p) # p_t)
    | (SPerm p, SPerm q) \<Rightarrow> if p = q then unify_perm p_t else None
  )"
  by pat_completeness auto
termination
  apply (relation "p_unify_rel")
                      apply (auto)
    (* simple cases *)
      apply (simp add: p_unify_rel_def)
     apply (simp_all add: simp_p_unify_rel)
   apply (simp add: orient_p_unify_rel)
  apply (simp add: elim_p_unify_rel)
  done
  
lemma unify_perm_unsat: "\<lbrakk> unify_perm p_list = None \<rbrakk> \<Longrightarrow> \<not> perm_eq_sat p_sub p_list"
  apply (induct rule: wf_induct [where r=p_unify_rel])
   apply (auto)
   apply (simp add: p_unify_rel_def)
  apply (case_tac x)
   apply (auto)
    (* elim case *)
  apply (case_tac "\<exists> r. a = SVar r")
   apply (auto)
   apply (simp add: perm_eq_sat_def)
   apply (case_tac "b = SVar r")
    apply (auto)
    apply (simp add: simp_p_unify_rel)
   apply (case_tac "unify_perm (perm_subst_eq_list (add_env empty_env r b) list)")
    apply (auto)
   apply (erule_tac x="perm_subst_eq_list (add_env empty_env r b) list" in allE)
   apply (simp add: elim_p_unify_rel)
   apply (simp add: perm_subst_perm_eq_sat)
     (* orient case *)
  apply (case_tac "\<exists> r. b = SVar r")
   apply (auto)
   apply (erule_tac x=" (SVar r, a) # list" in allE)
   apply (simp add: orient_p_unify_rel)
   apply (case_tac a)
    apply (auto)
   apply (simp add: perm_eq_sat_def)
    (* decomp case *)
  apply (case_tac a)
   apply (auto)
  apply (case_tac b)
   apply (auto)
  apply (erule_tac x="list" in allE)
  apply (simp add: simp_p_unify_rel)
  apply (simp add: perm_eq_sat_def)
  done
   
definition spec_perm_env where
  "spec_perm_env p_sub p_sub' = (\<forall> x. case p_sub x of
    None \<Rightarrow> True
    | Some p \<Rightarrow> (case p of
      SPerm p \<Rightarrow> p_sub' x = p
      | SVar r \<Rightarrow> p_sub' x = p_sub' r
    )
  )"
    
lemma unify_perm_gen: "\<lbrakk> unify_perm p_list = Some p_sub; perm_eq_sat p_subx p_list \<rbrakk> \<Longrightarrow> spec_perm_env p_sub p_subx"
  apply (induct arbitrary: p_sub rule: wf_induct [where r=p_unify_rel])
   apply (simp add: p_unify_rel_def)
  apply (case_tac x)
   apply (auto)
   apply (simp add: p_unify_rel_def)
   apply (simp add: pvar_total_def)
   apply (simp add: spec_perm_env_def)
   apply (simp add: empty_env_def)
    (* var case *)
  apply (case_tac "\<exists> r. a = SVar r")
   apply (auto)
   apply (simp add: perm_eq_sat_def)
    (* - delete case *)
   apply (case_tac "b = SVar r")
    apply (auto)
    apply (erule_tac x="list" in allE)
    apply (simp add: simp_p_unify_rel)
    (* - elim case *)
   apply (case_tac "unify_perm (perm_subst_eq_list (add_env empty_env r b) list)")
    apply (auto)
   apply (erule_tac x="perm_subst_eq_list (add_env empty_env r b) list" in allE)
   apply (auto)
     apply (simp add: elim_p_unify_rel)
    apply (simp add: perm_subst_perm_eq_sat)
    (* > we want to show that p_sub(b) is a specialization of p_subx, we start with case analysis over b *)
   apply (simp add: spec_perm_env_def)
   apply (simp add: add_env_def)
   apply (case_tac b)
    apply (auto)
    (* > the main case is the var case. if a substitution occurs, specialization still holds since p_sub <: p_subx *)
   apply (case_tac "a x2")
    apply (auto)
   apply (erule_tac x="x2" in allE)
    apply (auto)
   apply (case_tac aa)
    apply (auto)
    (* orient case *)
  apply (case_tac "\<exists> r. b = SVar r")
   apply (auto)
   apply (erule_tac x="(SVar r, a) # list" in allE)
   apply (simp add: orient_p_unify_rel)
   apply (case_tac a)
    apply (auto)
   apply (simp add: perm_eq_sat_def)
    (* decomp case *)
  apply (case_tac a)
   apply (auto)
  apply (case_tac b)
   apply (auto)
  apply (erule_tac x="list" in allE)
  apply (simp add: simp_p_unify_rel)
  apply (simp add: perm_eq_sat_def)
  done
    
    (*
lemma unify_perm_sat: "\<lbrakk> unify_perm p_list = Some p_sub; spec_perm_env p_sub p_subx \<rbrakk> \<Longrightarrow> perm_eq_sat p_subx p_list"
  apply (induct arbitrary: p_sub rule: wf_induct [where r=p_unify_rel])
   apply (simp add: p_unify_rel_def)
  apply (case_tac x)
   apply (auto)
    (* var case *)
   apply (case_tac "\<exists> r. a = SVar r")
    apply (auto)
    (* - delete case *)
    apply (case_tac "b = SVar r")
     apply (auto)
    apply (erule_tac x="list" in allE)
    apply (simp add: simp_p_unify_rel)
    apply (case_tac "unify_perm (perm_subst_eq_list (add_env empty_env r b) list)")
     apply (auto)
    *)  
    
lemma add_spec_perm_env_rev: "\<lbrakk> spec_perm_env (add_env p_sub r p) p_sub'; p_sub r = None \<rbrakk> \<Longrightarrow> spec_perm_env p_sub p_sub'"    
  apply (simp add: spec_perm_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "p_sub x")
   apply (auto)
  apply (simp add: add_env_def)
  apply (case_tac "r = x")
   apply (auto)
  done
    
fun pvar_eq_set where
  "pvar_eq_set [] = {}"
| "pvar_eq_set ((p1, p2) # p_t) = pvar_set_perm p1 \<union> pvar_set_perm p2 \<union> pvar_eq_set p_t"    
  
lemma add_pvar_perm: "\<lbrakk> x \<notin> pvar_set_perm p; x \<notin> pvar_set_perm q \<rbrakk> \<Longrightarrow>
    x \<notin> pvar_set_perm (perm_subst_perm (add_env empty_env r p) q)"  
  apply (case_tac q)
   apply (auto)
  apply (simp add: add_env_def)
  apply (case_tac "r = x2")
   apply (auto)
  apply (simp add: empty_env_def)
  done
    
lemma add_pvar_eq_set: "\<lbrakk> x \<notin> pvar_set_perm p; x \<notin> pvar_eq_set p_list \<rbrakk> \<Longrightarrow> x \<notin> pvar_eq_set (perm_subst_eq_list (add_env empty_env r p) p_list)"  
  apply (induct p_list)
   apply (auto)
   apply (simp add: add_pvar_perm)
  apply (simp add: add_pvar_perm)
  done
    
lemma perm_subst_pvar_perm: "\<lbrakk> p \<noteq> SVar r \<rbrakk> \<Longrightarrow> r \<notin> pvar_set_perm (perm_subst_perm (add_env empty_env r p) q)"    
  apply (case_tac q)
   apply (auto)
  apply (simp add: add_env_def)
  apply (case_tac "r = x2")
   apply (auto)
   apply (case_tac p)
    apply (auto)
  apply (simp add: empty_env_def)
  done
  
lemma perm_subst_pvar_eq_set: "\<lbrakk> p \<noteq> SVar r \<rbrakk> \<Longrightarrow> r \<notin> pvar_eq_set (perm_subst_eq_list (add_env empty_env r p) p_list)"    
  apply (induct p_list)
   apply (auto)
   apply (simp add: perm_subst_pvar_perm)
  apply (simp add: perm_subst_pvar_perm)
  done
    
definition perm_sub_range where
  "perm_sub_range p_sub = { x | x. \<exists> y. case p_sub y of None \<Rightarrow> False | Some p \<Rightarrow> x \<in> pvar_set_perm p }"  
    
definition uppr_res where
  "uppr_res p_sub x = (p_sub x = None \<and> x \<notin> perm_sub_range p_sub)"
    
lemma unify_perm_pvar_range_ih: "\<lbrakk> unify_perm p_list = Some p_sub; x \<notin> pvar_eq_set p_list \<rbrakk> \<Longrightarrow> uppr_res p_sub x"    
  apply (induct arbitrary: p_sub rule: wf_induct [where r=p_unify_rel])
   apply (simp add: p_unify_rel_def)
  apply (case_tac xa)
   apply (auto)
   apply (simp add: uppr_res_def)
   apply (simp add: perm_sub_range_def)
   apply (simp add: empty_env_def)
    (* var case *)
  apply (case_tac "\<exists> r. a = SVar r")
   apply (auto)
    (* - delete case *)
   apply (case_tac "b = SVar r")
    apply (auto)
    apply (erule_tac x="list" in allE)
    apply (simp add: simp_p_unify_rel)
    (* - elim case *)
   apply (case_tac "unify_perm (perm_subst_eq_list (add_env empty_env r b) list)")
    apply (auto)
   apply (erule_tac x="perm_subst_eq_list (add_env empty_env r b) list" in allE)
   apply (auto)
     apply (simp add: elim_p_unify_rel)
    apply (simp add: add_pvar_eq_set)
   apply (simp add: add_env_def)
   apply (simp add: uppr_res_def)
   apply (simp add: perm_sub_range_def)
   apply (auto)
   apply (case_tac b)
    apply (auto)
   apply (erule_tac x="x2" in allE)
   apply (case_tac "a x2")
    apply (auto)
    (* orient case *)
  apply (case_tac "\<exists> r. b = SVar r")
   apply (auto)
   apply (erule_tac x="(SVar r, a) # list" in allE)
   apply (simp add: orient_p_unify_rel)
   apply (case_tac a)
    apply (auto)
    (* decomp case *)
  apply (case_tac a)
   apply (auto)
  apply (case_tac b)
   apply (auto)
  apply (erule_tac x="list" in allE)
  apply (simp add: simp_p_unify_rel)
  apply (case_tac "x1 = x1a")
   apply (auto)
  done      
  
lemma unify_perm_pvar_range: "\<lbrakk> unify_perm p_list = Some p_sub; x \<notin> pvar_eq_set p_list \<rbrakk> \<Longrightarrow> x \<notin> perm_sub_range p_sub"  
  apply (cut_tac unify_perm_pvar_range_ih)
    apply (auto)
  apply (simp add: uppr_res_def)
  done         
    
lemma unify_perm_pvar_dom: "\<lbrakk> unify_perm p_list = Some p_sub; x \<notin> pvar_eq_set p_list \<rbrakk> \<Longrightarrow> p_sub x = None"  
  apply (cut_tac unify_perm_pvar_range_ih)
    apply (auto)
  apply (simp add: uppr_res_def)
  done          
    
lemma unify_perm_sat: "\<lbrakk> unify_perm p_list = Some p_sub; spec_perm_env p_sub p_subx \<rbrakk> \<Longrightarrow> perm_eq_sat p_subx p_list"
  apply (induct arbitrary: p_sub rule: wf_induct [where r=p_unify_rel])
   apply (simp add: p_unify_rel_def)
  apply (case_tac x)
   apply (auto)
   apply (simp add: perm_eq_sat_def)
    (* var case *)
  apply (case_tac "\<exists> r. a = SVar r")
   apply (auto)
    (* - delete case *)
   apply (case_tac "b = SVar r")
    apply (auto)
    apply (erule_tac x="list" in allE)
    apply (simp add: simp_p_unify_rel)
    apply (simp add: perm_eq_sat_def)
    (* - elim case *)
   apply (case_tac "unify_perm (perm_subst_eq_list (add_env empty_env r b) list)")
    apply (auto)
   apply (erule_tac x="perm_subst_eq_list (add_env empty_env r b) list" in allE)
   apply (auto)
     apply (simp add: elim_p_unify_rel)
    apply (cut_tac p_sub="a" and r="r" and p="perm_subst_perm a b" and p_sub'="p_subx" in add_spec_perm_env_rev)
      apply (auto)
    apply (cut_tac p_sub="a" and x="r" and p_list="perm_subst_eq_list (add_env empty_env r b) list" in unify_perm_pvar_dom)
      apply (auto)
    apply (simp add: perm_subst_pvar_eq_set)
    (* > prelim: p_subx r = sol_subst_perm p_subx b. the idea is that r is assigned a value in p_subx.
        in the original a, it is assigned b. if b is a permission, this is straightforward. *)
   apply (case_tac "\<not> p_subx r = sol_subst_perm p_subx b")
    apply (case_tac "\<not> (case add_env a r (perm_subst_perm a b) r of None \<Rightarrow> True | Some (SPerm pa) \<Rightarrow> p_subx r = pa | Some (SVar ra) \<Rightarrow> p_subx r = p_subx ra)")
     apply (simp add: spec_perm_env_def)
    apply (case_tac b)
     apply (auto)
     apply (simp add: add_env_def)
     (* > if b is a var, then the var it evaluates to should be equal to r *)
    apply (simp add: add_env_def)
    apply (case_tac "a x2")
     apply (auto)
    apply (simp add: spec_perm_env_def)
    apply (erule_tac x="x2" in allE)
    apply (auto)
    apply (case_tac aa)
     apply (auto)
      (* > unroll satisfiability definition *)
   apply (simp add: perm_eq_sat_def)
   apply (simp add: perm_subst_perm_eq_sat_rev)
    (* orient case *)
  apply (case_tac "\<exists> r. b = SVar r")
   apply (auto)
   apply (erule_tac x="(SVar r, a) # list" in allE)
   apply (simp add: orient_p_unify_rel)
   apply (case_tac a)
    apply (auto)
   apply (simp add: perm_eq_sat_def)
    (* decomp case *)
  apply (case_tac a)
   apply (auto)
  apply (case_tac b)
   apply (auto)
  apply (erule_tac x="list" in allE)
  apply (simp add: simp_p_unify_rel)
  apply (case_tac "x1 = x1a")
   apply (auto)
  apply (simp add: perm_eq_sat_def)
  done    
    
 
fun def_req_type where
  "def_req_type rho (ArrayScheme tau) = SPerm UsePerm"
| "def_req_type rho (ChanScheme tau c_end) = SPerm UsePerm"  
| "def_req_type rho (PairScheme t1 t2 p) = perm_subst_perm rho p"
| "def_req_type rho (FunScheme t1 t2 p a) = perm_subst_aff rho a"
| "def_req_type rho tau = SPerm NoPerm"    
    
fun subst_req_type where
  "subst_req_type sigma rho (ArrayScheme tau) = SPerm UsePerm"
| "subst_req_type sigma rho (ChanScheme tau c_end) = SPerm UsePerm"  
| "subst_req_type sigma rho (PairScheme t1 t2 p) = perm_subst_perm rho p"
| "subst_req_type sigma rho (FunScheme t1 t2 p a) = perm_subst_aff rho a"
| "subst_req_type sigma rho (VarScheme a) = (case sigma a of
    None \<Rightarrow> SPerm NoPerm
    | Some tau' \<Rightarrow> def_req_type rho tau'
  )"
| "subst_req_type sigma rho tau = SPerm NoPerm"
  
fun full_subst_permx where
  "full_subst_permx sigma rho (XPerm p) = XPerm (perm_subst_perm rho p)"
| "full_subst_permx sigma rho (XType a) = XPerm (subst_req_type sigma rho (VarScheme a))"    
| "full_subst_permx sigma rho (XComp px qx) = XComp (full_subst_permx sigma rho px) (full_subst_permx sigma rho qx)"  
| "full_subst_permx sigma rho (XLift px q) = XLift (full_subst_permx sigma rho px) (perm_subst_perm rho q)"
| "full_subst_permx sigma rho (XIfZero px qx) = XIfZero (full_subst_permx sigma rho px) (full_subst_permx sigma rho qx)"

fun reduce_subst_crn where
  "reduce_subst_crn sigma rho (UnifyCrn t1 t2) = []"
| "reduce_subst_crn sigma rho (LeqCrn px q) = [LeqCrn2 (full_subst_permx sigma rho px) (perm_subst_perm rho q)]"
| "reduce_subst_crn sigma rho (LeqTypeCrn tau q) = [LeqCrn2 (XPerm (subst_req_type sigma rho tau)) (perm_subst_perm rho q)]"  
| "reduce_subst_crn sigma rho (DisjCrn px qx) = [DisjCrn2 (full_subst_permx sigma rho px) (full_subst_permx sigma rho qx)]"  
| "reduce_subst_crn sigma rho (SemiDisjCrn px qx) = [MiniDisjCrn2 (full_subst_permx sigma rho px) (full_subst_permx sigma rho qx)]" 
(*| "reduce_subst_crn sigma rho (MemValCrn tau tau') = []"  *)
  
fun reduce_subst_list where
  "reduce_subst_list sigma rho [] = []"
| "reduce_subst_list sigma rho (c # c_t) = (reduce_subst_crn sigma rho c @ reduce_subst_list sigma rho c_t)"
  (*
fun no_mv_crn where
  "no_mv_crn [] = True"  
| "no_mv_crn (c # c_t) = (case c of
    MemValCrn tau tau' \<Rightarrow> False
    | c' \<Rightarrow> no_mv_crn c_t
  )"  *)
  
definition reduce_crn_list :: "perm_crn list \<Rightarrow> (perm_crn2 list) option" where
  "reduce_crn_list c_list = (case unify_type (unify_subset c_list) of
    None \<Rightarrow> None
    | Some (sigma, p_eq) \<Rightarrow> (case unify_perm p_eq of
      None \<Rightarrow> None
      | Some rho \<Rightarrow> Some (reduce_subst_list sigma rho c_list)
    )
  )"

    
lemma reduce_crn_list_unsat: "\<lbrakk> reduce_crn_list c_list = None \<rbrakk> \<Longrightarrow> \<not> dir_sol_sat t_sub p_sub c_list"
  apply (simp add: reduce_crn_list_def)
  apply (auto)
  apply (cut_tac t_sub="t_sub" and p_sub="p_sub" and c_list="c_list" in dir_sol_type_eq_sat)
   apply (auto)
  apply (case_tac "unify_type (unify_subset c_list)")
   apply (auto)
   apply (cut_tac t_sub="indir_sub t_sub" and p_sub="p_sub" and c_list="unify_subset c_list" in unify_type_unsat)
    apply (simp_all)
  apply (case_tac "unify_perm b")
   apply (auto)
  apply (cut_tac p_list="b" and p_sub="p_sub" in unify_perm_unsat)
   apply (auto)
  apply (cut_tac t_sub="a" and t_subx="indir_sub t_sub" and c_list="unify_subset c_list" and p_eq="b" and p_sub="p_sub" in unify_type_sat)
    apply (auto)
  apply (simp add: uts_res_def)
  done
    
lemma sol_sat_append_split: "\<lbrakk> sol_sat2 p_sub cl1; sol_sat2 p_sub cl2 \<rbrakk> \<Longrightarrow> sol_sat2 p_sub (cl1 @ cl2)"    
  apply (induct cl1)
   apply (auto)
  done
  
lemma sol_sat_rev1: "\<lbrakk>sol_sat2 p_sub (cl1 @ cl2) \<rbrakk> \<Longrightarrow> sol_sat2 p_sub cl1"    
  apply (induct cl1)
   apply (auto)
  done
    
lemma sol_sat_rev2: "\<lbrakk>sol_sat2 p_sub (cl1 @ cl2) \<rbrakk> \<Longrightarrow> sol_sat2 p_sub cl2"    
  apply (induct cl1)
   apply (auto)
  done    
    
lemma eval_sol_subst_perm: "\<lbrakk> spec_perm_env p_sub p_subx \<rbrakk> \<Longrightarrow>
  eval_perm p_subx (perm_subst_perm p_sub p) = sol_subst_perm p_subx p"    
  apply (case_tac p)
   apply (auto)
  apply (case_tac "p_sub x2")
   apply (auto)
  apply (simp add: spec_perm_env_def)
  apply (erule_tac x="x2" in allE)
  apply (auto)
  apply (case_tac a)
   apply (auto)
  done
    
lemma eval_sol_subst_aff: "\<lbrakk> spec_perm_env p_sub p_subx \<rbrakk> \<Longrightarrow>
  leq_perm (eval_perm p_subx (perm_subst_aff p_sub a)) (as_perm (sol_subst_aff p_subx a))"    
  apply (case_tac a)
   apply (auto)
   apply (case_tac "as_perm x1")
     apply (auto)
  apply (case_tac "p_sub x2")
   apply (auto)
   apply (case_tac "p_subx x2")
     apply (auto)
  apply (simp add: spec_perm_env_def)
  apply (erule_tac x="x2" in allE)
  apply (auto)
  apply (case_tac aa)
   apply (auto)
   apply (case_tac "p_subx x2")
     apply (auto)
  apply (case_tac "p_subx x2a")
    apply (auto)
  done
    
lemma eval_req_leq_perm: "\<lbrakk> t_sub x = Some tau_v; t_subx x = Some tau; spec_perm_env p_sub p_subx;
  equiv_sub (perm_compose p_subx (subst_compose t_sub t_sub')) (perm_compose p_subx (indir_sub t_subx)) \<rbrakk> \<Longrightarrow>
  leq_perm (eval_perm p_subx (def_req_type p_sub tau_v)) (as_perm (req_type tau))"
  apply (simp add: equiv_sub_def)
  apply (erule_tac x="x" in allE)
  apply (simp add: perm_compose_def)
  apply (simp add: subst_compose_def)
  apply (simp add: indir_sub_def)
  apply (case_tac tau_v)
    apply (auto)
     apply (case_tac tau)
           apply (auto)
    apply (case_tac tau)
          apply (auto)
    apply (rule_tac t="as_perm (as_aff (sol_subst_perm p_subx x63))" and s="sol_subst_perm p_subx x63" in subst)
     apply (case_tac "sol_subst_perm p_subx x63")
       apply (auto)
    apply (simp add: eval_sol_subst_perm)
    apply (case_tac "sol_subst_perm p_subx x63")
      apply (auto)
   apply (case_tac tau)
         apply (auto)
   apply (simp add: eval_sol_subst_aff)
  apply (case_tac tau)
        apply (auto)
  done
    
lemma eval_req_leq_perm2: "\<lbrakk> spec_perm_env p_sub p_subx; dir_subst_type t_subx p_subx tau_v tau;
  equiv_sub (perm_compose p_subx (subst_compose t_sub t_sub')) (perm_compose p_subx (indir_sub t_subx)) \<rbrakk> \<Longrightarrow>
  leq_perm (eval_perm p_subx (subst_req_type t_sub p_sub tau_v)) (as_perm (req_type tau))"
  apply (case_tac "\<exists> a. tau_v = VarScheme a")
    apply (auto)
   apply (case_tac "t_sub a")
    apply (auto)
   apply (rule_tac eval_req_leq_perm)
      apply (auto)
  apply (case_tac tau_v)
         apply (auto)
   apply (rule_tac t="as_perm (as_aff (sol_subst_perm p_subx x63))" and s="sol_subst_perm p_subx x63" in subst)
    apply (case_tac "sol_subst_perm p_subx x63")
      apply (auto)
   apply (simp add: eval_sol_subst_perm)
   apply (case_tac "sol_subst_perm p_subx x63")
     apply (auto)
  apply (simp add: eval_sol_subst_aff)
  done
    
lemma eval_dir_leq_permx: "\<lbrakk> equiv_sub (perm_compose p_subx (subst_compose t_sub t_sub')) (perm_compose p_subx (indir_sub t_subx));
  spec_perm_env p_sub p_subx \<rbrakk> \<Longrightarrow>
  leq_perm (eval_permx p_subx (full_subst_permx t_sub p_sub px)) (dir_subst_permx t_subx p_subx px)"    
  apply (induct px)
      apply (auto)
    (* perm case *)
       apply (simp add: eval_sol_subst_perm)
       apply (case_tac "sol_subst_perm p_subx x")
         apply (auto)
    (* type case. first we check if t_sub x \<noteq> None, while t_subx x = None*)
      apply (case_tac "t_sub x")
       apply (auto)
      apply (case_tac "t_subx x")
       apply (auto)
    (* - for this to happen, a must be a variable, meaning def_req_type will give None *)
       apply (simp add: equiv_sub_def)
       apply (erule_tac x="x" in allE)
       apply (case_tac "perm_compose p_subx (indir_sub t_subx) x \<noteq> None")
        apply (simp add: perm_compose_def)
        apply (simp add: indir_sub_def)
       apply (auto)
       apply (case_tac "\<not> (\<exists> a'. t_sub x = Some (VarScheme a')) ")
        apply (auto)
       apply (simp add: perm_compose_def)
       apply (simp add: subst_compose_def)
       apply (simp add: indir_sub_def)
       apply (case_tac a)
              apply (auto)
    (* - otherwise, both of them have a known type. *)
      apply (rule_tac eval_req_leq_perm)
         apply (auto)
    (* comp case *)
     apply (rule_tac dist_union_leq_perm)
      apply (rule_tac union_leq_perm1)
      apply (simp)
     apply (rule_tac union_leq_perm2)
     apply (simp)
    (* lift case *)
    apply (simp add: eval_sol_subst_perm)
    (* if zero case 1 *)
   apply (case_tac "eval_permx p_subx (full_subst_permx t_sub p_sub px)")
     apply (auto)
    (* if zero case 2 *)
  apply (case_tac "eval_permx p_subx (full_subst_permx t_sub p_sub px1)")
    apply (auto)
  done
    
lemma reduce_dir_sol_crn2: "\<lbrakk> dir_sol_crn t_subx p_subx c;
  equiv_sub (perm_compose p_subx (subst_compose t_sub t_sub')) (perm_compose p_subx (indir_sub t_subx));
  spec_perm_env p_sub p_subx \<rbrakk>  \<Longrightarrow> sol_sat2 p_subx (reduce_subst_crn t_sub p_sub c)"    
  apply (case_tac c)
       apply (auto)
    (* leq case *)
             apply (rule_tac q="dir_subst_permx t_subx p_subx x21" in trans_leq_perm)
              apply (rule_tac eval_dir_leq_permx)
               apply (auto)
             apply (simp add: eval_sol_subst_perm)
    (* leq_type case *)
            apply (rule_tac q="as_perm (req_type tau_x)" in trans_leq_perm)
             apply (rule_tac eval_req_leq_perm2)
               apply (auto)
            apply (simp add: eval_sol_subst_perm)
            apply (case_tac "req_type tau_x")
              apply (auto)
             apply (case_tac "sol_subst_perm p_subx x32")
               apply (auto)
            apply (case_tac "sol_subst_perm p_subx x32")
              apply (auto)
    (* disj crn. first half *)
           apply (cut_tac px="x41" in eval_dir_leq_permx)
             apply (auto)
           apply (case_tac "dir_subst_permx t_subx p_subx x41")
             apply (auto)
          apply (cut_tac px="x42" in eval_dir_leq_permx)
            apply (auto)
          apply (case_tac "dir_subst_permx t_subx p_subx x42")
            apply (auto)
         apply (cut_tac px="x41" in eval_dir_leq_permx)
           apply (auto)
        apply (cut_tac px="x41" in eval_dir_leq_permx)
          apply (auto)
        apply (case_tac "eval_permx p_subx (full_subst_permx t_sub p_sub x41)")
          apply (auto)
    (* disj crn. second half *)
       apply (cut_tac px="x42" in eval_dir_leq_permx)
         apply (auto)
       apply (case_tac "eval_permx p_subx (full_subst_permx t_sub p_sub x42)")
         apply (auto)
      apply (cut_tac px="x42" in eval_dir_leq_permx)
        apply (auto)
     apply (cut_tac px="x41" in eval_dir_leq_permx)
       apply (auto)
    apply (cut_tac px="x41" in eval_dir_leq_permx)
      apply (auto)
    apply (case_tac "eval_permx p_subx (full_subst_permx t_sub p_sub x41)")
      apply (auto)
    (* mini disj crn. *)
   apply (cut_tac px="x51" in eval_dir_leq_permx)
     apply (auto)
   apply (case_tac "dir_subst_permx t_subx p_subx x51")
     apply (auto)
  apply (cut_tac px="x52" in eval_dir_leq_permx)
    apply (auto)
  apply (case_tac "eval_permx p_subx (full_subst_permx t_sub p_sub x52)")
    apply (auto)
  done
    
lemma reduce_dir_sol_sat2: "\<lbrakk> dir_sol_sat t_subx p_subx c_list;
  equiv_sub (perm_compose p_subx (subst_compose t_sub t_sub')) (perm_compose p_subx (indir_sub t_subx));
  spec_perm_env p_sub p_subx \<rbrakk> \<Longrightarrow> sol_sat2 p_subx (reduce_subst_list t_sub p_sub c_list)"    
  apply (induct c_list)
   apply (auto)
  apply (rule_tac sol_sat_append_split)
   apply (auto)
  apply (rule_tac reduce_dir_sol_crn2)
    apply (auto)
  done

lemma reduce_crn_list_sat: "\<lbrakk> reduce_crn_list c_list = Some c_listx; dir_sol_sat t_sub p_sub c_list (*; no_mv_crn c_list*) \<rbrakk> \<Longrightarrow> sol_sat2 p_sub c_listx"  
  apply (simp add: reduce_crn_list_def)
  apply (case_tac "unify_type (unify_subset c_list)")
   apply (auto)
  apply (cut_tac t_sub="t_sub" and p_sub="p_sub" and c_list="c_list" in dir_sol_type_eq_sat)
   apply (auto)
  apply (cut_tac t_sub="a" and t_subx="indir_sub t_sub" and c_list="unify_subset c_list" and p_eq="b" and p_sub="p_sub" in unify_type_sat)
    apply (auto)
  apply (simp add: uts_res_def)
  apply (case_tac "unify_perm b")
   apply (auto)
  apply (cut_tac p_list="b" and p_sub="aa" and p_subx="p_sub" in unify_perm_gen)
    apply (auto)
  apply (rule_tac reduce_dir_sol_sat2)
    apply (auto)
  done

definition wf_psub where
  "wf_psub p_sub = (\<forall> x. case p_sub x of
    None \<Rightarrow> True
    | Some p \<Rightarrow> (\<forall> y. case p_sub y of
      None \<Rightarrow> True
      | Some q \<Rightarrow> x \<notin> pvar_set_perm q
    )
  )"       
    
definition def_perm_env where
  "def_perm_env p_sub = (\<lambda> x. case p_sub x of
    None \<Rightarrow> NoPerm
    | Some p \<Rightarrow> (case p of
      SPerm p \<Rightarrow> p
      | SVar r \<Rightarrow> NoPerm
    )
  )"
  
lemma def_spec_perm_env: "\<lbrakk> wf_psub p_sub \<rbrakk> \<Longrightarrow> spec_perm_env p_sub (def_perm_env p_sub)"   
  apply (simp add: spec_perm_env_def)
  apply (auto)
  apply (case_tac "p_sub x")
   apply (auto)
  apply (case_tac a)
   apply (auto)
   apply (simp add: def_perm_env_def)
  apply (simp add: def_perm_env_def)
  apply (case_tac "p_sub x2")
   apply (auto)
  apply (simp add: wf_psub_def)
  apply (erule_tac x="x2" in allE)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done
    
lemma unify_perm_wf_psub: "\<lbrakk> unify_perm p_list = Some p_sub \<rbrakk> \<Longrightarrow> wf_psub p_sub"    
  apply (induct arbitrary: p_sub rule: wf_induct [where r=p_unify_rel])
   apply (simp add: p_unify_rel_def)
  apply (case_tac x)
   apply (auto)
   apply (simp add: wf_psub_def)
   apply (simp add: empty_env_def)
    (* var case *)
  apply (case_tac "\<exists> r. a = SVar r")
   apply (auto)
    (* - delete case *)
   apply (case_tac "b = SVar r")
    apply (auto)
    apply (erule_tac x="list" in allE)
    apply (simp add: simp_p_unify_rel)
    (* - elim case *)
   apply (case_tac "unify_perm (perm_subst_eq_list (add_env empty_env r b) list)")
    apply (auto)
   apply (erule_tac x="perm_subst_eq_list (add_env empty_env r b) list" in allE)
   apply (auto)
    apply (simp add: elim_p_unify_rel)
   apply (simp add: wf_psub_def)
   apply (auto)
    (* > prelim: r is not present in the range of a *)
   apply (cut_tac p_sub="a" and p_list="perm_subst_eq_list (add_env empty_env r b) list" and x="r" in unify_perm_pvar_range)
     apply (auto)
    apply (cut_tac r="r" and p="b" and p_list="list" in perm_subst_pvar_eq_set)
     apply (auto)
    (* x = r, r = y. checks that r won't show up in b after applying a. *)
   apply (case_tac "x = r")
    apply (simp add: add_env_def)
    apply (auto)
     apply (case_tac b)
      apply (auto)
     apply (simp add: perm_sub_range_def)
     apply (erule_tac x="x2" in allE)
     apply (erule_tac x="x2" in allE)
     apply (case_tac "a x2")
      apply (auto)
    (* x = r, r \<noteq> y. checks that r won't show up anywhere else *)
    apply (case_tac "a y")
     apply (auto)
    apply (simp add: perm_sub_range_def)
    apply (erule_tac x="y" in allE)
    apply (erule_tac x="y" in allE)
    apply (auto)
    (* x \<noteq> r, y = r. checks that any other x won't show up in a b. this is true because say that b was some variable b'.
        since b' appears on the right-hand side, a b' = None. this means substitution yields nothing *)
   apply (simp add: add_env_def)
   apply (case_tac "a x")
    apply (auto)
   apply (simp add: add_env_def)
   apply (auto)
    apply (case_tac b)
     apply (auto)
    apply (case_tac "a x2")
     apply (auto)
    apply (erule_tac x="x" in allE)
    apply (auto)
    apply (erule_tac x="x2" in allE)
    apply (auto)
    (* x \<noteq> r, y \<noteq> r *)
   apply (erule_tac x="x" in allE)
   apply (auto)
    (* orient case *)
  apply (case_tac "\<exists> r. b = SVar r")
   apply (auto)
   apply (erule_tac x="(SVar r, a) # list" in allE)
   apply (simp add: orient_p_unify_rel)
   apply (case_tac a)
    apply (auto)
    (* decomp case *)
  apply (case_tac a)
   apply (auto)
  apply (case_tac b)
   apply (auto)
  apply (erule_tac x="list" in allE)
  apply (simp add: simp_p_unify_rel)
  apply (case_tac "x1 = x1a")
   apply (auto)
  done          
    
definition tsub_complete where
  "tsub_complete t_sub p_sub tau_n = (\<lambda> x. case t_sub x of
    None \<Rightarrow> Some tau_n
    | Some tau_v \<Rightarrow> Some (full_subst_type empty_env p_sub tau_n tau_v)
  )"
    
definition psub_compose where
  "psub_compose p_sub p_subx = (\<lambda> x. case p_sub x of
    None \<Rightarrow> p_subx x
    | Some p \<Rightarrow> (case p of
      SPerm p' \<Rightarrow> p'
      | SVar r \<Rightarrow> p_subx r
    )
  )"    
    
lemma complete_full_dir_subst_type: "dir_subst_type (tsub_complete t_sub p_sub tau_n) p_sub tau
  (full_subst_type (tsub_complete t_sub p_sub tau_n) p_sub tau_n tau)"
  apply (simp add: full_subst_type_def)
  apply (induct tau)
         apply (auto)
  apply (simp add: tsub_complete_def)
  apply (case_tac "t_sub x")
   apply (auto)
  done
  
lemma psub_compose_full_subst_type: "full_subst_type_f empty_env p_sub tau_n tau =
  full_subst_type_f empty_env empty_use_env tau_n (perm_subst_type p_sub tau)"    
  apply (induct tau)
         apply (auto)
  done

lemma reduce_full_subst_type: "
  full_subst_type (tsub_complete t_sub p_sub tau_n) p_sub tau_n tau =
  full_subst_type empty_env empty_use_env tau_n (perm_subst_type p_sub (sol_subst_type t_sub tau))"
  apply (simp add: full_subst_type_def)    
  apply (induct tau)
         apply (auto)
    (* var case *)
  apply (simp add: tsub_complete_def)
  apply (case_tac "t_sub x")
   apply (auto)
   apply (simp add: empty_env_def)
  apply (simp add: full_subst_type_def)
  apply (rule_tac psub_compose_full_subst_type)
  done
  

lemma psub_compose_spec_perm_env: "\<lbrakk> wf_psub p_sub \<rbrakk> \<Longrightarrow> spec_perm_env p_sub (psub_compose p_sub p_subx)"
  apply (simp add: spec_perm_env_def)
  apply (auto)
  apply (case_tac "p_sub x")
   apply (auto)
  apply (case_tac a)
   apply (auto)
   apply (simp add: psub_compose_def)
    (* say that p_sub contains a var. we want to show that after composition, they go to the same place. *)
  apply (simp add: psub_compose_def)
  apply (case_tac "p_sub x2")
   apply (auto)
    (* p_sub x2 cannot go anywhere, since this breaks well-formedness *)
  apply (simp add: wf_psub_def)
  apply (erule_tac x="x2" in allE)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done   
  
lemma compose_sol_eval_perm: "sol_subst_perm (psub_compose p_sub p_subx) p = eval_perm p_subx (perm_subst_perm p_sub p)"    
  apply (case_tac p)
   apply (auto)
  apply (simp add: psub_compose_def)
  apply (case_tac "p_sub x2")
   apply (auto)
  apply (case_tac a)
   apply (auto)
  done
 
lemma compose_aff_eval_perm: "leq_perm (as_perm (sol_subst_aff (psub_compose p_sub p_subx) a)) (eval_perm p_subx (perm_subst_aff p_sub a))" 
  apply (case_tac a)
   apply (auto)
   apply (case_tac x1)
     apply (auto)
  apply (simp add: psub_compose_def)
  apply (case_tac "p_sub x2")
   apply (auto)
   apply (case_tac "p_subx x2")
     apply (auto)
  apply (case_tac aa)
   apply (auto)
   apply (case_tac x1)
     apply (auto)
  apply (case_tac "p_subx x2a")
    apply (auto)    
  done
    
lemma complete_dir_eval_permx: "leq_perm (dir_subst_permx (tsub_complete t_sub (psub_compose p_sub p_subx) IntTy) (psub_compose p_sub p_subx) px)
   (eval_permx p_subx (full_subst_permx t_sub p_sub px))"    
  apply (induct px)
      apply (auto)
    (* perm case *)
       apply (simp add: compose_sol_eval_perm)
       apply (case_tac "eval_perm p_subx (perm_subst_perm p_sub x)")
         apply (auto)
    (* type case *)
      apply (simp add: tsub_complete_def)
      apply (case_tac "t_sub x")
       apply (auto)
      apply (simp add: full_subst_type_def)
      apply (case_tac a)
             apply (auto)
        apply (simp add: empty_env_def)
       apply (rule_tac t="as_perm (as_aff (sol_subst_perm (psub_compose p_sub p_subx) x63))" and
          s="sol_subst_perm (psub_compose p_sub p_subx) x63" in subst)
        apply (case_tac "sol_subst_perm (psub_compose p_sub p_subx) x63")
          apply (auto)
       apply (simp add: compose_sol_eval_perm)
       apply (case_tac "eval_perm p_subx (perm_subst_perm p_sub x63)")
         apply (auto)
      apply (rule_tac compose_aff_eval_perm)
    (* comp case *)
     apply (rule_tac dist_union_leq_perm)
      apply (rule_tac union_leq_perm1)
      apply (simp)
     apply (rule_tac union_leq_perm2)
     apply (simp)
    (* lift case *)
    apply (cut_tac p_sub="p_sub" and p_subx="p_subx" and p="x2a" in compose_sol_eval_perm)
    apply (auto)
    (* if zero case *)
   apply (case_tac "dir_subst_permx (tsub_complete t_sub (psub_compose p_sub p_subx) IntTy) (psub_compose p_sub p_subx) px")
     apply (auto)
  apply (case_tac "dir_subst_permx (tsub_complete t_sub (psub_compose p_sub p_subx) IntTy) (psub_compose p_sub p_subx) px1")
    apply (auto)
  done
    

lemma aff_leq_perm: "\<lbrakk> leq_perm (as_perm a) p \<rbrakk> \<Longrightarrow> aff_leq a p"    
  apply (case_tac "a")
    apply (auto)
   apply (case_tac p)
     apply (auto)
  apply (case_tac p)
    apply (auto)
  done    
    
lemma full_subst_aff_leq: "\<lbrakk> leq_perm (eval_perm p_subx (def_req_type p_sub tau_v)) p;
                full_subst_type_f empty_env (psub_compose p_sub p_subx) IntTy tau_v = tau \<rbrakk>
               \<Longrightarrow> aff_leq (req_type tau) p"    
  apply (rule_tac aff_leq_perm)
  apply (auto)
  apply (case_tac tau_v)
         apply (auto)
    apply (simp add: empty_env_def)
   apply (simp add: compose_sol_eval_perm)
   apply (case_tac "eval_perm p_subx (perm_subst_perm p_sub x63)")
     apply (auto)
  apply (rule_tac q="eval_perm p_subx (perm_subst_aff p_sub x74)" in trans_leq_perm)
   apply (rule_tac compose_aff_eval_perm)
  apply (simp)
  done
    
    
lemma complete_eval_aff_leq: "\<lbrakk> leq_perm (eval_perm p_subx (subst_req_type t_sub p_sub tau)) (eval_perm p_subx (perm_subst_perm p_sub p)) \<rbrakk>
   \<Longrightarrow> aff_leq (req_type (full_subst_type (tsub_complete t_sub (psub_compose p_sub p_subx) IntTy) (psub_compose p_sub p_subx) IntTy tau))
           (sol_subst_perm (psub_compose p_sub p_subx) p)"    
  apply (simp add: full_subst_type_def)
  apply (case_tac tau)
         apply (auto)
    (* var case *)
      apply (case_tac "tsub_complete t_sub (psub_compose p_sub p_subx) IntTy x4")
       apply (auto)
      apply (case_tac "t_sub x4")
       apply (auto)
       apply (simp add: tsub_complete_def)
      apply (simp add: tsub_complete_def)
      apply (simp add: compose_sol_eval_perm)
      apply (simp add: full_subst_type_def)
      apply (rule_tac full_subst_aff_leq)
       apply (auto)
    (* array case *)
     apply (simp add: compose_sol_eval_perm)
     apply (rule_tac aff_leq_perm)
     apply (auto)
    (* pair case *)
    apply (simp add: compose_sol_eval_perm)
    apply (rule_tac aff_leq_perm)
    apply (case_tac "eval_perm p_subx (perm_subst_perm p_sub x63)")
      apply (auto)
    (* fun case *)
   apply (simp add: compose_sol_eval_perm)
   apply (rule_tac aff_leq_perm)
   apply (rule_tac q="eval_perm p_subx (perm_subst_aff p_sub x74)" in trans_leq_perm)
    apply (rule_tac compose_aff_eval_perm)
   apply (simp)
    (* chan case *)
  apply (simp add: compose_sol_eval_perm)
  apply (rule_tac aff_leq_perm)
  apply (auto)
  done
    
lemma reduce_subst_crn_corr: "\<lbrakk> sol_sat2 p_subx (reduce_subst_crn t_sub p_sub c);
  \<forall> t1 t2. c \<noteq> UnifyCrn t1 t2 (*\<and> c \<noteq> MemValCrn t1 t2*); wf_psub p_sub \<rbrakk> \<Longrightarrow>
  dir_sol_crn (tsub_complete t_sub (psub_compose p_sub p_subx) IntTy) (psub_compose p_sub p_subx) c"
  apply (cut_tac p_sub="p_sub" and p_subx="p_subx" in psub_compose_spec_perm_env)
   apply (auto)
  apply (case_tac c)
       apply (auto)
    (* ordering constraint *)
             apply (rule_tac q="eval_permx p_subx (full_subst_permx t_sub p_sub x21)" in trans_leq_perm)
              apply (rule_tac complete_dir_eval_permx)
             apply (simp add: compose_sol_eval_perm)
    (* type order constraint *)
            apply (rule_tac x="full_subst_type (tsub_complete t_sub (psub_compose p_sub p_subx) IntTy) (psub_compose p_sub p_subx) IntTy x31" in exI)
            apply (auto)
             apply (rule_tac complete_full_dir_subst_type)
            apply (rule_tac complete_eval_aff_leq)
            apply (simp)
    (* disjointness first half *)
           apply (cut_tac t_sub="t_sub" and p_sub="p_sub" and p_subx="p_subx" and px="x41" in complete_dir_eval_permx)
           apply (auto)
           apply (case_tac "eval_permx p_subx (full_subst_permx t_sub p_sub x41)")
             apply (auto)
          apply (cut_tac t_sub="t_sub" and p_sub="p_sub" and p_subx="p_subx" and px="x42" in complete_dir_eval_permx)
          apply (auto)
          apply (case_tac "eval_permx p_subx (full_subst_permx t_sub p_sub x42)")
            apply (auto)
         apply (cut_tac t_sub="t_sub" and p_sub="p_sub" and p_subx="p_subx" and px="x41" in complete_dir_eval_permx)
         apply (auto)
        apply (cut_tac t_sub="t_sub" and p_sub="p_sub" and p_subx="p_subx" and px="x41" in complete_dir_eval_permx)
        apply (auto)
        apply (case_tac "dir_subst_permx (tsub_complete t_sub (psub_compose p_sub p_subx) IntTy) (psub_compose p_sub p_subx) x41")
          apply (auto)
    (* disjointness second half *)
       apply (cut_tac t_sub="t_sub" and p_sub="p_sub" and p_subx="p_subx" and px="x42" in complete_dir_eval_permx)
       apply (auto)
       apply (case_tac "dir_subst_permx (tsub_complete t_sub (psub_compose p_sub p_subx) IntTy) (psub_compose p_sub p_subx) x42")
         apply (auto)
      apply (cut_tac t_sub="t_sub" and p_sub="p_sub" and p_subx="p_subx" and px="x42" in complete_dir_eval_permx)
      apply (auto)
     apply (cut_tac t_sub="t_sub" and p_sub="p_sub" and p_subx="p_subx" and px="x41" in complete_dir_eval_permx)
     apply (auto)
    apply (cut_tac t_sub="t_sub" and p_sub="p_sub" and p_subx="p_subx" and px="x41" in complete_dir_eval_permx)
    apply (auto)
    apply (case_tac "dir_subst_permx (tsub_complete t_sub (psub_compose p_sub p_subx) IntTy) (psub_compose p_sub p_subx) x41")
      apply (auto)
    (* semi-disjointness *)
   apply (cut_tac t_sub="t_sub" and p_sub="p_sub" and p_subx="p_subx" and px="x51" in complete_dir_eval_permx)
   apply (auto)
   apply (case_tac "eval_permx p_subx (full_subst_permx t_sub p_sub x51)")
     apply (auto)
  apply (cut_tac t_sub="t_sub" and p_sub="p_sub" and p_subx="p_subx" and px="x52" in complete_dir_eval_permx)
  apply (auto)
  apply (case_tac "dir_subst_permx (tsub_complete t_sub (psub_compose p_sub p_subx) IntTy) (psub_compose p_sub p_subx) x52")
    apply (auto)
  done
    
lemma reduce_subst_list_corr: "\<lbrakk> sol_sat2 p_subx (reduce_subst_list t_sub p_sub c_list); (*no_mv_crn c_list;*)
  type_eq_sat t_sub (psub_compose p_sub p_subx) (unify_subset c_list); wf_psub p_sub \<rbrakk> \<Longrightarrow>
  dir_sol_sat (tsub_complete t_sub (psub_compose p_sub p_subx) IntTy) (psub_compose p_sub p_subx) c_list"    
  apply (induct c_list)
   apply (auto)
   apply (simp add: type_eq_sat_def)
    (* unification case *)
   apply (case_tac "\<exists> t1 t2. a = UnifyCrn t1 t2")
    apply (auto)
    apply (rule_tac x="full_subst_type (tsub_complete t_sub (psub_compose p_sub p_subx) IntTy) (psub_compose p_sub p_subx) IntTy t1" in exI)
    apply (auto)
     apply (rule_tac complete_full_dir_subst_type)
    apply (rule_tac t="full_subst_type (tsub_complete t_sub (psub_compose p_sub p_subx) IntTy) (psub_compose p_sub p_subx) IntTy t1"
      and s="full_subst_type (tsub_complete t_sub (psub_compose p_sub p_subx) IntTy) (psub_compose p_sub p_subx) IntTy t2" in subst)
     apply (simp add: reduce_full_subst_type)
    apply (rule_tac complete_full_dir_subst_type)
    (* misc constraints *)
   apply (rule_tac reduce_subst_crn_corr)
     apply (rule_tac sol_sat_rev1)
     apply (auto)
    (* induction *)
  apply (cut_tac p_sub="p_subx" and ?cl2.0="reduce_subst_list t_sub p_sub c_list" in sol_sat_rev2)
   apply (auto)(*
  apply (case_tac "\<not> no_mv_crn c_list")
   apply (auto)
   apply (case_tac a)
        apply (auto)*)
  apply (case_tac "\<not> type_eq_sat t_sub (psub_compose p_sub p_subx) (unify_subset c_list)")
   apply (case_tac a)
        apply (auto)
  apply (simp add: type_eq_sat_def)
  done
    
    (* in this lemma we state that if a constratint list is successfully reduced,
      and the reduced list can be solved, then the original constraint list also has a solution.
    *)
lemma reduce_crn_list_satx: "\<lbrakk> reduce_crn_list c_list = Some c_listx; sol_sat2 p_sub c_listx(*; no_mv_crn c_list *)\<rbrakk> \<Longrightarrow>
  (\<exists> t_subx p_subx. dir_sol_sat t_subx p_subx c_list)"  
  apply (simp add: reduce_crn_list_def)
  apply (case_tac "unify_type (unify_subset c_list)")
   apply (auto)
  apply (case_tac "unify_perm b")
   apply (auto)
    (* permission unification returns a valid permission substitution *)
  apply (cut_tac p_subx="psub_compose aa p_sub" and p_list="b" and p_sub="aa" in unify_perm_sat)
    apply (simp)
   apply (rule_tac psub_compose_spec_perm_env)
   apply (rule_tac unify_perm_wf_psub)
   apply (auto)
    (* this means type unification can be used to construct a valid solution to the unification subset *)
  apply (cut_tac c_list="unify_subset c_list" and t_sub="a" and p_eq="b" in unify_type_satx)
    apply (auto)
    (* our overall claim is that we can solve using the main type substitution + a composition of p_sub with p_eq's solution *)
  apply (rule_tac x="tsub_complete a (psub_compose aa p_sub) IntTy" in exI)
  apply (rule_tac x="psub_compose aa p_sub" in exI)
  apply (rule_tac reduce_subst_list_corr)
     apply (auto)
  apply (rule_tac unify_perm_wf_psub)
  apply (auto)
  done
    
end