theory InferComplete
  imports InferRange AltLBoundLemma
begin

    (* ##### defines specialization properties *)
  
definition spec_env :: "nat res_env \<Rightarrow> pt_env \<Rightarrow> dir_type_subst \<Rightarrow> bool" where
  "spec_env env_v env t_subx = (\<forall> x. case env_v x of
    None \<Rightarrow> env x = None
    | Some a \<Rightarrow> env x = t_subx a
  )"    
  
lemma self_spec_env: "spec_env env_v (dir_subst_tenv t_sub env_v) t_sub"  
  apply (simp add: spec_env_def)
  apply (auto)
  apply (case_tac "env_v x")
   apply (auto)
   apply (simp add: dir_subst_tenv_def)
  apply (simp add: dir_subst_tenv_def)
  done
  
lemma eq_spec_env: "\<lbrakk> dir_subst_tenv t_sub env_v = dir_subst_tenv t_sub' env_v \<rbrakk> \<Longrightarrow> spec_env env_v (dir_subst_tenv t_sub env_v) t_sub'"  
  apply (simp)
  apply (rule_tac self_spec_env)
  done    
    
    (* #### fresh list lemmas *)

lemma dom_list_set_contain: "\<lbrakk> x \<in> dom_list_set l \<rbrakk> \<Longrightarrow> list_contain (dom_list l) x"    
  apply (induct l)
   apply (auto)
  done
    
lemma dom_list_set_use: "\<lbrakk> list_contain (dom_list l) x; dom_list_set l \<subseteq> ds\<rbrakk> \<Longrightarrow> x \<in> ds"    
  apply (induct l)
   apply (auto)
  done
  
lemma append_contain_dom_list: "\<lbrakk> list_contain (dom_list (l1 @ l2)) a \<rbrakk> \<Longrightarrow> list_contain (dom_list l1) a \<or> list_contain (dom_list l2) a"
  apply (auto)
  apply (induct l1)
   apply (auto)
  done

lemma append_fresh_in_list: "\<lbrakk> fresh_in_list (dom_list l1); \<forall>x. list_contain (dom_list l2) x \<longrightarrow> \<not> list_contain (dom_list l1) x;
  fresh_in_list (dom_list l2) \<rbrakk> \<Longrightarrow> fresh_in_list (dom_list (l1 @ l2))"
  apply (induct l1)
   apply (auto)
  apply (cut_tac a="a" and ?l1.0="l1" and ?l2.0="l2" in append_contain_dom_list)
   apply (auto)
  done
  
lemma append_fresh_list: "\<lbrakk> fresh_list ds (dom_list l1); tsub_dom (dir_list_add_env t_sub l1) ds';
  fresh_list ds' (dom_list l2); ds \<subseteq> ds' \<rbrakk> \<Longrightarrow> fresh_list ds (dom_list (l1 @ l2))"
  apply (simp add: fresh_list_def)
  apply (auto)
    (* first we prove that l1 @ l2 is fresh internally *)
   apply (rule_tac append_fresh_in_list)
     apply (auto)
   apply (erule_tac x="x" in allE)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (cut_tac l="l1" and ds="ds'" in list_add_dls)
    apply (auto)
   apply (cut_tac x="x" and ds="ds'" and l="l1" in dom_list_set_use)
     apply (auto)
    (* next we want to prove that if x is in l1 @ l2, x \<notin> ds *)
  apply (cut_tac ?l1.0="l1" and ?l2.0="l2" and a="x" in append_contain_dom_list)
   apply (auto)
  done    
    
lemma add_list_contain: "\<lbrakk> list_contain (dom_list l) x \<rbrakk> \<Longrightarrow> dir_list_add_env t_sub l x \<noteq> None"
  apply (induct l)
   apply (auto)
   apply (simp add: dir_add_env_def)
  apply (simp add: dir_add_env_def)
  done
    
lemma add_fresh_list: "\<lbrakk> fresh_list ds (dom_list l); tsub_dom (dir_list_add_env t_sub l) ds';
  x \<notin> ds'; ds \<subseteq> ds' \<rbrakk> \<Longrightarrow> fresh_list ds (dom_list ((x, t) # l))"    
  apply (simp add: fresh_list_def)
  apply (auto)
  apply (simp add: tsub_dom_def)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (cut_tac t_sub="t_sub" and l="l" and x="x" in add_list_contain)
   apply (auto)
  done
    
lemma append_fresh_list2: "\<lbrakk> fresh_list ds (dom_list l2); tsub_dom (dir_list_add_env t_sub l2) ds';
  fresh_list ds' (dom_list l1); ds \<subseteq> ds' \<rbrakk> \<Longrightarrow> fresh_list ds (dom_list (l1 @ l2))"
  apply (simp add: fresh_list_def)
  apply (auto)
    (* first we prove that l1 @ l2 is fresh internally *)
   apply (rule_tac append_fresh_in_list)
     apply (auto)
   apply (erule_tac x="x" in allE)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (cut_tac l="l2" and ds="ds'" in list_add_dls)
    apply (auto)
   apply (cut_tac x="x" and ds="ds'" and l="l2" in dom_list_set_use)
     apply (auto)
    (* next we want to prove that if x is in l1 @ l2, x \<notin> ds *)
  apply (cut_tac ?l1.0="l1" and ?l2.0="l2" and a="x" in append_contain_dom_list)
   apply (auto)
  done          
    
    (* #### unsorted lemmas *)
    
    
lemma add_subst_perm: "\<lbrakk> x \<notin> pvar_set_perm p \<rbrakk> \<Longrightarrow> sol_subst_perm (add_use_env p_sub x r) p = sol_subst_perm p_sub p"        
  apply (case_tac p)
    apply (auto)
  apply (simp add: add_use_env_def)
  done
  
lemma add_subst_permx: "\<lbrakk> x \<notin> pvar_set px \<rbrakk> \<Longrightarrow> dir_subst_permx t_sub (add_use_env p_sub x r) px = dir_subst_permx t_sub p_sub px"    
  apply (induct px)
     apply (auto)
      apply (simp_all add: add_subst_perm)
  done
    
lemma add_psub_leq_use_env: "\<lbrakk> pvar_range r_xv ds; x \<notin> ds; leq_use_env (dir_subst_penv t_sub p_sub r_xv) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (dir_subst_penv t_sub (add_use_env p_sub x r) r_xv) r_s"
  apply (simp add: leq_use_env_def)
  apply (simp add: dir_subst_penv_def)
  apply (auto)
  apply (rule_tac t="dir_subst_permx t_sub (add_use_env p_sub x r) (r_xv xa)"
      and s="dir_subst_permx t_sub p_sub (r_xv xa)" in subst)
   apply (case_tac "x \<notin> pvar_set (r_xv xa)")
    apply (simp add: add_subst_permx)
   apply (simp add: pvar_range_def)
   apply (erule_tac x="xa" in allE)
   apply (auto)
  done    
    
lemma add_psub_use_env: "\<lbrakk> pvar_range r_xv ds; x \<notin> ds \<rbrakk> \<Longrightarrow>
  dir_subst_penv t_sub (add_use_env p_sub x r) r_xv = dir_subst_penv t_sub p_sub r_xv"    
  apply (case_tac "\<forall> y. dir_subst_penv t_sub (add_use_env p_sub x r) r_xv y = dir_subst_penv t_sub p_sub r_xv y")  
   apply (auto)
  apply (simp add: dir_subst_penv_def)
  apply (cut_tac t_sub="t_sub" and p_sub="p_sub" and x="x" and px="r_xv y" and r="r" in add_subst_permx)
   apply (auto)
  apply (simp add: pvar_range_def)
  apply (erule_tac x="y" in allE)
  apply (auto)
  done
    
lemma comp_subst_perm: "\<lbrakk> psub_dom p_sub2 ds'; pvar_set_perm p \<subseteq> ds; ds \<inter> ds' = {} \<rbrakk> \<Longrightarrow>
  sol_subst_perm (comp_use_env p_sub1 p_sub2) p = sol_subst_perm p_sub1 p"
  apply (case_tac p)
    apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: psub_dom_def)
  apply (erule_tac x="x2" in allE)
  apply (auto)
  apply (case_tac "p_sub1 x2")
    apply (auto)
  done

lemma comp_subst_permx: "\<lbrakk> psub_dom p_sub2 ds'; pvar_set px \<subseteq> ds; ds \<inter> ds' = {} \<rbrakk> \<Longrightarrow>
  dir_subst_permx t_sub (comp_use_env p_sub1 p_sub2) px = dir_subst_permx t_sub p_sub1 px"    
  apply (induct px)
     apply (auto)
    apply (simp add: comp_subst_perm)
   apply (simp add: comp_subst_perm)
  apply (simp add: comp_subst_perm)
  done
    
lemma comp_psub_leq_use_env1: "\<lbrakk> psub_dom p_sub2 ds'; pvar_range r_xv ds; ds \<inter> ds' = {};
  leq_use_env (dir_subst_penv t_sub p_sub1 r_xv) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (dir_subst_penv t_sub (comp_use_env p_sub1 p_sub2) r_xv) r_s"
  apply (simp add: leq_use_env_def)
  apply (simp add: dir_subst_penv_def)
  apply (auto)
  apply (rule_tac t="dir_subst_permx t_sub (comp_use_env p_sub1 p_sub2) (r_xv x)"
      and s="dir_subst_permx t_sub p_sub1 (r_xv x)" in subst)
   apply (case_tac "pvar_set (r_xv x) \<subseteq> ds")
    apply (simp add: comp_subst_permx)
   apply (simp add: pvar_range_def)
  apply (auto)
  done

lemma comp_psub_use_env1: "\<lbrakk> psub_dom p_sub2 ds'; pvar_range r_xv ds; ds \<inter> ds' = {} \<rbrakk> \<Longrightarrow>
  dir_subst_penv t_sub (comp_use_env p_sub1 p_sub2) r_xv = dir_subst_penv t_sub p_sub1 r_xv"    
  apply (case_tac "\<forall> x. dir_subst_penv t_sub (comp_use_env p_sub1 p_sub2) r_xv x = dir_subst_penv t_sub p_sub1 r_xv x")
   apply (auto)
  apply (simp add: dir_subst_penv_def)
  apply (cut_tac t_sub="t_sub" and ?p_sub1.0="p_sub1" and ?p_sub2.0="p_sub2" and ds="ds" and ds'="ds'" and px="r_xv x" in comp_subst_permx)
     apply (auto)
  apply (simp add: pvar_range_def)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done
    
lemma comp_psub_leq_use_env2: "\<lbrakk> psub_dom p_sub1 ds'; pvar_range r_xv ds; ds \<inter> ds' = {};
  leq_use_env (dir_subst_penv t_sub p_sub2 r_xv) r_s \<rbrakk> \<Longrightarrow>
  leq_use_env (dir_subst_penv t_sub (comp_use_env p_sub1 p_sub2) r_xv) r_s"
  apply (cut_tac r_s="p_sub1" and r_x="p_sub2" in comm_comp_use_env)
  apply (auto)
  apply (rule_tac comp_psub_leq_use_env1)
     apply (auto)
  done
   
lemma comp_psub_use_env2: "\<lbrakk> psub_dom p_sub2 ds'; pvar_range r_xv ds; ds \<inter> ds' = {} \<rbrakk> \<Longrightarrow>
  dir_subst_penv t_sub (comp_use_env p_sub2 p_sub1) r_xv = dir_subst_penv t_sub p_sub1 r_xv"        
  apply (simp add: comm_comp_use_env)
  apply (rule_tac comp_psub_use_env1)
    apply (auto)
  done
    
lemma diff_leq_use_env_rev: "\<lbrakk> leq_use_env (diff_use_env r_x r_ex) r_s; leq_use_env r_ex r_s \<rbrakk> \<Longrightarrow> leq_use_env r_x r_s"
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done
    
lemma dist_union_use_leq: "\<lbrakk> leq_perm p r; leq_perm q r \<rbrakk> \<Longrightarrow> leq_perm (union_perm p q) r"    
  apply (case_tac r)
    apply (auto)
   apply (case_tac p)
     apply (auto)
   apply (case_tac q)
     apply (auto)
  apply (case_tac p)
    apply (auto)
   apply (case_tac q)
     apply (auto)
  apply (case_tac q)
    apply (auto)
  done
  
lemma union_use_leq1: "\<lbrakk> leq_perm p q \<rbrakk> \<Longrightarrow> leq_perm p (union_perm q r)"    
  apply (case_tac q)
    apply (auto)
   apply (case_tac r)
     apply (auto)
   apply (case_tac p)
     apply (auto)
  apply (case_tac r)
    apply (auto)
  done

lemma union_use_leq2: "\<lbrakk> leq_perm p r \<rbrakk> \<Longrightarrow> leq_perm p (union_perm q r)"    
  apply (case_tac r)
    apply (auto)
    apply (case_tac q)
      apply (auto)
    apply (case_tac p)
      apply (auto)
   apply (case_tac q)
     apply (auto)
  apply (case_tac q)
    apply (auto)
  done
    
lemma dir_add_leq_permx: "\<lbrakk> t_sub x = None \<rbrakk> \<Longrightarrow> leq_perm (dir_subst_permx t_sub p_sub r) (dir_subst_permx (dir_add_env t_sub x tau) p_sub r)"    
  apply (induct r)
      apply (auto)
      apply (case_tac "sol_subst_perm p_sub xa")
        apply (auto)
     apply (simp add: dir_add_env_def)
     apply (auto)
     apply (case_tac "t_sub xa")
      apply (auto)
     apply (case_tac "as_perm (req_type a)")
       apply (auto)
    apply (rule_tac dist_union_use_leq)
     apply (rule_tac union_use_leq1)
     apply (auto)
    apply (rule_tac union_use_leq2)
    apply (auto)
   apply (case_tac "dir_subst_permx t_sub p_sub r")
     apply (auto)
  apply (case_tac "dir_subst_permx t_sub p_sub r1")
    apply (auto)
  done
  
lemma dir_add_leq_use_env: "\<lbrakk> tsub_dom t_sub ds; x \<notin> ds \<rbrakk> \<Longrightarrow> leq_use_env (dir_subst_penv t_sub p_sub r_sv) (dir_subst_penv (dir_add_env t_sub x tau) p_sub r_sv)"
  apply (simp add: leq_use_env_def)
  apply (simp add: dir_subst_penv_def)
  apply (auto)
  apply (simp add: tsub_dom_def)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (rule_tac dir_add_leq_permx)
  apply (simp)
  done
  
lemma dom_list_contain: "\<lbrakk> x \<in> dom_list_set l \<rbrakk> \<Longrightarrow> list_contain (dom_list l) x"    
  apply (induct l)
   apply (auto)
  done

lemma dom_list_contain_rev: "\<lbrakk> list_contain (dom_list l) x \<rbrakk> \<Longrightarrow> x \<in> dom_list_set l"    
  apply (induct l)
   apply (auto)
  done    
    
lemma dir_list_add_leq_use_env: "\<lbrakk> tsub_dom t_sub ds; fresh_list ds (dom_list l) \<rbrakk> \<Longrightarrow>
  leq_use_env (dir_subst_penv t_sub p_sub r_sv) (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv)"
  apply (induct l)
   apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac r_sb="dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv" in trans_leq_use_env)
   apply (rule_tac ds="ds \<union> (dom_list_set l)" in dir_add_leq_use_env)
    apply (rule_tac ds="ds" in list_add_tsub_dom)
      apply (auto)
    apply (simp add: fresh_list_def)
    apply (auto)
   apply (cut_tac x="a" and l="l" in dom_list_contain)
    apply (simp)
   apply (simp add: fresh_list_def)
  apply (simp add: fresh_list_def)
  done
   
lemma dir_list_append_eq_ih: "dir_list_add_env t_sub (l @ la) a = dir_list_add_env (dir_list_add_env t_sub la) l a"       
  apply (induct l)
   apply (auto)
  apply (simp add: dir_add_env_def)
  done
    
lemma dir_list_append_eq: "dir_list_add_env t_sub (l @ la) = dir_list_add_env (dir_list_add_env t_sub la) l"    
  apply (case_tac "\<forall> a. dir_list_add_env t_sub (l @ la) a = dir_list_add_env (dir_list_add_env t_sub la) l a")
   apply (auto)
  apply (simp add: dir_list_append_eq_ih)
  done
    
lemma ifz_sol_subst_penv: "\<lbrakk> p_sub p = NoPerm \<rbrakk> \<Longrightarrow> dir_subst_penv t_sub p_sub (ifz_var_env (XPerm (SVar p)) r_sv) = empty_use_env"    
  apply (case_tac "\<forall> x. dir_subst_penv t_sub p_sub (ifz_var_env (XPerm (SVar p)) r_sv) x = empty_use_env x")   
   apply (auto)
  apply (simp add: dir_subst_penv_def)
  apply (simp add: ifz_var_env_def)
  apply (simp add: empty_use_env_def)
  apply (case_tac "r_sv x = XPerm (SPerm NoPerm)")
   apply (auto)
  done        
    
    (* #### pvar / tvar lemmas *)
    
fun pvar_aff where
  "pvar_aff (AffConst a) = {}"
| "pvar_aff (AffVar v) = {v}"    
  
fun pvar_type where
  "pvar_type IntScheme = {}"
  | "pvar_type BoolScheme = {}"
  | "pvar_type UnitScheme = {}"
  | "pvar_type (VarScheme v) = {}" 
  | "pvar_type (ArrayScheme tau) = pvar_type tau"
  | "pvar_type (PairScheme t1 t2 p) = pvar_type t1 \<union> pvar_type t2 \<union> pvar_set_perm p"
  | "pvar_type (FunScheme t1 t2 p a) = pvar_type t1 \<union> pvar_type t2 \<union> pvar_set_perm p \<union> pvar_aff a"
  | "pvar_type (ChanScheme tau c_end) = pvar_type tau"   
    
lemma comp_subst_aff: "\<lbrakk> psub_dom p_subx ds; pvar_aff a \<inter> ds = {} \<rbrakk> \<Longrightarrow>
  sol_subst_aff p_sub a = sol_subst_aff (comp_use_env p_sub p_subx) a"    
  apply (case_tac a)
   apply (auto)
  apply (simp add: psub_dom_def)
  apply (simp add: comp_use_env_def)
  apply (erule_tac x="x2" in allE)
  apply (auto)
  apply (case_tac "p_sub x2")
    apply (auto)
  done
    
lemma comp_dir_subst_type1: "\<lbrakk> dir_subst_type t_sub p_sub tau_v tau;
  pvar_type tau_v \<subseteq> ds; psub_dom p_subx ds'; ds \<inter> ds' = {} \<rbrakk> \<Longrightarrow>
  dir_subst_type t_sub (comp_use_env p_sub p_subx) tau_v tau"    
  apply (induct tau_v arbitrary: tau)
         apply (auto)
    apply (simp add: comp_subst_perm)
   apply (simp add: comp_subst_perm)
  apply (rule_tac comp_subst_aff)
   apply (auto)
  done

lemma comp_dir_subst_type2: "\<lbrakk> dir_subst_type t_sub p_subx tau_v tau;
  pvar_type tau_v \<subseteq> ds; psub_dom p_sub ds'; ds \<inter> ds' = {} \<rbrakk> \<Longrightarrow>
  dir_subst_type t_sub (comp_use_env p_sub p_subx) tau_v tau"    
  apply (cut_tac r_s="p_sub" and r_x="p_subx" in comm_comp_use_env)
  apply (auto)
  apply (rule_tac comp_dir_subst_type1)
     apply (auto)
  done
    
lemma add_subst_aff: "\<lbrakk> p \<notin> pvar_aff a \<rbrakk> \<Longrightarrow>
  sol_subst_aff p_sub a = sol_subst_aff (add_use_env p_sub p r) a"    
  apply (case_tac a)
   apply (auto)
  apply (simp add: add_use_env_def)
  done
    
lemma add_dir_subst_type: "\<lbrakk> dir_subst_type t_sub p_sub tau_v tau; p \<notin> pvar_type tau_v \<rbrakk> \<Longrightarrow>
  dir_subst_type t_sub (add_use_env p_sub p r) tau_v tau"
  apply (induct tau_v arbitrary: tau)
         apply (auto)
    apply (simp add: add_subst_perm)
   apply (simp add: add_subst_perm)
  apply (rule_tac add_subst_aff)
  apply (auto)
  done
    
lemma dir_add_subst_permx: "\<lbrakk> x \<notin> tvar_set px \<rbrakk> \<Longrightarrow>
  dir_subst_permx (dir_add_env t_sub x tau) p_sub px = dir_subst_permx t_sub p_sub px"
  apply (induct px)
      apply (auto)
  apply (simp add: dir_add_env_def)
  done    
    
lemma dir_add_subst_type: "\<lbrakk> dir_subst_type t_sub p_sub tau_v tau; x \<notin> tvar_type tau_v \<rbrakk> \<Longrightarrow>
  dir_subst_type (dir_add_env t_sub x t) p_sub tau_v tau"
  apply (induct tau_v arbitrary: tau)
    apply (auto)
  apply (simp add: dir_add_env_def)
  done
    
lemma dir_list_add_subst_type: "\<lbrakk> dir_subst_type t_sub p_sub tau_v tau; tvar_type tau_v \<inter> dom_list_set l = {} \<rbrakk> \<Longrightarrow>
  dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau"
  apply (induct l arbitrary: tau_v tau)
   apply (auto)
  apply (rule_tac dir_add_subst_type)
    apply (auto)
  done
    
lemma infer_tvar_type: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; sub_range env_v ds \<rbrakk> \<Longrightarrow> tvar_type tau_v \<subseteq> ds'"    
  apply (induct e arbitrary: env_v ds tau_v r_sv r_xv r_mv c_list ds')
        apply (auto)
    (* const + op case *)
         apply (case_tac x)
                     apply (auto)
               apply (simp_all add: pure_fun_s_def)
        apply (case_tac x)
             apply (auto)
             apply (simp_all add: pure_fun_s_def)
    (* var case *)
       apply (simp add: sub_range_def)
       apply (erule_tac x="Var x'" in allE)
       apply (auto)
    (* pair case *)    
      apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
       apply (simp)
      apply (cut_tac c="x" and A="tvar_type t1" and B="ds2" in contra_subsetD)
        apply (auto)
     apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
       apply (simp)
      apply (rule_tac infer_x_subset)
      apply (auto)
     apply (cut_tac c="x" and A="tvar_type t2" and B="ds3" in contra_subsetD)
       apply (auto)
    (* if case *)
    apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
     apply (simp)
    apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
      apply (simp)
     apply (rule_tac infer_x_subset)
     apply (auto)
    apply (case_tac "x \<in> ds'")
     apply (auto)
    apply (cut_tac c="x" and A="tvar_type t2" and B="ds3" in contra_subsetD)
      apply (auto)
    (* lam case *)
   apply (cut_tac ds="insert a ds" and ds'="ds2" in infer_x_subset)
    apply (auto)
  apply (cut_tac env_v="env_v" and ds="ds" and x="Var x1a" and a="a" in add_sub_range)
   apply (auto)
  apply (cut_tac c="x" and A="tvar_type t2" and B="ds2" in contra_subsetD)
    apply (auto)
  done
    
lemma ipvt_const: "\<lbrakk>sub_range env_v ds; xa \<in> pvar_type tau_v; const_scheme x ds tau_v c_list ds'\<rbrakk> \<Longrightarrow> xa \<in> set_diff ds' ds"   
  apply (case_tac x)
              apply (auto)
               apply (simp_all add: pure_fun_s_def)
        apply (simp_all add: set_diff_def)
       apply (simp_all add: fresh_list_def)
  apply (auto)
  done
    
lemma infer_pvar_type: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; sub_range env_v ds \<rbrakk> \<Longrightarrow> pvar_type tau_v \<subseteq> set_diff ds' ds"    
  apply (induct e arbitrary: env_v ds tau_v r_sv r_xv r_mv c_list ds')
        apply (auto)
    (* const + op case *)
          apply (rule_tac ipvt_const)
            apply (auto)
         apply (case_tac x)
              apply (auto)
              apply (simp_all add: pure_fun_s_def)
    (* pair case p1. *)
        apply (simp add: set_diff_def)
        apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
         apply (simp)
        apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
         apply (auto)
       apply (case_tac "\<not> pvar_type t1 \<subseteq> ds2 - ds")
        apply (simp add: set_diff_def)
       apply (auto)
       apply (case_tac "x \<notin> ds2")
        apply (auto)
       apply (case_tac "x \<in> ds")
        apply (auto)
       apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
        apply (auto)
       apply (simp add: set_diff_def)
       apply (auto)
    (* pair case p2. *)
      apply (case_tac "\<not> pvar_type t2 \<subseteq> ds3 - ds2")
       apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
         apply (simp)
        apply (rule_tac infer_x_subset)
        apply (simp)
       apply (simp add: set_diff_def)
      apply (auto)
      apply (case_tac "x \<notin> ds3")
       apply (auto)
      apply (case_tac "x \<in> ds2")
       apply (auto)
      apply (simp add: set_diff_def)
      apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
       apply (auto)
    (* if case *)
     apply (case_tac "\<not> pvar_type t2 \<subseteq> ds3 - ds2")
      apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
        apply (simp)
       apply (rule_tac infer_x_subset)
       apply (simp)
      apply (simp add: set_diff_def)
     apply (case_tac "x \<notin> ds3")
      apply (auto)
     apply (case_tac "x \<in> ds2")
      apply (auto)
     apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
      apply (auto)
     apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
      apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    (* lam case *)
    apply (cut_tac ds="insert a ds" and ds'="ds2" in infer_x_subset)
     apply (simp)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (case_tac "\<not> pvar_type t2 \<subseteq> ds2 - (insert a ds)")
    apply (cut_tac env_v="env_v" and ds="ds" and x="Var x1a" and a="a" in add_sub_range)
     apply (simp)
    apply (simp add: set_diff_def)
   apply (case_tac "p \<notin> ds2")
    apply (auto)
   apply (case_tac "a \<in> insert a ds")
    apply (auto)
   apply (simp add: set_diff_def)
   apply (auto)
   apply (cut_tac ds="insert a ds" and ds'="ds2" in infer_x_subset)
    apply (auto)(*
  apply (cut_tac env_v="add_env env_v (Var x1a) a" and r_sv="r_s'" and ds'="ds2" in infer_s_sub_range)
   apply (auto)*)
  apply (cut_tac env_v="env_v" and ds="ds" and x="Var x1a" and a="a" in add_sub_range)
   apply (auto)
  apply (cut_tac ds="insert a ds" and ds'="ds2" in infer_x_subset)
   apply (auto)
  apply (simp add: set_diff_def)
  apply (auto)
   apply (cut_tac c="x" and A="pvar_type t2" and B="ds2 - (insert a ds)" in contra_subsetD)
     apply (auto)
  apply (cut_tac c="x" and A="pvar_type t2" and B="ds2 - (insert a ds)" in contra_subsetD)
    apply (auto)
  done        
    
    (* #### auxiliary lemmas *)
    
    (* 
      when we call "infer" on an expression, we receive a constraint set representing the set of all possible solutions for well-typedness.

      suppose that an expression is well-typed, and we have a partial solution to the constraint set, solving all permission based constraints,
        reducing all constraints to just type-based constraints.

      Gamma, P1 |- e: tau, P2, Q \<and> Infer(Gamma*, X, e) = (tau*, P*, Q*, R*, K, X') \<and>
        \<rho>( P* ) \<le> P1 \<and> \<rho>( tau* ) \<le> tau \<and> Gamma* \<le> Gamma \<Longrightarrow>
        (\<exists> \<sigma>. \<sigma> |= \<rho>(K) \<and> \<sigma>( Gamma* ) = Gamma \<and> \<sigma>(\<rho>( tau* )) = tau)


      Gamma, P1 |- e: tau, P2, Q \<and> Infer(Gamma*, X, e) = (tau*, P*, Q*, R*, K, X') 
        Gamma* \<le> Gamma \<Longrightarrow>
        (\<exists> \<sigma>. \<sigma> |~ K \<and> \<sigma>( Gamma* ) = Gamma \<and> \<sigma>( tau* ) = tau) 
    *)

lemma dir_subst_spec_env_ex: "\<lbrakk> spec_env env_v env t_subx \<rbrakk> \<Longrightarrow> dir_subst_tenv t_subx env_v = env"
  apply (case_tac "\<forall> x. dir_subst_tenv t_subx env_v x = env x")
   apply (auto)
  apply (simp add: dir_subst_tenv_def)
  apply (simp add: spec_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "env_v x")
   apply (auto)
  done    
    
lemma dir_subst_spec_env: "\<lbrakk> spec_env env_v env t_subx \<rbrakk> \<Longrightarrow> \<exists>t_sub. dir_subst_tenv t_sub env_v = env"  
  apply (rule_tac x="t_subx" in exI)
  apply (rule_tac dir_subst_spec_env_ex)
  apply (simp)
  done
  
lemma ivrcc_prim_case: "\<lbrakk> spec_env env_v env t_sub; tsub_dom t_sub ds \<rbrakk> \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds \<and>
            fresh_list ds (dom_list l) \<and> dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and> (\<exists>p_sub. psub_dom p_sub {})"    
  apply (rule_tac x="[]" in exI)
  apply (auto)
    apply (simp add: fresh_list_def)
   apply (rule_tac dir_subst_spec_env_ex)
   apply (simp)
  apply (rule_tac x="empty_use_env" in exI)
  apply (simp add: psub_dom_def)
  apply (simp add: empty_use_env_def)
  done
       
lemma ivrcc_array_case: "\<lbrakk> spec_env env_v env t_sub; sub_range env_v ds; tsub_dom t_sub ds;
    ta \<notin> ds; req_type t \<noteq> Aff \<rbrakk> \<Longrightarrow>
    \<exists>l. tsub_dom (dir_list_add_env t_sub l) (insert ta ds) \<and>
        fresh_list ds (dom_list l) \<and>
        dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
        (\<exists>p_sub. psub_dom p_sub (insert ta ds - ds)) \<and>
        dir_list_add_env t_sub l ta = Some t \<and> (\<exists>tau_x. dir_list_add_env t_sub l ta = Some tau_x \<and> aff_leq (req_type tau_x) UsePerm)"  
  apply (rule_tac x="[(ta, t)]" in exI)
  apply (auto)
       apply (rule_tac add_tsub_dom)
        apply (rule_tac ds="ds" in subset_tsub_dom)
         apply (auto)
      apply (simp add: fresh_list_def)
     apply (rule_tac ds="ds" in dir_add_eq_env)
       apply (rule_tac dir_subst_spec_env_ex)
       apply (auto)
    apply (rule_tac x="empty_use_env" in exI)
    apply (rule_tac empty_psub_dom)
   apply (simp add: dir_add_env_def)
  apply (rule_tac x="t" in exI)
  apply (simp add: dir_add_env_def)
  apply (case_tac "req_type t")
    apply (auto)  
  done
    
lemma ivrcc_chan_case: "\<lbrakk> spec_env env_v env t_sub; sub_range env_v ds; tsub_dom t_sub ds; ta \<notin> ds \<rbrakk> \<Longrightarrow>
  \<exists>l. tsub_dom (dir_list_add_env t_sub l) (insert ta ds) \<and>
                    fresh_list ds (dom_list l) \<and>
                    dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and> (\<exists>p_sub. psub_dom p_sub (insert ta ds - ds)) \<and> dir_list_add_env t_sub l ta = Some t"    
  apply (rule_tac x="[(ta, t)]" in exI)
  apply (auto)
      apply (rule_tac add_tsub_dom)
       apply (rule_tac ds="ds" in subset_tsub_dom)
        apply (auto)
     apply (simp add: fresh_list_def)
    apply (rule_tac dir_add_eq_env)
      apply (rule_tac dir_subst_spec_env_ex)
      apply (auto)
   apply (rule_tac x="empty_use_env" in exI)
   apply (rule_tac empty_psub_dom)
  apply (simp add: dir_add_env_def)
  done

lemma empty_cut_use_env: "cut_use_env empty_use_env = empty_use_env"    
  apply (case_tac "\<forall> x. cut_use_env empty_use_env x = empty_use_env x")
   apply (auto)
  apply (simp add: cut_use_env_def)
  apply (simp add: empty_use_env_def)
  done
      
lemma ivr_const_case: "\<lbrakk>spec_env env_v env t_sub; sub_range env_v ds; tsub_dom t_sub ds; tau \<in> const_type x; const_scheme x ds tau_v c_list ds';
        leq_use_env (diff_use_env r_s r_ex) r_s; leq_use_env r_x (diff_use_env r_s r_ex)\<rbrakk>
       \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
               fresh_list ds (dom_list l) \<and>
               dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
               (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                        leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub empty_var_env) r_s \<and>
                        leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub empty_var_env) r_ex) r_x \<and>
                        leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub empty_var_env)) r_ex \<and>
                        dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list)"  
  apply (simp add: empty_leq_var_env)
  apply (simp add: subst_empty_var_env)
  apply (simp add: diff_empty_use_env1)
  apply (simp add: empty_cut_use_env)
  apply (simp add: leq_empty_use_env)
  apply (case_tac x)
              apply (auto)
              apply (simp_all add: pure_fun_def)
              apply (simp_all add: pure_fun_s_def)
              apply (simp_all add: unlim_def)
              apply (simp_all add: set_diff_def)
    (* basic cases *)
              apply (rule_tac ivrcc_prim_case)
               apply (auto)
             apply (rule_tac ivrcc_prim_case)
              apply (auto)
            apply (rule_tac ivrcc_prim_case)
             apply (auto)
    (* fixed point *)
           apply (case_tac t)
                 apply (auto)
           apply (rule_tac x="[(t2, x62), (t1, x61)]" in exI)
           apply (auto)
              apply (rule_tac add_tsub_dom)
               apply (rule_tac add_tsub_dom)
                apply (rule_tac ds="ds" in subset_tsub_dom)
                 apply (auto)
             apply (simp add: fresh_list_def)
            apply (rule_tac ds="ds" in dir_add_eq_env)
              apply (rule_tac ds="ds" in dir_add_eq_env)
                apply (rule_tac dir_subst_spec_env_ex)
                apply (auto)
             apply (simp add: fresh_list_def)
             apply (auto)
            apply (simp add: fresh_list_def)
            apply (auto)
           apply (simp add: dir_add_env_def)
           apply (auto)
            apply (simp add: fresh_list_def)
           apply (rule_tac x="add_use_env (add_use_env empty_use_env p x63) q (as_perm x64)" in exI)
           apply (auto)
                apply (rule_tac add_psub_dom)
                 apply (rule_tac add_psub_dom)
                  apply (rule_tac empty_psub_dom)
                 apply (auto)
                 apply (simp add: fresh_list_def)
                 apply (auto)
                apply (simp add: fresh_list_def)
                apply (auto)
               apply (simp add: add_use_env_def)
               apply (simp add: fresh_list_def)
              apply (simp add: add_use_env_def)
              apply (simp add: trip_convert)
             apply (simp add: fresh_list_def)
             apply (simp add: add_use_env_def)
            apply (simp add: fresh_list_def)
            apply (simp add: add_use_env_def)
            apply (simp add: trip_convert)
           apply (simp add: add_use_env_def)
           apply (case_tac x64)
             apply (auto)
    (* null case*)
          apply (rule_tac x="[(t, tau)]" in exI)
          apply (auto)
              apply (rule_tac add_tsub_dom)
               apply (rule_tac ds="ds" in subset_tsub_dom)
                apply (auto)
             apply (simp add: fresh_list_def)
            apply (rule_tac ds="ds" in dir_add_eq_env)
              apply (rule_tac dir_subst_spec_env_ex)
              apply (auto)
           apply (rule_tac x="empty_use_env" in exI)
           apply (rule_tac empty_psub_dom)
          apply (simp add: dir_add_env_def)
    (* array cases *)
         apply (rule_tac ivrcc_array_case)
             apply (auto)
        apply (rule_tac ivrcc_array_case)
            apply (auto)
       apply (rule_tac ivrcc_array_case)
           apply (auto)
    (* unpack *)
      apply (rule_tac x="[(t1a, t1), (t2a, t2), (txa, tx)]" in exI)
      apply (auto)
         apply (rule_tac add_tsub_dom)
          apply (rule_tac add_tsub_dom)
           apply (rule_tac add_tsub_dom)
            apply (rule_tac ds="ds" in subset_tsub_dom)
             apply (auto)
        apply (simp add: fresh_list_def)
       apply (rule_tac ds="ds" in dir_add_eq_env)
         apply (rule_tac ds="ds" in dir_add_eq_env)
           apply (rule_tac ds="ds" in dir_add_eq_env)
             apply (rule_tac dir_subst_spec_env_ex)
             apply (auto)
         apply (simp add: fresh_list_def)
         apply (auto)
        apply (simp add: fresh_list_def)
        apply (auto)
       apply (simp add: fresh_list_def)
       apply (auto)
      apply (rule_tac x="add_use_env (add_use_env empty_use_env p r) p' r'" in exI)
      apply (auto)
                     apply (rule_tac add_psub_dom)
                      apply (rule_tac add_psub_dom)
                      apply (rule_tac empty_psub_dom)
                      apply (auto)
                      apply (simp add: fresh_list_def)
                      apply (auto)
                     apply (simp add: fresh_list_def)
                     apply (auto)
                    apply (simp add: dir_add_env_def)
                   apply (simp add: dir_add_env_def)
                   apply (simp add: fresh_list_def)
                   apply (auto)
                  apply (simp add: add_use_env_def)
                  apply (simp add: fresh_list_def)
                  apply (auto)
                 apply (simp add: dir_add_env_def)
                apply (simp add: dir_add_env_def)
                apply (simp add: fresh_list_def)
                apply (auto)
               apply (simp add: dir_add_env_def)
               apply (simp add: fresh_list_def)
               apply (auto)
              apply (simp add: add_use_env_def)
              apply (simp add: fresh_list_def)
              apply (auto)
             apply (simp add: add_use_env_def)
            apply (simp add: add_use_env_def)
            apply (simp add: fresh_list_def)
            apply (auto)
           apply (simp add: add_use_env_def)
          apply (simp add: dir_add_env_def)
          apply (simp add: fresh_list_def)
          apply (auto)
         apply (simp add: add_use_env_def)
        apply (simp add: add_use_env_def)
        apply (simp add: fresh_list_def)
        apply (auto)
       apply (simp add: add_use_env_def)
       apply (simp add: fresh_list_def)
       apply (auto)
      apply (simp add: add_use_env_def)
      apply (simp add: fresh_list_def)
      apply (auto)
    (* simp chan cases *)
     apply (simp_all add: is_own_def)
     apply (rule_tac ivrcc_chan_case)
        apply (auto)
    apply (rule_tac ivrcc_chan_case)
       apply (auto)
   apply (rule_tac ivrcc_chan_case)
      apply (auto)
    (* fork *)
  apply (rule_tac x="[]" in exI)
  apply (auto)
     apply (rule_tac ds="ds" in subset_tsub_dom)
      apply (auto)
    apply (simp add: fresh_list_def)
   apply (rule_tac dir_subst_spec_env_ex)
   apply (auto)
  apply (rule_tac x="add_use_env empty_use_env p (as_perm a)" in exI)
  apply (auto)
   apply (rule_tac add_psub_dom)
    apply (rule_tac empty_psub_dom)
   apply (auto)
  apply (simp add: add_use_env_def)
  apply (simp add: trip_convert)
  done

lemma ivr_op_case: "\<lbrakk>spec_env env_v env t_sub; sub_range env_v ds'; tsub_dom t_sub ds'; leq_use_env (diff_use_env r_s r_ex) r_s; leq_use_env r_x (diff_use_env r_s r_ex)\<rbrakk>
       \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
               fresh_list ds' (dom_list l) \<and>
               dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
               (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds') \<and>
                        leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub empty_var_env) r_s \<and>
                        leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub empty_var_env) r_ex) r_x \<and>
                        leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub empty_var_env)) r_ex \<and>
                        dir_subst_type (dir_list_add_env t_sub l) p_sub (op_scheme x) (op_type x))"
  apply (rule_tac x="[]" in exI)
  apply (auto)
    apply (simp add: fresh_list_def)
   apply (rule_tac dir_subst_spec_env_ex)
   apply (simp)
  apply (rule_tac x="empty_use_env" in exI)
  apply (simp add: empty_psub_dom)
  apply (simp add: empty_leq_var_env)
  apply (simp add: subst_empty_var_env)
  apply (simp add: diff_empty_use_env1)
  apply (simp add: empty_cut_use_env)
  apply (simp add: leq_empty_use_env)
  apply (case_tac x)
       apply (auto)
       apply (simp_all add: pure_fun_def)
       apply (simp_all add: pure_fun_s_def)
  done

    (* 
      we want to show that if we subtract EX from our constructed requirements - constructed subtractant,
          we will end up with a result contained in Q. (that our total construction is minimal).
        `(X - M) - EX \<le> Q`

      by induction, our constructed reqs should be less than the real reqs. the key then is to make
        sure that we are subtracting our "enough". both the real subtractant + the artificial subtractant.
        we can know that we are since EX subtracts more than both of these.
          (X - M) \<le> rx  \<and>  rx - EX' \<le> Q \<le> P1 - EX' \<le> P1 - EX
    *)
    
lemma squish_leq_use_env: "\<lbrakk> leq_use_env (diff_use_env r_s r_ex') (diff_use_env r_c r_ex);
  leq_use_env (diff_use_env r_c r_ex) (diff_use_env r_c r_ex'); leq_use_env r_x r_s; leq_use_env r_s r_c \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env r_x r_ex) (diff_use_env r_s r_ex')"    
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (simp add: diff_use_env_def)
  apply (case_tac "r_x x")
    apply (auto)
    apply (case_tac "r_ex x")
      apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
    apply (case_tac "r_ex' x")
      apply (auto)
    apply (case_tac "r_c x")
      apply (auto)
    apply (case_tac "r_s x")
      apply (auto)
   apply (case_tac "r_ex' x")
     apply (auto)
   apply (case_tac "r_c x")
     apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  apply (case_tac "r_c x")
    apply (auto)
  done
    
lemma crush_leq_use_env: "\<lbrakk> leq_use_env (diff_use_env r_s r_ex) (diff_use_env r_s r_ex'); leq_use_env r_xa r_s;
  leq_use_env (diff_use_env r_xb r_ex) r_xa \<rbrakk> \<Longrightarrow>
  leq_use_env (diff_use_env r_xb r_ex) (diff_use_env r_xa r_ex')"
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_ex x")
    apply (auto)
   apply (case_tac "r_ex' x")
     apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
   apply (case_tac "r_xa x")
     apply (auto)
  apply (case_tac "r_ex' x")
    apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  apply (case_tac "r_xa x")
    apply (auto)
  done

lemma dist_diff_leq_use_env_rev: "\<lbrakk> leq_use_env r_exa r_s; leq_use_env (diff_use_env r_s r_exb) (diff_use_env r_s r_exa) \<rbrakk> \<Longrightarrow>
  leq_use_env (cut_use_env r_exa) r_exb"
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: cut_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_exa x")
    apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  apply (case_tac "r_exb x")
    apply (auto)
  done
    
lemma ivrvc_ineq: "\<lbrakk> t_sub b = Some tau_x \<rbrakk> \<Longrightarrow>
  leq_use_env (dir_subst_penv t_sub p_sub (one_var_env x (XType b))) (ereq_use_env x tau_x)"   
  apply (simp add: leq_use_env_def)
  apply (simp add: dir_subst_penv_def)
  apply (simp add: one_var_env_def)
  apply (simp add: ereq_use_env_def)
  apply (simp add: one_use_env_def)
  apply (simp add: end_req_perm_def)
  apply (case_tac "req_type tau_x")
    apply (auto)
  done
    
lemma dist_cut_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (cut_use_env r_x) (cut_use_env r_s)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: cut_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma rhs_cut_leq_use_env: "\<lbrakk> leq_use_env (cut_use_env r_x) r_s \<rbrakk> \<Longrightarrow> leq_use_env (cut_use_env r_x) (cut_use_env r_s)"        
  apply (simp add: leq_use_env_def)
  apply (simp add: cut_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma dist_cut_comp_use_env: "cut_use_env (comp_use_env r_s r_x) = comp_use_env (cut_use_env r_s) (cut_use_env r_x)"    
  apply (case_tac "\<forall> x. cut_use_env (comp_use_env r_s r_x) x = comp_use_env (cut_use_env r_s) (cut_use_env r_x) x")  
   apply (auto)
  apply (simp add: cut_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
    apply (simp_all add: comp_use_env_def)
   apply (case_tac "r_x x")
     apply (auto)
    apply (simp_all add: comp_use_env_def)
  apply (case_tac "r_x x")
    apply (auto)
  apply (simp add: comp_use_env_def)
  done
  
lemma lhs_dist_cut_leq_use_env: "\<lbrakk> leq_use_env (comp_use_env (cut_use_env r_s) (cut_use_env r_x)) r_c \<rbrakk> \<Longrightarrow>
  leq_use_env (cut_use_env (comp_use_env r_s r_x)) r_c"    
  apply (simp add: dist_cut_comp_use_env)
  done
  
lemma ivr_var_case: "\<lbrakk>spec_env env_v env t_sub; sub_range env_v ds; tsub_dom t_sub ds; env (Var x) = Some tau; env_v (Var x) = Some a;
        env (Var x) = Some tau_x; value_req x tau tau_x; env_v (Var x) = Some b; leq_use_env (ereq_use_env (Var x) tau_x) r_s;
        leq_use_env (diff_use_env r_s r_ex) (diff_use_env r_s (comp_use_env (ereq_use_env (Var x) tau_x) r_exa)); leq_use_env r_x (diff_use_env r_s r_ex);
        leq_use_env r_exa r_s; leq_use_env (diff_use_env (ereq_use_env (Var x) tau_x) (comp_use_env (ereq_use_env (Var x) tau_x) r_exa)) r_x\<rbrakk>
       \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds \<and>
               fresh_list ds (dom_list l) \<and>
               dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
               (\<exists>p_sub. psub_dom p_sub (set_diff ds ds) \<and>
                        leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub (one_var_env (Var x) (XType b))) r_s \<and>
                        leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub (one_var_env (Var x) (XType b))) r_ex) r_x \<and>
                        leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub (one_var_env (Var x) (XType b)))) r_ex \<and>
                        dir_list_add_env t_sub l a = Some tau)"    
  apply (rule_tac x="[]" in exI)
  apply (auto)
    apply (simp add: fresh_list_def)
   apply (rule_tac dir_subst_spec_env_ex)
   apply (simp)
  apply (case_tac "t_sub a \<noteq> Some tau")
   apply (simp add: spec_env_def)
   apply (erule_tac x="Var x" in allE)
   apply (case_tac "env_v (Var x)")
    apply (auto)
  apply (case_tac "t_sub b \<noteq> Some tau_x")
   apply (simp add: spec_env_def)
  apply (cut_tac t_sub="t_sub" and x="Var x" and b="b" and tau_x="tau_x" in ivrvc_ineq)
   apply (auto)
  apply (rule_tac x="empty_use_env" in exI)
  apply (auto)
      apply (rule_tac empty_psub_dom)
     apply (rule_tac r_sb="ereq_use_env (Var x) tau_x" in trans_leq_use_env)
      apply (simp_all)(*
    apply (rule_tac st_diff_comp_leq_use_env)*)
    apply (rule_tac r_sb="diff_use_env (ereq_use_env (Var x) tau_x) (comp_use_env (ereq_use_env (Var x) tau_x) r_exa)" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac r_s="r_s" in crush_leq_use_env)
      apply (simp_all)
    apply (rule_tac diff_leq_use_env)
    apply (simp)
   apply (rule_tac r_sb="cut_use_env (comp_use_env (ereq_use_env (Var x) tau_x) r_exa)" in trans_leq_use_env)
    apply (rule_tac r_s="r_s" in dist_diff_leq_use_env_rev)
     apply (rule_tac dist_comp_leq_use_env)
      apply (simp_all)
   apply (rule_tac dist_cut_leq_use_env)
   apply (rule_tac comp_leq_use_env1)
   apply (simp)(*
   apply (rule_tac r_sb="diff_use_env (ereq_use_env (owner_name x) tau_x) (comp_use_env (ereq_use_env (owner_name x) tau_x) r_exa)" in trans_leq_use_env)
    apply (auto)
   apply (rule_tac r_c="r_s" in squish_leq_use_env)
      apply (rule_tac r_sb="r_x" in trans_leq_use_env)
       apply (auto)*)
  done
    

lemma ivrpc_coerce: "\<lbrakk> \<And>tau r_s r_x r_ex env env_v ds tau_v r_sv r_xv r_mv c_list ds' t_sub.
           \<lbrakk>well_typed env id r_s e tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds\<rbrakk>
           \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list);
  well_typed env id r_s e tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds \<rbrakk> \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list)"    
  apply (auto)
  done

lemma sub_snorm_use_env: "\<lbrakk> leq_use_env r_exa r_s; leq_use_env r_x (diff_use_env r_s r_exa);
  \<forall> x. super_norm_use_env (diff_use_env r_s r_exa) r_x x = diff_use_env (diff_use_env r_s r_exa) r_exb x \<rbrakk> \<Longrightarrow>
  diff_use_env r_s (comp_use_env r_exa r_exb) = super_norm_use_env r_s r_x"
  apply (case_tac "\<forall> x. diff_use_env r_s (comp_use_env r_exa r_exb) x = super_norm_use_env r_s r_x x")
   apply (auto)
  apply (erule_tac x="x" in allE)
  apply (simp add: leq_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (simp add: super_norm_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (case_tac "diff_perm (r_s x) (r_exa x) = OwnPerm \<and> r_x x = NoPerm")
   apply (auto)
    apply (case_tac "r_exa x")
      apply (auto)
     apply (case_tac "r_exb x")
       apply (auto)
    apply (case_tac "r_exb x")
      apply (auto)
   apply (simp add: diff_use_env_def)
   apply (case_tac "r_s x = OwnPerm \<and> r_x x = NoPerm")
    apply (auto)
     apply (case_tac "r_exa x")
       apply (auto)
    apply (case_tac "r_exa x")
      apply (auto)
      apply (case_tac "r_exb x")
        apply (auto)
     apply (case_tac "r_exb x")
       apply (auto)
    apply (case_tac "r_s x")
      apply (auto)
   apply (case_tac "r_exa x")
     apply (auto)
     apply (case_tac "r_exb x")
       apply (auto)
    apply (case_tac "r_exb x")
      apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (simp add: diff_use_env_def)
  apply (case_tac "r_exa x")
    apply (auto)
    apply (case_tac "r_exb x")
      apply (auto)
   apply (case_tac "r_exb x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
  
    
lemma ivr_induct_format: "\<lbrakk> well_typed env delta r_s1 e1 t1 r_s2 rx1; well_typed env delta r_s2 e2 t2 r_s3 rx2 \<rbrakk> \<Longrightarrow>
  (\<exists> r_exa r_exb. leq_use_env r_exa r_s1 \<and> leq_use_env r_exb (diff_use_env r_s1 r_exa) \<and>
  super_norm_use_env r_s1 r_s3 = diff_use_env r_s1 (comp_use_env r_exa r_exb) \<and>
  well_typed env delta r_s1 e1 t1 (diff_use_env r_s1 r_exa) rx1 \<and>
  well_typed env delta (diff_use_env r_s1 r_exa) e2 t2 (diff_use_env (diff_use_env r_s1 r_exa) r_exb) rx2)"    
  apply (cut_tac env="env" and e="e1" in well_typed_sstr_end_perm) 
   apply (auto)
  apply (cut_tac env="env" and r_c="super_norm_use_env r_s1 r_s2" and e="e2" in well_typed_incr_start_perm)
    apply (auto)
   apply (rule_tac rhs_snorm_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (cut_tac r_s="r_s1" and r_x="r_s2" in snorm_diff_use_env)
  apply (auto)
  apply (cut_tac env="env" and ?r_s1.0="diff_use_env r_s1 r_ex" and e="e2" in well_typed_sstr_end_perm)
   apply (auto)
  apply (cut_tac r_s="diff_use_env r_s1 r_ex" and r_x="r_s3" in snorm_diff_use_env)
  apply (auto)
  apply (rule_tac x="r_ex" in exI)
  apply (auto)
  apply (rule_tac x="r_exa" in exI)
  apply (auto)
  apply (cut_tac r_s="r_s1" and r_x="r_s3" and r_exa="r_ex" and r_exb="r_exa" in sub_snorm_use_env)
     apply (auto)
  apply (rule_tac well_typed_perm_leq)
  apply (auto)
  done
    
lemma sol_sat_split: "\<lbrakk> dir_sol_sat t_sub p_sub cl1; dir_sol_sat t_sub p_sub cl2 \<rbrakk> \<Longrightarrow> dir_sol_sat t_sub p_sub (cl1 @ cl2)"    
  apply (induct cl1)
   apply (auto)
  done

fun tvar_crn where
  "tvar_crn (UnifyCrn t1 t2) = (tvar_type t1 \<union> tvar_type t2)"
(*| "tvar_crn (MemValCrn tau tau_x) = (tvar_type tau \<union> tvar_type tau_x)"*)
| "tvar_crn (LeqCrn px q) = (tvar_set px)"
| "tvar_crn (LeqTypeCrn tau px) = (tvar_type tau)"
| "tvar_crn (DisjCrn px qx) = (tvar_set px \<union> tvar_set qx)" 
| "tvar_crn (SemiDisjCrn px qx) = (tvar_set px \<union> tvar_set qx)"

fun tvar_crn_list where
  "tvar_crn_list [] = {}"
| "tvar_crn_list (c # c_t) = (tvar_crn c \<union> tvar_crn_list c_t)"
  
fun pvar_crn where
  "pvar_crn (UnifyCrn t1 t2) = (pvar_type t1 \<union> pvar_type t2)"
(*| "pvar_crn (MemValCrn tau tau_x) = (pvar_type tau \<union> pvar_type tau_x)"*)
| "pvar_crn (LeqCrn px q) = (pvar_set px \<union> pvar_set_perm q)"
| "pvar_crn (LeqTypeCrn tau px) = (pvar_type tau \<union> pvar_set_perm px)"
| "pvar_crn (DisjCrn px qx) = (pvar_set px \<union> pvar_set qx)" 
| "pvar_crn (SemiDisjCrn px qx) = (pvar_set px \<union> pvar_set qx)"

fun pvar_crn_list where
  "pvar_crn_list [] = {}"
| "pvar_crn_list (c # c_t) = (pvar_crn c \<union> pvar_crn_list c_t)"
  
lemma dir_add_sol_crn: "\<lbrakk> dir_sol_crn t_sub p_sub c; x \<notin> tvar_crn c \<rbrakk> \<Longrightarrow> dir_sol_crn (dir_add_env t_sub x tau) p_sub c"
  apply (case_tac c)
       apply (auto)
               apply (simp_all add: dir_add_subst_permx)
    apply (rule_tac x="tau_x" in exI)
    apply (simp add: dir_add_subst_type)(*
   apply (rule_tac x="t'" in exI)
   apply (rule_tac x="tx'" in exI)
   apply (simp add: dir_add_subst_type)*)
  apply (rule_tac x="tau_x" in exI)
  apply (simp add: dir_add_subst_type)
  done
    
lemma dir_add_sol_sat: "\<lbrakk> dir_sol_sat t_sub p_sub c_list; x \<notin> tvar_crn_list c_list \<rbrakk> \<Longrightarrow> dir_sol_sat (dir_add_env t_sub x tau) p_sub c_list"
  apply (induct c_list)
   apply (auto)
  apply (rule_tac dir_add_sol_crn)
   apply (auto)
  done

    (* if we add variables to t_sub, and those variables are fresh from c_list, solution satisfaction is maintained *)
lemma dir_list_add_sol_sat: "\<lbrakk> dir_sol_sat t_sub p_sub c_list; (dom_list_set l) \<inter> (tvar_crn_list c_list) = {} \<rbrakk> \<Longrightarrow>
  dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list"
  apply (induct l)
   apply (auto)
  apply (rule_tac dir_add_sol_sat)
   apply (auto)
  done

lemma add_psub_sol_crn: "\<lbrakk> dir_sol_crn t_sub p_sub c; x \<notin> pvar_crn c \<rbrakk> \<Longrightarrow>
  dir_sol_crn t_sub (add_use_env p_sub x r) c"
  apply (case_tac c)
       apply (auto)
               apply (simp_all add: add_subst_permx)
     apply (rule_tac x="tau_x" in exI)
     apply (simp add: add_dir_subst_type)(*
    apply (rule_tac x="t'" in exI)
    apply (rule_tac x="tx'" in exI)
    apply (simp add: add_dir_subst_type)*)
   apply (simp add: add_subst_perm)
  apply (rule_tac x="tau_x" in exI)
  apply (auto)
   apply (simp add: add_dir_subst_type)
  apply (simp add: add_subst_perm)
  done
    
lemma add_psub_sol_sat: "\<lbrakk> dir_sol_sat t_sub p_sub c_list; x \<notin> pvar_crn_list c_list \<rbrakk> \<Longrightarrow>
  dir_sol_sat t_sub (add_use_env p_sub x r) c_list"
  apply (induct c_list)
   apply (auto)
  apply (simp add: add_psub_sol_crn)
  done
 
lemma comp_psub_sol_crn: "\<lbrakk> dir_sol_crn t_sub p_sub c; pvar_crn c \<subseteq> ds; psub_dom p_subx ds'; ds \<inter> ds' = {} \<rbrakk> \<Longrightarrow>
  dir_sol_crn t_sub (comp_use_env p_sub p_subx) c"
  apply (induct c)
       apply (auto)
               apply (simp_all add: comp_subst_permx)
     apply (rule_tac x="tau_x" in exI)
     apply (simp add: comp_dir_subst_type1)(*
    apply (rule_tac x="t'" in exI)
    apply (rule_tac x="tx'" in exI)
    apply (simp add: comp_dir_subst_type1)*)
   apply (simp add: comp_subst_perm)
  apply (rule_tac x="tau_x" in exI)
  apply (simp add: comp_dir_subst_type1)
  apply (simp add: comp_subst_perm)
  done
    
lemma comp_psub_sol_sat1: "\<lbrakk> dir_sol_sat t_sub p_sub c_list; pvar_crn_list c_list \<subseteq> ds; psub_dom p_subx ds'; ds \<inter> ds' = {} \<rbrakk> \<Longrightarrow>
  dir_sol_sat t_sub (comp_use_env p_sub p_subx) c_list"
  apply (induct c_list)
   apply (auto)
  apply (simp add: comp_psub_sol_crn)
  done

lemma comp_psub_sol_sat2: "\<lbrakk> dir_sol_sat t_sub p_sub c_list; pvar_crn_list c_list \<subseteq> ds; psub_dom p_subx ds'; ds \<inter> ds' = {} \<rbrakk> \<Longrightarrow>
  dir_sol_sat t_sub (comp_use_env p_subx p_sub) c_list"
  apply (simp add: comm_comp_use_env)
  apply (rule_tac comp_psub_sol_sat1)
     apply (auto)
  done
    
lemma derive_dom_list_set: "\<lbrakk> tsub_dom (dir_list_add_env t_sub l) ds';
  fresh_list ds (dom_list l) \<rbrakk> \<Longrightarrow> dom_list_set l \<subseteq> set_diff ds' ds"
  apply (induct l)
   apply (auto)
   apply (simp add: set_diff_def)
   apply (simp add: tsub_dom_def)
   apply (simp add: fresh_list_def)
   apply (simp add: dir_add_env_def)
  apply (case_tac "tsub_dom (dir_list_add_env t_sub l) ds'")
   apply (case_tac "fresh_list ds (dom_list l)")
    apply (auto)
   apply (simp add: fresh_list_def)
  apply (cut_tac t_sub="dir_list_add_env t_sub l" and x="a" and ds="ds'" and tau="b" in add_tsub_dom_rev)
   apply (auto)
  done
  
    (*
lemma infer_tvar_crn_list: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds' \<rbrakk> \<Longrightarrow> tvar_crn_list c_list \<subseteq> ds'"      
  apply (induct e arbitrary: env_v ds tau_v r_sv r_xv r_mv c_list ds')
        apply (auto)
    *)
    
lemma tvar_clist_split: "\<lbrakk> x \<in> tvar_crn_list (cl1 @ cl2) \<rbrakk> \<Longrightarrow> x \<in> tvar_crn_list cl1 \<or> x \<in> tvar_crn_list cl2"    
  apply (induct cl1)
   apply (auto)
  done    
    
lemma tvar_clist_disj: "\<lbrakk> x \<in> tvar_crn_list (disj_crn r_s r_x d); tvar_range r_s ds; tvar_range r_x ds \<rbrakk> \<Longrightarrow> x \<in> ds"    
  apply (induct d)
   apply (auto)
   apply (simp add: tvar_range_def)
   apply (erule_tac x="a" in allE)
   apply (auto)
  apply (simp add: tvar_range_def)
  apply (erule_tac x="a" in allE)
  apply (auto)
  done
   
lemma tvar_clist_semi_disj: "\<lbrakk> x \<in> tvar_crn_list (semi_disj_crn r_s r_x d); tvar_range r_s ds; tvar_range r_x ds \<rbrakk> \<Longrightarrow> x \<in> ds"    
  apply (induct d)
   apply (auto)
   apply (simp add: tvar_range_def)
   apply (erule_tac x="a" in allE)
   apply (auto)
  apply (simp add: tvar_range_def)
  apply (erule_tac x="a" in allE)
  apply (auto)
  done

lemma tvar_clist_aff: "\<lbrakk> x \<in> tvar_crn_list (aff_crn r_s p d); tvar_range r_s ds; tvar_set_perm p \<subseteq> ds \<rbrakk> \<Longrightarrow> x \<in> ds"    
  apply (induct d)
   apply (auto)
  apply (simp add: tvar_range_def)
  apply (erule_tac x="a" in allE)
  apply (auto)
  done    
    
lemma pvar_clist_split: "\<lbrakk> x \<in> pvar_crn_list (cl1 @ cl2) \<rbrakk> \<Longrightarrow> x \<in> pvar_crn_list cl1 \<or> x \<in> pvar_crn_list cl2"    
  apply (induct cl1)
   apply (auto)
  done
    
lemma pvar_clist_disj: "\<lbrakk> x \<in> pvar_crn_list (disj_crn r_s r_x d); pvar_range r_s ds; pvar_range r_x ds \<rbrakk> \<Longrightarrow> x \<in> ds"    
  apply (induct d)
   apply (auto)
   apply (simp add: pvar_range_def)
   apply (erule_tac x="a" in allE)
   apply (auto)
  apply (simp add: pvar_range_def)
  apply (erule_tac x="a" in allE)
  apply (auto)
  done

lemma pvar_clist_semi_disj: "\<lbrakk> x \<in> pvar_crn_list (semi_disj_crn r_s r_x d); pvar_range r_s ds; pvar_range r_x ds \<rbrakk> \<Longrightarrow> x \<in> ds"    
  apply (induct d)
   apply (auto)
   apply (simp add: pvar_range_def)
   apply (erule_tac x="a" in allE)
   apply (auto)
  apply (simp add: pvar_range_def)
  apply (erule_tac x="a" in allE)
  apply (auto)
  done

lemma pvar_clist_aff: "\<lbrakk> x \<in> pvar_crn_list (aff_crn r_s p d); pvar_range r_s ds; pvar_set_perm p \<subseteq> ds \<rbrakk> \<Longrightarrow> x \<in> ds"    
  apply (induct d)
   apply (auto)
  apply (simp add: pvar_range_def)
  apply (erule_tac x="a" in allE)
  apply (auto)
  done

definition induct_clist where
  "induct_clist v_list ds = (v_list \<subseteq> ds)"
    
lemma infer_tvar_crn_list_ih: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; sub_range env_v ds \<rbrakk> \<Longrightarrow> induct_clist (tvar_crn_list c_list) ds'"    
  apply (induct e arbitrary: env_v ds tau_v r_sv r_xv r_mv c_list ds')
        apply (auto)
    (* const + op case *)
        apply (simp add: induct_clist_def)
        apply (case_tac x)
                    apply (auto)
       apply (simp add: induct_clist_def)
    (* var case *)
      apply (simp add: induct_clist_def)(*
      apply (case_tac x)
       apply (auto)
       apply (simp add: sub_range_def)
       apply (erule_tac x="Loc x22" in allE)
       apply (auto)
      apply (simp add: sub_range_def)
      apply (erule_tac x="Loc x21" in allE)
      apply (auto)*)
    (* pair case *)
     apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
      apply (auto)
     apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
      apply (auto)
     apply (cut_tac ds="ds" and ds'="ds2" and env_v="env_v" in subset_sub_range)
       apply (auto)
     apply (simp add: induct_clist_def)
     apply (auto)
       apply (cut_tac ds="ds" and ds'="ds2" in infer_tvar_type)
         apply (auto)
      apply (cut_tac ds="ds2" and ds'="ds3" in infer_tvar_type)
        apply (auto)
     apply (cut_tac r_sv="r_s1" and r_xv="r_x1" and e="e1" and env_v="env_v" and ds="ds" and ds'="ds2" in infer_tvar_range)
       apply (auto)
     apply (cut_tac r_sv="r_s2" and r_xv="r_x2" and e="e2" and env_v="env_v" and ds="ds2" and ds'="ds3" in infer_tvar_range)
       apply (auto)
     apply (cut_tac r_mv="r_m1" and e="e1" and env_v="env_v" and ds="ds" and ds'="ds2" in infer_m_tvar_range)
       apply (auto)
     apply (cut_tac r_mv="r_m2" and e="e2" and env_v="env_v" and ds="ds2" and ds'="ds3" in infer_m_tvar_range)
       apply (auto)
     apply (cut_tac x="x" and ?cl1.0="disj_crn (lift_var_env r_x1 (SVar p)) (lift_var_env r_x2 (SVar p)) d" and
        ?cl2.0="semi_disj_crn r_m2 r_x1 d @ semi_disj_crn r_m1 r_s2 d @ cl1 @ cl2" in tvar_clist_split)
      apply (auto)
      apply (cut_tac r_s="lift_var_env r_x1 (SVar p)" and r_x="lift_var_env r_x2 (SVar p)" and x="x" and ds="insert p ds3" in tvar_clist_disj)
         apply (simp)
        apply (rule_tac lift_tvar_range)
         apply (rule_tac ds="ds2" in subset_tvar_range)
          apply (auto)
      apply (rule_tac lift_tvar_range)
       apply (rule_tac ds="ds3" in subset_tvar_range)
        apply (auto)
     apply (cut_tac x="x" and ?cl1.0="semi_disj_crn r_m2 r_x1 d" and
        ?cl2.0="semi_disj_crn r_m1 r_s2 d @ cl1 @ cl2" in tvar_clist_split)
      apply (auto)
      apply (cut_tac r_s="r_m2" and r_x="r_x1" and x="x" and ds="insert p ds3" in tvar_clist_semi_disj)
         apply (simp)
        apply (rule_tac ds="ds3" in subset_tvar_range)
         apply (auto)
      apply (rule_tac ds="ds2" in subset_tvar_range)
       apply (auto)
     apply (cut_tac x="x" and ?cl1.0="semi_disj_crn r_m1 r_s2 d" and ?cl2.0="cl1 @ cl2" in tvar_clist_split)
      apply (auto)
      apply (cut_tac r_s="r_m1" and r_x="r_s2" and x="x" and ds="ds3" in tvar_clist_semi_disj)
         apply (simp)
        apply (rule_tac ds="ds2" in subset_tvar_range)
         apply (auto)
     apply (cut_tac x="x" and ?cl1.0="cl1" and ?cl2.0="cl2" in tvar_clist_split)
      apply (auto)
      apply (cut_tac c="x" and A="tvar_crn_list cl1" and B="ds2" in Set.rev_subsetD)
        apply (auto)
     apply (cut_tac c="x" and A="tvar_crn_list cl2" and B="ds3" in Set.rev_subsetD)
       apply (auto)
    (* if case *)
    apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (auto)
    apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
     apply (auto)
    apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
      apply (auto)
    apply (cut_tac env_v="env_v" and ds="ds2" and ds'="ds3" in subset_sub_range)
      apply (auto)
    apply (simp add: induct_clist_def)
    apply (auto)
       apply (cut_tac ds="ds" and ds'="ds2" in infer_tvar_type)
         apply (auto)
      apply (cut_tac ds="ds2" and ds'="ds3" in infer_tvar_type)
        apply (auto)
     apply (cut_tac ds="ds3" and ds'="ds'" in infer_tvar_type)
       apply (auto)
    apply (cut_tac x="x" and ?cl1.0="semi_disj_crn r_m1 (comp_var_env r_s2 r_s3) d" and
        ?cl2.0="cl1 @ cl2 @ cl3" in tvar_clist_split)
     apply (auto)
     apply (cut_tac r_s="r_m1" and r_x="comp_var_env r_s2 r_s3" and x="x" and ds="ds'" in tvar_clist_semi_disj)
        apply (simp)
       apply (cut_tac r_mv="r_m1" and e="e1" and env_v="env_v" and ds="ds" and ds'="ds2" in infer_m_tvar_range)
        apply (auto)
      apply (rule_tac ds="ds2" in subset_tvar_range)
       apply (auto)
     apply (rule_tac comp_tvar_range)
      apply (cut_tac r_sv="r_s2" and e="e2" and env_v="env_v" and ds="ds2" and ds'="ds3" in infer_tvar_range)
       apply (auto)
      apply (rule_tac ds="ds3" in subset_tvar_range)
       apply (auto)
     apply (cut_tac r_sv="r_s3" and e="e3" and env_v="env_v" and ds="ds3" and ds'="ds'" in infer_tvar_range)
      apply (auto)
    apply (cut_tac x="x" and ?cl1.0="cl1" and ?cl2.0="cl2 @ cl3" in tvar_clist_split)
     apply (auto)
     apply (cut_tac c="x" and A="tvar_crn_list cl1" and B="ds2" in Set.rev_subsetD)
       apply (auto)
    apply (cut_tac x="x" and ?cl1.0="cl2" and ?cl2.0="cl3" in tvar_clist_split)
     apply (auto)
     apply (cut_tac c="x" and A="tvar_crn_list cl2" and B="ds3" in Set.rev_subsetD)
       apply (auto)
    apply (cut_tac c="x" and A="tvar_crn_list cl3" and B="ds'" in Set.rev_subsetD)
      apply (auto)
    (* lam case *)
   apply (simp add: induct_clist_def)
   apply (auto)
    apply (cut_tac r_sv="r_s'" and e="e" and env_v="add_env env_v (Var x1a) a" in infer_tvar_range)
      apply (auto) 
     apply (rule_tac add_sub_range)
     apply (simp)
    apply (simp add: tvar_range_def)
    apply (erule_tac x="Var x1a" in allE)
    apply (auto)
   apply (cut_tac x="x" and ?cl1.0="aff_crn (rem_var_env r_s' (Var x1a)) (SVar q) d" and ?cl2.0="cl" in tvar_clist_split)
    apply (auto)
    apply (cut_tac r_s="rem_var_env r_s' (Var x1a)" and x="x" and p="SVar q" and ds="insert q ds2" in tvar_clist_aff)
       apply (simp)
      apply (rule_tac rem_tvar_range)
      apply (rule_tac ds="ds2" in subset_tvar_range)
       apply (cut_tac r_sv="r_s'" and e="e" and env_v="add_env env_v (Var x1a) a" in infer_tvar_range)
         apply (auto)
    apply (cut_tac e="e" and ds="insert a ds" and ds'="ds2" in infer_x_subset)
     apply (auto)
    apply (rule_tac add_sub_range)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and x="Var x1a" and a="a" in add_sub_range)
    apply (simp_all)
   apply (cut_tac c="x" and A="tvar_crn_list cl" and B="ds2" in Set.rev_subsetD)
     apply (auto)
    (* app case *)
  apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
   apply (auto)
  apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
   apply (auto)
  apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
    apply (cut_tac r_sv="r_s1" and e="e1" and env_v="env_v" in infer_tvar_range)
      apply (auto)
  apply (simp add: induct_clist_def)
  apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_tvar_type)
      apply (auto)
   apply (cut_tac ds="ds" and ds'="ds2" in infer_tvar_type)
     apply (auto)
  apply (cut_tac x="x" and ?cl1.0="disj_crn r_x1 (lift_var_env r_x2 (SVar p)) d" and
      ?cl2.0="semi_disj_crn r_m2 r_x1 d @ semi_disj_crn r_m1 r_s2 d @ cl1 @ cl2" in tvar_clist_split)
   apply (auto)
   apply (cut_tac r_s="r_x1" and r_x="lift_var_env r_x2 (SVar p)" and x="x" and ds="insert p ds3" in tvar_clist_disj)
      apply (auto)
    apply (rule_tac ds="ds2" in subset_tvar_range)
     apply (cut_tac r_sv="r_s1" and e="e1" and env_v="env_v" in infer_tvar_range)
       apply (auto)
   apply (rule_tac lift_tvar_range)
    apply (auto)
   apply (rule_tac ds="ds3" in subset_tvar_range)
    apply (auto)
   apply (cut_tac r_sv="r_s2" and e="e2" and ds="ds2" and env_v="env_v" in infer_tvar_range)
     apply (auto)
  apply (cut_tac x="x" and ?cl1.0="semi_disj_crn r_m2 r_x1 d" and ?cl2.0="semi_disj_crn r_m1 r_s2 d @ cl1 @ cl2" in tvar_clist_split)
   apply (auto)
   apply (cut_tac r_s="r_m2" and r_x="r_x1" and x="x" and ds="insert p ds3" in tvar_clist_semi_disj)
      apply (auto)
    apply (rule_tac ds="ds3" in subset_tvar_range)
     apply (auto)
    apply (rule_tac env_v="env_v" and ds="ds2" in infer_m_tvar_range)
     apply (auto)
   apply (rule_tac ds="ds2" in subset_tvar_range)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and e="e1" in infer_tvar_range)
     apply (auto)
  apply (cut_tac x="x" and ?cl1.0="semi_disj_crn r_m1 r_s2 d" and ?cl2.0="cl1 @ cl2" in tvar_clist_split)
   apply (auto)
   apply (cut_tac r_s="r_m1" and r_x="r_s2" and x="x" and ds="insert p ds3" in tvar_clist_semi_disj)
      apply (auto)
    apply (rule_tac ds="ds2" in subset_tvar_range)
     apply (auto)
    apply (rule_tac env_v="env_v" and ds="ds" in infer_m_tvar_range)
      apply (auto)
   apply (rule_tac ds="ds3" in subset_tvar_range)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" in infer_tvar_range)
     apply (auto)
  apply (cut_tac x="x" and ?cl1.0="cl1" and ?cl2.0="cl2" in tvar_clist_split)
   apply (auto)
   apply (cut_tac c="x" and A="tvar_crn_list cl1" and B="ds2" in Set.rev_subsetD)
     apply (auto)
  apply (cut_tac c="x" and A="tvar_crn_list cl2" and B="ds3" in Set.rev_subsetD)
    apply (auto)
  done
    
lemma infer_tvar_crn_list: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; sub_range env_v ds \<rbrakk> \<Longrightarrow> tvar_crn_list c_list \<subseteq> ds'"      
  apply (cut_tac env_v="env_v" and e="e" and ds="ds" and ds'="ds'" in infer_tvar_crn_list_ih)
    apply (auto)
  apply (simp add: induct_clist_def)
  apply (auto)
  done
    
lemma infer_pvar_crn_list_ih: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; sub_range env_v ds \<rbrakk> \<Longrightarrow> induct_clist (pvar_crn_list c_list) (set_diff ds' ds)"    
  apply (induct e arbitrary: env_v ds tau_v r_sv r_xv r_mv c_list ds')
        apply (auto)
    (* const + op case *)
        apply (simp add: induct_clist_def)
        apply (simp add: set_diff_def)
        apply (case_tac x)
                    apply (auto)
           apply (simp add: fresh_list_def)
           apply (auto)
          apply (simp add: fresh_list_def)
          apply (auto)
         apply (simp add: fresh_list_def)
         apply (auto)
        apply (simp add: fresh_list_def)
        apply (auto)
       apply (simp add: induct_clist_def)
    (* var case *)
      apply (simp add: induct_clist_def)(*
      apply (simp add: set_diff_def)
      apply (auto)
      apply (case_tac x)
       apply (auto)*)
    (* pair case *)
     apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
      apply (auto)
     apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
      apply (auto)
     apply (simp add: induct_clist_def)
     apply (auto)
        apply (simp add: set_diff_def)
        apply (auto)
       apply (cut_tac ds="ds" and ds'="ds2" in infer_pvar_type)
         apply (auto)
       apply (simp add: set_diff_def)
       apply (auto)
      apply (cut_tac ds="ds2" and ds'="ds3" in infer_pvar_type)
        apply (auto)
       apply (rule_tac ds="ds" in subset_sub_range)
        apply (auto)
      apply (simp add: set_diff_def)
      apply (auto)
     apply (cut_tac r_sv="r_s1" and r_xv="r_x1" and e="e1" and env_v="env_v" and ds="ds" and ds'="ds2" in infer_s_sub_range)
      apply (auto)
     apply (cut_tac r_sv="r_s2" and r_xv="r_x2" and e="e2" and env_v="env_v" and ds="ds2" and ds'="ds3" in infer_s_sub_range)
      apply (auto)
     apply (cut_tac r_mv="r_m1" and e="e1" and env_v="env_v" and ds="ds" and ds'="ds2" in infer_m_sub_range)
      apply (auto)
     apply (cut_tac r_mv="r_m2" and e="e2" and env_v="env_v" and ds="ds2" and ds'="ds3" in infer_m_sub_range)
      apply (auto)
     apply (cut_tac x="x" and ?cl1.0="disj_crn (lift_var_env r_x1 (SVar p)) (lift_var_env r_x2 (SVar p)) d" and
        ?cl2.0="semi_disj_crn r_m2 r_x1 d @ semi_disj_crn r_m1 r_s2 d @ cl1 @ cl2" in pvar_clist_split)
      apply (auto)
      apply (cut_tac r_s="lift_var_env r_x1 (SVar p)" and r_x="lift_var_env r_x2 (SVar p)" and x="x" and ds="set_diff (insert p ds3) ds" in pvar_clist_disj)
         apply (simp)
        apply (rule_tac lift_pvar_range)
         apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
          apply (auto)
        apply (simp add: set_diff_def)
        apply (auto)
       apply (simp add: set_diff_def)
       apply (auto)
      apply (rule_tac lift_pvar_range)
       apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
        apply (auto)
       apply (simp add: set_diff_def)
       apply (auto)
      apply (simp add: set_diff_def)
      apply (auto)
     apply (cut_tac x="x" and ?cl1.0="semi_disj_crn r_m2 r_x1 d" and
        ?cl2.0="semi_disj_crn r_m1 r_s2 d @ cl1 @ cl2" in pvar_clist_split)
      apply (auto)
      apply (cut_tac r_s="r_m2" and r_x="r_x1" and x="x" and ds="set_diff (insert p ds3) ds" in pvar_clist_semi_disj)
         apply (simp)
        apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
         apply (auto)
       apply (simp add: set_diff_def)
       apply (auto)
      apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
       apply (auto)
      apply (simp add: set_diff_def)
      apply (auto)
     apply (cut_tac x="x" and ?cl1.0="semi_disj_crn r_m1 r_s2 d" and ?cl2.0="cl1 @ cl2" in pvar_clist_split)
      apply (auto)
      apply (cut_tac r_s="r_m1" and r_x="r_s2" and x="x" and ds="set_diff (insert p ds3) ds" in pvar_clist_semi_disj)
         apply (simp)
        apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
         apply (auto)
       apply (simp add: set_diff_def)
       apply (auto)
      apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
       apply (auto)
      apply (simp add: set_diff_def)
      apply (auto)
     apply (cut_tac x="x" and ?cl1.0="cl1" and ?cl2.0="cl2" in pvar_clist_split)
      apply (auto)
      apply (case_tac "x \<in> set_diff ds2 ds")
       apply (simp add: set_diff_def)
       apply (auto)
      apply (cut_tac c="x" and A="pvar_crn_list cl1" and B="set_diff ds2 ds" in Set.rev_subsetD)
        apply (auto)
     apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
       apply (auto)
     apply (cut_tac c="x" and A="pvar_crn_list cl2" and B="set_diff ds3 ds2" in Set.rev_subsetD)
       apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    (* if case *)
    apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (auto)
    apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
     apply (auto)
    apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
      apply (auto)
    apply (cut_tac env_v="env_v" and ds="ds2" and ds'="ds3" in subset_sub_range)
      apply (auto)
    apply (simp add: induct_clist_def)
    apply (auto)
       apply (cut_tac ds="ds" and ds'="ds2" in infer_pvar_type)
         apply (auto)
       apply (simp add: set_diff_def)
       apply (auto)
      apply (cut_tac ds="ds2" and ds'="ds3" in infer_pvar_type)
        apply (auto)
      apply (simp add: set_diff_def)
      apply (auto)
     apply (cut_tac ds="ds3" and ds'="ds'" in infer_pvar_type)
       apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (cut_tac x="x" and ?cl1.0="semi_disj_crn r_m1 (comp_var_env r_s2 r_s3) d" and
        ?cl2.0="cl1 @ cl2 @ cl3" in pvar_clist_split)
     apply (auto)
     apply (cut_tac r_s="r_m1" and r_x="comp_var_env r_s2 r_s3" and x="x" and ds="set_diff ds' ds" in pvar_clist_semi_disj)
        apply (simp)
       apply (cut_tac r_mv="r_m1" and e="e1" and env_v="env_v" and ds="ds" and ds'="ds2" in infer_m_sub_range)
        apply (auto)
      apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
       apply (auto)
      apply (simp add: set_diff_def)
      apply (auto)
     apply (rule_tac comp_pvar_range)
      apply (cut_tac r_sv="r_s2" and e="e2" and env_v="env_v" and ds="ds2" and ds'="ds3" in infer_s_sub_range)
       apply (auto)
      apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
       apply (auto)
      apply (simp add: set_diff_def)
      apply (auto)
     apply (cut_tac r_sv="r_s3" and e="e3" and env_v="env_v" and ds="ds3" and ds'="ds'" in infer_s_sub_range)
      apply (auto)
     apply (rule_tac ds="set_diff ds' ds3" in subset_pvar_range)
      apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (cut_tac x="x" and ?cl1.0="cl1" and ?cl2.0="cl2 @ cl3" in pvar_clist_split)
     apply (auto)
     apply (cut_tac c="x" and A="pvar_crn_list cl1" and B="set_diff ds2 ds" in Set.rev_subsetD)
       apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (cut_tac x="x" and ?cl1.0="cl2" and ?cl2.0="cl3" in pvar_clist_split)
     apply (auto)
     apply (cut_tac c="x" and A="pvar_crn_list cl2" and B="set_diff ds3 ds2" in Set.rev_subsetD)
       apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (cut_tac c="x" and A="pvar_crn_list cl3" and B="set_diff ds' ds3" in Set.rev_subsetD)
      apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
    (* lam case *)
   apply (simp add: induct_clist_def)
   apply (auto)
     apply (case_tac "p \<in> ds")
      apply (cut_tac ds="insert a ds" and ds'="ds2" in infer_x_subset)
       apply (auto)
     apply (simp add: set_diff_def)
    apply (cut_tac r_sv="r_s'" and e="e" and env_v="add_env env_v (Var x1a) a" in infer_s_sub_range)
     apply (auto)
    apply (simp add: pvar_range_def)
    apply (erule_tac x="Var x1a" in allE)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac x="x" and ?cl1.0="aff_crn (rem_var_env r_s' (Var x1a)) (SVar q) d" and ?cl2.0="cl" in pvar_clist_split)
    apply (auto)
    apply (cut_tac r_s="rem_var_env r_s' (Var x1a)" and x="x" and p="SVar q" and ds="set_diff (insert q ds2) ds" in pvar_clist_aff)
       apply (simp)
      apply (rule_tac rem_pvar_range)
      apply (rule_tac ds="set_diff ds2 (insert a ds)" in subset_pvar_range)
       apply (cut_tac r_sv="r_s'" and e="e" and env_v="add_env env_v (Var x1a) a" in infer_s_sub_range)
        apply (auto)
      apply (simp add: set_diff_def)
     apply (case_tac "q \<in> ds")
      apply (cut_tac e="e" and ds="insert a ds" and ds'="ds2" in infer_x_subset)
       apply (auto)
     apply (simp add: set_diff_def)
    apply (simp add: set_diff_def)
   apply (cut_tac env_v="env_v" and ds="ds" and x="Var x1a" and a="a" in add_sub_range)
    apply (simp)
   apply (cut_tac c="x" and A="pvar_crn_list cl" and B="set_diff ds2 (insert a ds)" in Set.rev_subsetD)
     apply (auto)
   apply (simp add: set_diff_def)
    (* app case *)
  apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
   apply (auto)
  apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
   apply (auto)
  apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
    apply (cut_tac r_sv="r_s1" and e="e1" and env_v="env_v" in infer_s_sub_range)
     apply (auto)
  apply (simp add: induct_clist_def)
  apply (auto)
      apply (case_tac "q \<in> ds3")
       apply (simp add: fresh_list_def)
       apply (auto)
      apply (simp add: set_diff_def)
      apply (auto)
     apply (case_tac "p \<in> ds3")
      apply (simp add: fresh_list_def)
      apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_pvar_type)
      apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac ds="ds" and ds'="ds2" in infer_pvar_type)
     apply (auto)
   apply (simp add: set_diff_def)
   apply (auto)
  apply (cut_tac x="x" and ?cl1.0="disj_crn r_x1 (lift_var_env r_x2 (SVar p)) d" and
      ?cl2.0="semi_disj_crn r_m2 r_x1 d @ semi_disj_crn r_m1 r_s2 d @ cl1 @ cl2" in pvar_clist_split)
   apply (auto)
   apply (cut_tac r_s="r_x1" and r_x="lift_var_env r_x2 (SVar p)" and x="x" and ds="set_diff (insert p ds3) ds" in pvar_clist_disj)
      apply (auto)
     apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
      apply (cut_tac r_sv="r_s1" and e="e1" and env_v="env_v" in infer_s_sub_range)
       apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (cut_tac r_sv="r_s2" and e="e2" and env_v="env_v" in infer_s_sub_range)
     apply (auto)
    apply (rule_tac lift_pvar_range)
     apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
      apply (simp)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (case_tac "p \<in> ds3")
     apply (simp add: fresh_list_def)
     apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (simp add: set_diff_def)
   apply (auto)
  apply (cut_tac x="x" and ?cl1.0="semi_disj_crn r_m2 r_x1 d" and
      ?cl2.0="semi_disj_crn r_m1 r_s2 d @ cl1 @ cl2" in pvar_clist_split)
   apply (auto)
   apply (cut_tac r_s="r_m2" and r_x="r_x1" and x="x" and ds="set_diff (insert p ds3) ds" in pvar_clist_semi_disj)
      apply (auto)
     apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
      apply (rule_tac infer_m_sub_range)
      apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
     apply (cut_tac ds="ds" and ds'="ds2" in infer_s_sub_range)
      apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (simp add: set_diff_def)
   apply (auto)
  apply (cut_tac x="x" and ?cl1.0="semi_disj_crn r_m1 r_s2 d" and
      ?cl2.0="cl1 @ cl2" in pvar_clist_split)
   apply (auto)
   apply (cut_tac r_s="r_m1" and r_x="r_s2" and x="x" and ds="set_diff (insert p ds3) ds" in pvar_clist_semi_disj)
      apply (auto)
     apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
      apply (rule_tac infer_m_sub_range)
      apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
     apply (cut_tac ds="ds2" and ds'="ds3" in infer_s_sub_range)
      apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (simp add: set_diff_def)
   apply (auto)
  apply (cut_tac x="x" and ?cl1.0="cl1" and ?cl2.0="cl2" in pvar_clist_split)
   apply (auto)
   apply (cut_tac c="x" and A="pvar_crn_list cl1" and B="set_diff ds2 ds" in Set.rev_subsetD)
     apply (auto)
   apply (simp add: set_diff_def)
   apply (auto)
  apply (cut_tac c="x" and A="pvar_crn_list cl2" and B="set_diff ds3 ds2" in Set.rev_subsetD)
    apply (auto)
  apply (simp add: set_diff_def)
  apply (auto)
  done
    
lemma infer_pvar_crn_list: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; sub_range env_v ds \<rbrakk> \<Longrightarrow> pvar_crn_list c_list \<subseteq> set_diff ds' ds"    
  apply (cut_tac env_v="env_v" and e="e" and ds="ds" and ds'="ds'" in infer_pvar_crn_list_ih)
    apply (auto)
  apply (simp add: induct_clist_def)
  apply (auto)
  done
    
lemma sol_sat_disj: "\<lbrakk> disj_use_env (dir_subst_penv t_sub p_sub r_s) (dir_subst_penv t_sub p_sub r_x) \<rbrakk> \<Longrightarrow> dir_sol_sat t_sub p_sub (disj_crn r_s r_x d)"    
  apply (induct d)
   apply (auto)
   apply (simp add: disj_use_env_def)
   apply (simp add: mini_disj_use_env_def)
   apply (simp add: dir_subst_penv_def)
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: dir_subst_penv_def)
  done

lemma sol_sat_mini_disj: "\<lbrakk> mini_disj_use_env (dir_subst_penv t_sub p_sub r_s) (dir_subst_penv t_sub p_sub r_x) \<rbrakk> \<Longrightarrow>
  dir_sol_sat t_sub p_sub (semi_disj_crn r_s r_x d)"    
  apply (induct d)
   apply (auto)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: dir_subst_penv_def)
  done
  (*
lemma sol_sat_aff: "\<lbrakk> aff_use_env (dir_subst_penv t_sub p_sub r_s) a \<rbrakk> \<Longrightarrow> dir_sol_sat t_sub p_sub (aff_crn r_s (SVar p) d)"    *)

lemma cut_disj_use_env: "\<lbrakk> mini_disj_use_env r_x r_s \<rbrakk> \<Longrightarrow> disj_use_env r_s (cut_use_env r_x)"    
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: cut_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma swap_diff_cut_leq_use_env: "\<lbrakk> leq_use_env r_x r_s; leq_use_env r_ex (diff_use_env r_s r_x) \<rbrakk> \<Longrightarrow>
  leq_use_env (cut_use_env r_x) (diff_use_env r_s r_ex)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: cut_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done
    
lemma cut_mini_disj_use_env: "\<lbrakk> mini_disj_use_env (cut_use_env r_s) r_x \<rbrakk> \<Longrightarrow> mini_disj_use_env r_s r_x"    
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: cut_use_env_def)
  done

lemma ivrpc_main: "\<lbrakk>
        spec_env env_v (dir_subst_tenv (dir_list_add_env t_sub l) env_v) t_sub; sub_range env_v ds; tsub_dom t_sub ds;
        infer_type env_v ds e1 t1a r_s1 r_x1 r_m1 cl1 ds2; 
        infer_type env_v ds2 e2 t2a r_s2 r_x2 r_m2 cl2 ds3;
        leq_use_env (lift_use_env rx1 r) r_s3; leq_use_env (lift_use_env rx2 r) r_s3; aff_leq (max_aff (req_type t1) (req_type t2)) r;
        disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r); leq_use_env r_s3 r_s;
        finite_dom (comp_var_env (comp_var_env r_s1 (lift_var_env r_x1 (SVar p))) (comp_var_env r_s2 (lift_var_env r_x2 (SVar p)))) d;
        leq_use_env (diff_use_env r_s r_ex) (diff_use_env r_s3 r_exa); p \<notin> ds3; leq_use_env r_exa r_s;
        leq_use_env (pair_req (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_exa (PairTy t1 t2 r)) r_x; leq_use_env r_exaa r_s;
        leq_use_env r_exb (diff_use_env r_s r_exaa); super_norm_use_env r_s r_s3 = diff_use_env r_s (comp_use_env r_exaa r_exb);
        well_typed (dir_subst_tenv (dir_list_add_env t_sub l) env_v) id r_s e1 t1 (diff_use_env r_s r_exaa) rx1;
        well_typed (dir_subst_tenv (dir_list_add_env t_sub l) env_v) id (diff_use_env r_s r_exaa) e2 t2 (diff_use_env (diff_use_env r_s r_exaa) r_exb) rx2;
        tsub_dom (dir_list_add_env t_sub l) ds2; fresh_list ds (dom_list l); env = dir_subst_tenv (dir_list_add_env t_sub l) env_v;
        psub_dom p_sub (set_diff ds2 ds); leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_s1) r_s;
        leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_x1) r_exaa) rx1;
        leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_m1)) r_exaa; dir_subst_type (dir_list_add_env t_sub l) p_sub t1a t1;
        dir_sol_sat (dir_list_add_env t_sub l) p_sub cl1; tsub_dom (dir_list_add_env (dir_list_add_env t_sub l) la) ds3; fresh_list ds2 (dom_list la);
        dir_subst_tenv (dir_list_add_env (dir_list_add_env t_sub l) la) env_v = dir_subst_tenv (dir_list_add_env t_sub l) env_v;
        psub_dom p_suba (set_diff ds3 ds2); leq_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba r_s2) (diff_use_env r_s r_exaa);
        leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba r_x2) r_exb) rx2;
        leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba r_m2)) r_exb;
        dir_subst_type (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba t2a t2; dir_sol_sat (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba cl2\<rbrakk>
       \<Longrightarrow> \<exists>la. tsub_dom (dir_list_add_env t_sub la) (insert p ds3) \<and>
                fresh_list ds (dom_list la) \<and>
                dir_subst_tenv (dir_list_add_env t_sub la) env_v = dir_subst_tenv (dir_list_add_env t_sub l) env_v \<and>
                (\<exists>p_sub. psub_dom p_sub (set_diff (insert p ds3) ds) \<and>
                         leq_use_env
                          (dir_subst_penv (dir_list_add_env t_sub la) p_sub
                            (comp_var_env (comp_var_env r_s1 (lift_var_env r_x1 (SVar p))) (comp_var_env r_s2 (lift_var_env r_x2 (SVar p)))))
                          r_s \<and>
                         leq_use_env
                          (diff_use_env
                            (dir_subst_penv (dir_list_add_env t_sub la) p_sub
                              (ifz_var_env (XPerm (SVar p)) (comp_var_env (lift_var_env r_x1 (SVar p)) (lift_var_env r_x2 (SVar p)))))
                            r_ex)
                          r_x \<and>
                         leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub la) p_sub (comp_var_env r_m1 r_m2))) r_ex \<and>
                         dir_subst_type (dir_list_add_env t_sub la) p_sub t1a t1 \<and>
                         dir_subst_type (dir_list_add_env t_sub la) p_sub t2a t2 \<and>
                         r = p_sub p \<and>
                         (\<exists>tau_x. dir_subst_type (dir_list_add_env t_sub la) p_sub t1a tau_x \<and> aff_leq (req_type tau_x) (p_sub p)) \<and>
                         (\<exists>tau_x. dir_subst_type (dir_list_add_env t_sub la) p_sub t2a tau_x \<and> aff_leq (req_type tau_x) (p_sub p)) \<and>
                         dir_sol_sat (dir_list_add_env t_sub la) p_sub
                          (disj_crn (lift_var_env r_x1 (SVar p)) (lift_var_env r_x2 (SVar p)) d @
                           semi_disj_crn r_m2 r_x1 d @ semi_disj_crn r_m1 r_s2 d @ cl1 @ cl2))"    
    (* defining new t_sub *)
  apply (rule_tac x="la @ l" in exI)
  apply (auto)
     apply (rule_tac append_tsub_dom)
      apply (rule_tac ds="ds" in list_add_tsub_dom)
        apply (auto)
       apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
        apply (auto)
       apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
        apply (auto)
      apply (cut_tac t_sub="t_sub" and l="l" and ds="ds2" in list_add_dls)
       apply (auto)
      apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
       apply (auto)
     apply (cut_tac t_sub="dir_list_add_env t_sub l" and l="la" and ds="ds3" in list_add_dls)
      apply (auto)
    apply (rule_tac ds="ds" and ds'="ds2" in append_fresh_list2)
       apply (auto)
    apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
     apply (auto)
   apply (simp add: dir_list_append_eq)
    (* P* inequality 1 *)
  apply (case_tac "\<not> leq_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) r_s1) r_s")
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and l="la" and p_sub="add_use_env (comp_use_env p_sub p_suba) p r"
                and r_sv="r_s1" and ds="ds2" in dir_list_add_cancel_use_env)
     apply (auto)
    apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_tvar_range)
      apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_s_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and p_sub="comp_use_env p_sub p_suba" and r_xv="r_s1" and ds="set_diff ds2 ds" and x="p" and r="r" in add_psub_use_env)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and ?p_sub1.0="p_sub" and ?p_sub2.0="p_suba" and r_xv="r_s1" and ds="set_diff ds2 ds" in comp_psub_use_env1)
      apply (auto)
   apply (simp add: set_diff_def)
    (* P* inequality 2 *)
  apply (case_tac "\<not> leq_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) r_s2) (diff_use_env r_s r_exaa)")
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_s_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and p_sub="comp_use_env p_sub p_suba" and r_xv="r_s2" and ds="set_diff ds3 ds2" and x="p" and r="r" in add_psub_use_env)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and ?p_sub1.0="p_suba" and ?p_sub2.0="p_sub" and r_xv="r_s2" and ds="set_diff ds3 ds2" in comp_psub_use_env2)
      apply (auto)
   apply (simp add: set_diff_def)   
    (* X* inequality 1 *)
  apply (case_tac "\<not> leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) r_x1) r_exaa) rx1")
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and l="la" and p_sub="add_use_env (comp_use_env p_sub p_suba) p r"
                and r_sv="r_x1" and ds="ds2" in dir_list_add_cancel_use_env)
     apply (auto)
    apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_tvar_range)
      apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_s_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and p_sub="comp_use_env p_sub p_suba" and r_xv="r_x1" and ds="set_diff ds2 ds" and x="p" and r="r" in add_psub_use_env)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and ?p_sub1.0="p_sub" and ?p_sub2.0="p_suba" and r_xv="r_x1" and ds="set_diff ds2 ds" in comp_psub_use_env1)
      apply (auto)
   apply (simp add: set_diff_def) 
    (* X* inequality 2 *)
  apply (case_tac "\<not> leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) r_x2) r_exb) rx2")
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_s_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and p_sub="comp_use_env p_sub p_suba" and r_xv="r_x2" and ds="set_diff ds3 ds2" and x="p" and r="r" in add_psub_use_env)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and ?p_sub1.0="p_suba" and ?p_sub2.0="p_sub" and r_xv="r_x2" and ds="set_diff ds3 ds2" in comp_psub_use_env2)
      apply (auto)
   apply (simp add: set_diff_def)
    (* M* inequality 1 *)
  apply (case_tac "\<not> leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) r_m1)) r_exaa")
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and l="la" and p_sub="add_use_env (comp_use_env p_sub p_suba) p r"
                and r_sv="r_m1" and ds="ds2" in dir_list_add_cancel_use_env)
     apply (auto)
    apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_m_tvar_range)
      apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_m_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and p_sub="comp_use_env p_sub p_suba" and r_xv="r_m1" and ds="set_diff ds2 ds" and x="p" and r="r" in add_psub_use_env)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and ?p_sub1.0="p_sub" and ?p_sub2.0="p_suba" and r_xv="r_m1" and ds="set_diff ds2 ds" in comp_psub_use_env1)
      apply (auto)
   apply (simp add: set_diff_def)
    (* M* inequality 2 *)
  apply (case_tac "\<not> leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) r_m2)) r_exb")
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_m_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and p_sub="comp_use_env p_sub p_suba" and r_xv="r_m2" and ds="set_diff ds3 ds2" and x="p" and r="r" in add_psub_use_env)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and ?p_sub1.0="p_suba" and ?p_sub2.0="p_sub" and r_xv="r_m2" and ds="set_diff ds3 ds2" in comp_psub_use_env2)
      apply (auto)
   apply (simp add: set_diff_def)
    (* - prelim: (t_sub, p_sub)(t1a) = t1 *)
  apply (cut_tac t_sub="dir_list_add_env t_sub l" and l="la" and p_sub="add_use_env (comp_use_env p_sub p_suba) p r" and
      tau_v="t1a" and tau="t1" in dir_list_add_subst_type)
    apply (rule_tac add_dir_subst_type)
     apply (rule_tac ds="set_diff ds2 ds" in comp_dir_subst_type1)
        apply (simp)
       apply (rule_tac infer_pvar_type)
        apply (auto)
     apply (simp add: set_diff_def)
    apply (cut_tac tau_v="t1a" and ds'="ds2" and ds="ds" in infer_pvar_type)
      apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (simp)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac x="x" and l="la" in dom_list_contain)
    apply (simp)
   apply (cut_tac tau_v="t1a" and ds'="ds2" and ds="ds" in infer_tvar_type)
     apply (auto)
   apply (simp add: fresh_list_def)
   apply (auto)
    (* - prelim: (t_sub, p_sub)(t2a) = t2 *)
  apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and p_sub="comp_use_env p_sub p_suba" and p="p" and r="r" and
      tau_v="t2a" and tau="t2" in add_dir_subst_type)
    apply (rule_tac ds="set_diff ds3 ds2" in comp_dir_subst_type2)
       apply (simp)
      apply (rule_tac infer_pvar_type)
       apply (auto)
     apply (rule_tac ds="ds" in subset_sub_range)
      apply (simp)
     apply (rule_tac infer_x_subset)
     apply (simp)
    apply (simp add: set_diff_def)
   apply (cut_tac tau_v="t2a" and ds'="ds3" and ds="ds2" in infer_pvar_type)
     apply (auto)
    apply (rule_tac ds="ds" in subset_sub_range)
     apply (simp)
    apply (rule_tac infer_x_subset)
    apply (simp)
   apply (simp add: set_diff_def)
   apply (auto)
    (* defining new p_sub *)
  apply (rule_tac x="add_use_env (comp_use_env p_sub p_suba) p r" in exI)
  apply (auto)
    (* - psub domain containment *)
           apply (rule_tac add_psub_dom)
            apply (rule_tac comp_psub_dom)
             apply (rule_tac ds="set_diff ds2 ds" in subset_psub_dom)
              apply (simp)
             apply (rule_tac set_diff_subset)
              apply (auto)
             apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
              apply (auto)
            apply (rule_tac ds="set_diff ds3 ds2" in subset_psub_dom)
             apply (simp)
            apply (rule_tac set_diff_subset)
             apply (auto)
            apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
             apply (auto)
           apply (simp add: set_diff_def)
           apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
            apply (auto)
           apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
            apply (auto)
    (* - p_sub(r_sv) \<le> r_s *)
          apply (rule_tac dist_comp_leq_var_env)
           apply (simp add: dir_list_append_eq)
           apply (rule_tac dist_comp_leq_var_env)
            apply (auto)
           apply (rule_tac t="dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) (lift_var_env r_x1 (SVar p))"
            and s="lift_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) r_x1)
                  (sol_subst_perm (add_use_env (comp_use_env p_sub p_suba) p r) (SVar p))" in subst)
            apply (rule_tac lift_sol_subst_penv)
           apply (auto)
           apply (case_tac "add_use_env (comp_use_env p_sub p_suba) p r p \<noteq> r")
            apply (simp add: add_use_env_def)
           apply (auto)
           apply (rule_tac r_ex="r_exaa" in diff_leq_use_env_rev)
            apply (simp add: lift_diff_use_env)
            apply (rule_tac r_sb="lift_use_env rx1 r" in trans_leq_use_env)
             apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
              apply (simp_all)
           apply (rule_tac dist_lift_leq_use_env)
           apply (simp)
    (* > part 2. *)
          apply (simp add: dir_list_append_eq)
          apply (rule_tac dist_comp_leq_var_env)
           apply (rule_tac r_sb="diff_use_env r_s r_exaa" in trans_leq_use_env)
            apply (rule_tac self_diff_leq_use_env)
           apply (simp)
          apply (rule_tac t="dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) (lift_var_env r_x2 (SVar p))"
            and s="lift_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) r_x2)
                  (sol_subst_perm (add_use_env (comp_use_env p_sub p_suba) p r) (SVar p))" in subst)
           apply (rule_tac lift_sol_subst_penv)
          apply (rule_tac r_ex="r_exb" in diff_leq_use_env_rev)
           apply (simp add: lift_diff_use_env)
           apply (rule_tac r_sb="lift_use_env rx2 r" in trans_leq_use_env)
            apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
             apply (simp_all)
           apply (case_tac "add_use_env (comp_use_env p_sub p_suba) p r p \<noteq> r")
            apply (simp add: add_use_env_def)
           apply (auto)
           apply (rule_tac dist_lift_leq_use_env)
           apply (simp)
          apply (rule_tac r_sb="diff_use_env r_s r_exaa" in trans_leq_use_env)
           apply (rule_tac self_diff_leq_use_env)
          apply (simp)
    (* - p_sub(r_xv) \<le> r_x. primitive case *)
        apply (case_tac "r = NoPerm")
         apply (cut_tac t_sub="dir_list_add_env t_sub (la @ l)" and p_sub="add_use_env (comp_use_env p_sub p_suba) p r" and p="p" and
          r_sv="comp_var_env (lift_var_env r_x1 (SVar p)) (lift_var_env r_x2 (SVar p))" in ifz_sol_subst_penv)
          apply (auto)
          apply (simp add: add_use_env_def)
         apply (rule_tac diff_leq_use_env)
         apply (rule_tac leq_empty_use_env)
        apply (simp add: pair_req_def)
    (* > non-primitive case *)
         apply (simp add: dir_list_append_eq)
         apply (case_tac "as_aff r = Prim")
          apply (case_tac r)
            apply (auto)
        apply (rule_tac r_sb="diff_use_env
              (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r)
                (comp_var_env (lift_var_env r_x1 (SVar p)) (lift_var_env r_x2 (SVar p)))) r_ex" in trans_leq_use_env)
         apply (simp add: comp_sol_subst_penv)
         apply (rule_tac lhs_dist_dcl_use_env)
         apply (rule_tac r_sb="diff_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_exa" in trans_leq_use_env)
          apply (simp)
         apply (rule_tac dist_comp_leq_use_env)
          apply (rule_tac t="dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) (lift_var_env r_x1 (SVar p))"
          and s="lift_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) r_x1)
            (sol_subst_perm (add_use_env (comp_use_env p_sub p_suba) p r) (SVar p))" in subst)
           apply (rule_tac lift_sol_subst_penv)
          apply (rule_tac r_sb="diff_use_env (lift_use_env rx1 r) r_exa" in trans_leq_use_env)
           apply (rule_tac dist_diff_leq_use_env)
           apply (rule_tac self_comp_leq_use_env1)
          apply (simp add: lift_diff_use_env)
          apply (case_tac "add_use_env (comp_use_env p_sub p_suba) p r p \<noteq> r")
           apply (simp add: add_use_env_def)
          apply (simp)
          apply (rule_tac dist_lift_leq_use_env)
           apply (rule_tac r_s="r_s" in crush_leq_use_env)
             apply (rule_tac r_sb="diff_use_env r_s3 r_exa" in trans_leq_use_env)
              apply (rule_tac dist_diff_leq_use_env)
              apply (simp_all)
             apply (rule_tac r_sb="lift_use_env rx1 r" in trans_leq_use_env)
              apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
               apply (simp_all)
            apply (rule_tac self_lift_leq_use_env)
            apply (rule_tac r_sb="diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la)
              (add_use_env (comp_use_env p_sub p_suba) p r) r_x1) r_exaa" in trans_leq_use_env)
            apply (simp)
           apply (rule_tac r_s="r_s" in crush_leq_use_env)
             apply (rule_tac r_sb="super_norm_use_env r_s r_s3" in trans_leq_use_env)
              apply (simp)
              apply (rule_tac dist_diff_leq_use_env_gen)
               apply (rule_tac id_leq_use_env)
              apply (rule_tac self_comp_leq_use_env1)
             apply (rule_tac rhs_snorm_leq_use_env)
              apply (rule_tac self_diff_leq_use_env)
             apply (rule_tac r_sb="diff_use_env r_s3 r_exa" in trans_leq_use_env)
              apply (rule_tac self_diff_leq_use_env)
             apply (simp)
            apply (rule_tac r_sb="dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la)
              (add_use_env (comp_use_env p_sub p_suba) p r) r_s1" in trans_leq_use_env)
             apply (simp)
            apply (rule_tac infer_x_leq_use_env)
            apply (auto)
           apply (rule_tac self_diff_leq_use_env)
    (* > transformation proving removal of extra substitutions is sound *)
    (* > part 2. *)
         apply (rule_tac t="dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) (lift_var_env r_x2 (SVar p))"
          and s="lift_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) r_x2)
            (sol_subst_perm (add_use_env (comp_use_env p_sub p_suba) p r) (SVar p))" in subst)
          apply (rule_tac lift_sol_subst_penv)
         apply (rule_tac rhs_dist_dcl_use_env)
         apply (rule_tac comp_leq_use_env2)
         apply (simp add: lift_diff_use_env)
         apply (case_tac "add_use_env (comp_use_env p_sub p_suba) p r p \<noteq> r")
          apply (simp add: add_use_env_def)
         apply (simp)
         apply (rule_tac dist_lift_leq_use_env)
          apply (rule_tac r_s="r_s" in crush_leq_use_env)
            apply (rule_tac r_sb="diff_use_env r_s3 r_exa" in trans_leq_use_env)
             apply (rule_tac dist_diff_leq_use_env)
             apply (simp_all)
            apply (rule_tac r_sb="lift_use_env rx2 r" in trans_leq_use_env)
             apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
              apply (simp_all)
           apply (rule_tac self_lift_leq_use_env)
          apply (rule_tac r_sb="diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) r_x2)
              r_exb" in trans_leq_use_env)
           apply (simp)
          apply (rule_tac r_s="r_s" in crush_leq_use_env)
            apply (rule_tac r_sb="super_norm_use_env r_s r_s3" in trans_leq_use_env)
             apply (simp)
             apply (rule_tac dist_diff_leq_use_env_gen)
              apply (rule_tac id_leq_use_env)
             apply (rule_tac self_comp_leq_use_env2)
            apply (rule_tac rhs_snorm_leq_use_env)
             apply (rule_tac self_diff_leq_use_env)
            apply (rule_tac r_sb="diff_use_env r_s3 r_exa" in trans_leq_use_env)
             apply (rule_tac self_diff_leq_use_env)
            apply (simp)
           apply (rule_tac r_sb="dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) r_s2" in trans_leq_use_env)
            apply (rule_tac r_sb="diff_use_env r_s r_exaa" in trans_leq_use_env)
             apply (rule_tac self_diff_leq_use_env)
            apply (simp)
           apply (rule_tac infer_x_leq_use_env)
           apply (auto)
          apply (rule_tac self_diff_leq_use_env)
    (* > finishing the case *)
        apply (rule_tac dist_diff_leq_use_env)
        apply (rule_tac if_zero_leq_var_env)
         apply (rule_tac id_leq_use_env)
    (* - (t_sub, p_sub)( M1* ) \<le> EX. r_s - r_ex <= r_s3 <=  r_s1 - (r_exaa + r_exb) *)
        apply (rule_tac r_sb="cut_use_env (comp_use_env r_exaa r_exb)" in trans_leq_use_env)
         apply (rule_tac r_s="r_s" in dist_diff_leq_use_env_rev)
          apply (rule_tac dist_comp_leq_use_env)
           apply (simp)
          apply (rule_tac r_sb="diff_use_env r_s r_exaa" in trans_leq_use_env)
           apply (rule_tac self_diff_leq_use_env)
          apply (simp)
         apply (rule_tac r_sb="diff_use_env r_s3 r_exa" in trans_leq_use_env)
          apply (rule_tac diff_leq_use_env)
          apply (rule_tac r_sb="super_norm_use_env r_s r_s3" in trans_leq_use_env)
           apply (simp)
           apply (rule_tac id_leq_use_env)
          apply (rule_tac rhs_snorm_leq_use_env)
           apply (simp)
          apply (rule_tac id_leq_use_env)
         apply (simp)
        apply (rule_tac rhs_cut_leq_use_env)
        apply (simp add: comp_sol_subst_penv)
        apply (simp add: dist_cut_comp_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac comp_leq_use_env1)
         apply (simp add: dir_list_append_eq)
        apply (rule_tac comp_leq_use_env2)
        apply (simp add: dir_list_append_eq)
    (* - type equivalences *)
       apply (simp add: dir_list_append_eq)
      apply (simp add: dir_list_append_eq)
    (* - pair permission *)
     apply (simp add: add_use_env_def)
    (* - further type equivalence *)
    apply (rule_tac x="t1" in exI)
    apply (simp add: dir_list_append_eq)
    apply (simp add: add_use_env_def)
    apply (case_tac "req_type t2")
      apply (auto)
      apply (case_tac "req_type t1")
        apply (auto)
      apply (case_tac r)
        apply (auto)
     apply (case_tac "req_type t1")
       apply (auto)
    apply (case_tac "req_type t1")
      apply (simp_all)
   apply (rule_tac x="t2" in exI)
   apply (simp add: dir_list_append_eq)
   apply (simp add: add_use_env_def)
   apply (case_tac "req_type t1")
     apply (auto)
     apply (case_tac "req_type t2")
       apply (simp_all)
     apply (case_tac r)
       apply (simp_all)
    apply (case_tac "req_type t2")
      apply (simp_all)
   apply (case_tac "req_type t2")
     apply (simp_all)
      (* - solution satisfiability. disjointness *)
  apply (rule_tac sol_sat_split)
   apply (rule_tac sol_sat_disj)
   apply (simp add: dir_list_append_eq)
   apply (rule_tac r_s="comp_use_env (lift_use_env rx1 r) (cut_use_env r_exaa)" in disj_leq_use_env1)
    apply (rule_tac r_s="comp_use_env (lift_use_env rx2 r) (cut_use_env r_exb)" in disj_leq_use_env2)
     apply (rule_tac disj_comp_use_env1)
      apply (rule_tac disj_comp_use_env2)
       apply (simp)
      apply (rule_tac cut_disj_use_env)
      apply (rule_tac r_s="diff_use_env r_s r_exb" in mini_disj_leq_use_env2)
       apply (rule_tac mini_disj_diff_use_env)
      apply (rule_tac r_sb="super_norm_use_env r_s r_s3" in trans_leq_use_env)
       apply (simp)
       apply (rule_tac dist_diff_leq_use_env_gen)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac self_comp_leq_use_env2)
      apply (rule_tac rhs_snorm_leq_use_env2)
       apply (simp_all)
     apply (rule_tac disj_comp_use_env2)
      apply (rule_tac comm_disj_use_env)
      apply (rule_tac cut_disj_use_env)
      apply (rule_tac r_s="diff_use_env r_s r_exaa" in mini_disj_leq_use_env2)
       apply (rule_tac mini_disj_diff_use_env)
      apply (rule_tac r_sb="super_norm_use_env r_s r_s3" in trans_leq_use_env)
       apply (simp)
       apply (rule_tac dist_diff_leq_use_env_gen)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac self_comp_leq_use_env1)
      apply (rule_tac rhs_snorm_leq_use_env2)
       apply (simp_all)
     apply (rule_tac comm_disj_use_env)
     apply (rule_tac cut_disj_use_env)
     apply (rule_tac r_s="diff_use_env r_s r_exaa" in mini_disj_leq_use_env2)
      apply (rule_tac mini_disj_diff_use_env)
     apply (rule_tac cut_leq_use_env)
     apply (simp)
    (* > proving the inequality for r_x2 vs rx2 *)
    apply (rule_tac st_diff_comp_leq_use_env)
    apply (rule_tac r_sb="diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la)
      (add_use_env (comp_use_env p_sub p_suba) p r) (lift_var_env r_x2 (SVar p))) r_exb" in trans_leq_use_env)
     apply (rule_tac s="lift_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) r_x2)
         (add_use_env (comp_use_env p_sub p_suba) p r p)" and
      t="dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) (lift_var_env r_x2 (SVar p))" in subst)
      apply (simp add: lift_sol_subst_penvx)
     apply (simp add: lift_diff_use_env)
     apply (rule_tac r_sb="lift_use_env (diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la)
      (add_use_env (comp_use_env p_sub p_suba) p r) r_x2) r_exb) r" in trans_leq_use_env)
      apply (rule_tac dist_lift_leq_use_env)
      apply (simp)(*
      apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_s_sub_range)
       apply (auto)
      apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and p_sub="comp_use_env p_sub p_suba" and
        r_xv="r_x2" and ds="set_diff ds3 ds2" and x="p" and r="r" in add_psub_use_env)
           apply (auto)
       apply (simp add: set_diff_def)
        apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and ?p_sub1.0="p_suba" and ?p_sub2.0="p_sub" and
          r_xv="r_x2" and ds="set_diff ds3 ds2" and ds'="set_diff ds2 ds" in comp_psub_use_env2)
         apply (simp_all)
       apply (simp add: set_diff_def)
       apply (auto)*)
     apply (rule_tac dist_lift_leq_use_env_gen)
     apply (simp add: add_use_env_def)
     apply (case_tac r)
       apply (simp_all)
    apply (rule_tac dist_diff_leq_use_env_cut)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac id_leq_use_env)
    (* > proving the inequality for r_x1 vs rx1 *)
    apply (rule_tac st_diff_comp_leq_use_env)
   apply (rule_tac r_sb="diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la)
      (add_use_env (comp_use_env p_sub p_suba) p r) (lift_var_env r_x1 (SVar p))) r_exaa" in trans_leq_use_env)
    apply (rule_tac t="dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) (lift_var_env r_x1 (SVar p))"
      and s="lift_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) (add_use_env (comp_use_env p_sub p_suba) p r) r_x1)
         (add_use_env (comp_use_env p_sub p_suba) p r p)" in subst)
     apply (simp add: lift_sol_subst_penvx)
    apply (simp add: lift_diff_use_env)
    apply (rule_tac r_sb="lift_use_env (diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la)
      (add_use_env (comp_use_env p_sub p_suba) p r) r_x1) r_exaa) r" in trans_leq_use_env)
     apply (rule_tac dist_lift_leq_use_env)
     apply (simp)
    apply (rule_tac dist_lift_leq_use_env_gen)
    apply (simp add: add_use_env_def)
    apply (case_tac r)
      apply (simp_all)
   apply (rule_tac dist_diff_leq_use_env_cut)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac id_leq_use_env)
    (* > semi-disjointness 1 *)
  apply (simp add: dir_list_append_eq)
  apply (rule_tac sol_sat_split)
  apply (rule_tac sol_sat_mini_disj)
   apply (rule_tac cut_mini_disj_use_env)
   apply (rule_tac r_s="r_exb" in mini_disj_leq_use_env1)
    apply (rule_tac r_s="diff_use_env r_s r_exb" in mini_disj_leq_use_env2)
     apply (rule_tac mini_disj_diff_use_env)
    apply (rule_tac r_sb="comp_use_env (diff_use_env r_s r_exb) (cut_use_env r_exaa)" in trans_leq_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac swap_diff_cut_leq_use_env)
      apply (simp_all)
   apply (rule_tac st_diff_comp_leq_use_env)
   apply (rule_tac r_sb="diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la)
      (add_use_env (comp_use_env p_sub p_suba) p r) r_x1) r_exaa" in trans_leq_use_env)
    apply (rule_tac r_sb="lift_use_env rx1 r" in trans_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (rule_tac mini_disj_diff_leq_use_env2)
       apply (simp)
      apply (rule_tac r_s="diff_use_env r_s r_exb" in mini_disj_leq_use_env2)
       apply (rule_tac mini_disj_diff_use_env)
      apply (rule_tac r_sb="super_norm_use_env r_s r_s3" in trans_leq_use_env)
       apply (simp)
       apply (rule_tac dist_diff_leq_use_env_gen)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac self_comp_leq_use_env2)
      apply (rule_tac rhs_snorm_leq_use_env2)
       apply (rule_tac id_leq_use_env)
      apply (simp_all)
    apply (rule_tac lift_leq_use_env)
    apply (simp)
   apply (rule_tac dist_diff_leq_use_env_cut)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac id_leq_use_env)
    (* > semi-disjointness 2 *)
  apply (rule_tac sol_sat_split)
   apply (rule_tac sol_sat_mini_disj)
   apply (rule_tac cut_mini_disj_use_env)
   apply (rule_tac r_s="r_exaa" in mini_disj_leq_use_env1)
    apply (rule_tac r_s="diff_use_env r_s r_exaa" in mini_disj_leq_use_env2)
     apply (rule_tac mini_disj_diff_use_env)
    apply (simp_all)
    (* > constraint list 1 correctness *)
  apply (rule_tac sol_sat_split)
   apply (cut_tac c_list="cl1" and ds="ds" and ds'="ds2" in infer_tvar_crn_list)
     apply (auto)
   apply (cut_tac c_list="cl1" and ds="ds" and ds'="ds2" in infer_pvar_crn_list)
     apply (auto)
   apply (rule_tac dir_list_add_sol_sat)
    apply (rule_tac add_psub_sol_sat)
     apply (rule_tac ds="set_diff ds2 ds" in comp_psub_sol_sat1)
        apply (simp_all)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (case_tac "p \<in> ds2")
     apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
      apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac x="x" and l="la" in dom_list_set_contain)
    apply (auto)
   apply (simp add: fresh_list_def)
   apply (auto)
    (* > constraint list 2 correctness *)
  apply (cut_tac c_list="cl2" and ds="ds2" and ds'="ds3" in infer_pvar_crn_list)
    apply (auto)
   apply (rule_tac ds="ds" in subset_sub_range)
    apply (auto)
   apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
    apply (auto)
  apply (rule_tac add_psub_sol_sat)
   apply (rule_tac ds="set_diff ds3 ds2" in comp_psub_sol_sat2)
      apply (simp_all)
   apply (simp add: set_diff_def)
   apply (auto)
  apply (case_tac "p \<in> ds2")
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
  apply (simp add: set_diff_def)
  apply (auto)
  done

    
lemma ivr_pair_case: "\<lbrakk>\<And>tau r_s r_x r_ex env env_v ds tau_v r_sv r_xv r_mv c_list ds' t_sub.
           \<lbrakk>well_typed env id r_s e1 tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e1 tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds\<rbrakk>
           \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list);
        \<And>tau r_s r_x r_ex env env_v ds tau_v r_sv r_xv r_mv c_list ds' t_sub.
           \<lbrakk>well_typed env id r_s e2 tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e2 tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds\<rbrakk>
           \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list);
        spec_env env_v env t_sub; sub_range env_v ds; tsub_dom t_sub ds; infer_type env_v ds e1 t1a r_s1 r_x1 r_m1 cl1 ds2; well_typed env id r_s e1 t1 r_s2a rx1;
        infer_type env_v ds2 e2 t2a r_s2 r_x2 r_m2 cl2 ds3; well_typed env id r_s2a e2 t2 r_s3 rx2; leq_use_env (lift_use_env rx1 r) r_s3;
        leq_use_env (lift_use_env rx2 r) r_s3; aff_leq (max_aff (req_type t1) (req_type t2)) r; disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r);
        finite_dom (comp_var_env (comp_var_env r_s1 (lift_var_env r_x1 (SVar p))) (comp_var_env r_s2 (lift_var_env r_x2 (SVar p)))) d;
        leq_use_env (diff_use_env r_s r_ex) (diff_use_env r_s3 r_exa); leq_use_env r_x (diff_use_env r_s r_ex); p \<notin> ds3; leq_use_env r_exa r_s;
        leq_use_env (pair_req (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_exa (PairTy t1 t2 r)) r_x\<rbrakk>
       \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) (insert p ds3) \<and>
               fresh_list ds (dom_list l) \<and>
               dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
               (\<exists>p_sub. psub_dom p_sub (set_diff (insert p ds3) ds) \<and>
                        leq_use_env
                         (dir_subst_penv (dir_list_add_env t_sub l) p_sub
                           (comp_var_env (comp_var_env r_s1 (lift_var_env r_x1 (SVar p))) (comp_var_env r_s2 (lift_var_env r_x2 (SVar p)))))
                         r_s \<and>
                        leq_use_env
                         (diff_use_env
                           (dir_subst_penv (dir_list_add_env t_sub l) p_sub
                             (ifz_var_env (XPerm (SVar p)) (comp_var_env (lift_var_env r_x1 (SVar p)) (lift_var_env r_x2 (SVar p)))))
                           r_ex)
                         r_x \<and>
                        leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub (comp_var_env r_m1 r_m2))) r_ex \<and>
                        dir_subst_type (dir_list_add_env t_sub l) p_sub t1a t1 \<and>
                        dir_subst_type (dir_list_add_env t_sub l) p_sub t2a t2 \<and>
                        r = p_sub p \<and>
                        (\<exists>tau_x. dir_subst_type (dir_list_add_env t_sub l) p_sub t1a tau_x \<and> aff_leq (req_type tau_x) (p_sub p)) \<and>
                        (\<exists>tau_x. dir_subst_type (dir_list_add_env t_sub l) p_sub t2a tau_x \<and> aff_leq (req_type tau_x) (p_sub p)) \<and>
                        dir_sol_sat (dir_list_add_env t_sub l) p_sub
                         (disj_crn (lift_var_env r_x1 (SVar p)) (lift_var_env r_x2 (SVar p)) d @
                          semi_disj_crn r_m2 r_x1 d @ semi_disj_crn r_m1 r_s2 d @ cl1 @ cl2))"
  apply (cut_tac env="env" and ?e1.0="e1" and ?e2.0="e2" in ivr_induct_format)
    apply (auto)
  apply (cut_tac e="e1" and env_v="env_v" and t_sub="t_sub" and ds="ds" in ivrpc_coerce)
        apply (auto)
  apply (cut_tac e="e2" and env_v="env_v" and t_sub="dir_list_add_env t_sub l" and ds="ds2" in ivrpc_coerce)
        apply (auto)
    apply (rule_tac self_spec_env)
   apply (rule_tac ds="ds" in subset_sub_range)
    apply (simp)
   apply (rule_tac infer_x_subset)
   apply (auto)
  apply (rule_tac env_v="env_v" and r_s="r_s" and ?r_s3.0="r_s3" and ?e1.0="e1" and ?e2.0="e2" 
      and ?r_s1.0="r_s1" and ?r_x1.0="r_x1" and ?r_m1.0="r_m1" and ?r_s2.0="r_s2" and ?r_x2.0="r_x2" and ?r_m2.0="r_m2" in ivrpc_main)
                      apply (auto)
  apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  apply (rule_tac well_typed_perm_leq)
  apply (auto)
  done 
    

lemma ivric_coerce: "\<lbrakk> \<And>tau r_s r_x r_ex env env_v ds tau_v r_sv r_xv r_mv c_list ds' t_sub.
           \<lbrakk>well_typed env id r_s e tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds\<rbrakk>
           \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list);
    well_typed env id r_s e tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds \<rbrakk> \<Longrightarrow>
  \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list)"    
  apply (auto)
  done
  
lemma subset_fresh_list: "\<lbrakk> ds \<subseteq> ds'; fresh_list ds' l \<rbrakk> \<Longrightarrow> fresh_list ds l"    
  apply (simp add: fresh_list_def)
  apply (auto)
  done

lemma ivric_main: "\<lbrakk> spec_env env_v (dir_subst_tenv (dir_list_add_env t_sub l) env_v) t_sub; sub_range env_v ds; tsub_dom t_sub ds;
        well_typed (dir_subst_tenv (dir_list_add_env t_sub l) env_v) id r_s e1 BoolTy r_s2 rx'; infer_type env_v ds e1 t1 r_s1 r_x1 r_m1 cl1 ds2;
        well_typed (dir_subst_tenv (dir_list_add_env t_sub l) env_v) id r_s2 e2 tau (diff_use_env r_s r_ex) rx1; infer_type env_v ds2 e2 t2 r_s2a r_x2 r_m2 cl2 ds3;
        well_typed (dir_subst_tenv (dir_list_add_env t_sub l) env_v) id r_s2 e3 tau (diff_use_env r_s r_ex) rx2; infer_type env_v ds3 e3 t3 r_s3 r_x3 r_m3 cl3 ds';
        finite_dom (comp_var_env r_s1 (comp_var_env r_s2a r_s3)) d; super_norm_use_env r_s r_s2 = diff_use_env r_s r_exa; leq_use_env r_exa r_s;
        tsub_dom (dir_list_add_env t_sub l) ds2; fresh_list ds (dom_list l); env = dir_subst_tenv (dir_list_add_env t_sub l) env_v;
        psub_dom p_sub (set_diff ds2 ds); leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_s1) r_s;
        leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_x1) r_exa) rx';
        leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_m1)) r_exa; dir_subst_type (dir_list_add_env t_sub l) p_sub t1 BoolTy;
        dir_sol_sat (dir_list_add_env t_sub l) p_sub cl1; tsub_dom (dir_list_add_env (dir_list_add_env t_sub l) la) ds3; fresh_list ds2 (dom_list la);
        dir_subst_tenv (dir_list_add_env (dir_list_add_env t_sub l) la) env_v = dir_subst_tenv (dir_list_add_env t_sub l) env_v;
        psub_dom p_suba (set_diff ds3 ds2); leq_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba r_s2a) r_s2;
        leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba r_x2) r_ex) rx1;
        leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba r_m2)) r_ex;
        dir_subst_type (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba t2 tau; dir_sol_sat (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba cl2;
        tsub_dom (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb) ds'; fresh_list ds3 (dom_list lb);
        dir_subst_tenv (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb) env_v = dir_subst_tenv (dir_list_add_env t_sub l) env_v;
        psub_dom p_subb (set_diff ds' ds3); leq_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb) p_subb r_s3) r_s2;
        leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb) p_subb r_x3) r_ex) rx2;
        leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb) p_subb r_m3)) r_ex;
        dir_subst_type (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb) p_subb t3 tau;
        dir_sol_sat (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb) p_subb cl3\<rbrakk>
       \<Longrightarrow> \<exists>la. tsub_dom (dir_list_add_env t_sub la) ds' \<and>
                fresh_list ds (dom_list la) \<and>
                dir_subst_tenv (dir_list_add_env t_sub la) env_v = dir_subst_tenv (dir_list_add_env t_sub l) env_v \<and>
                (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                         leq_use_env (dir_subst_penv (dir_list_add_env t_sub la) p_sub (comp_var_env r_s1 (comp_var_env r_s2a r_s3))) r_s \<and>
                         leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub la) p_sub (comp_var_env r_x2 r_x3)) r_ex) (comp_use_env rx1 rx2) \<and>
                         leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub la) p_sub (comp_var_env r_m1 (comp_var_env r_m2 r_m3)))) r_ex \<and>
                         dir_subst_type (dir_list_add_env t_sub la) p_sub t2 tau \<and>
                         dir_subst_type (dir_list_add_env t_sub la) p_sub t1 BoolTy \<and>
                         (\<exists>tau_x. dir_subst_type (dir_list_add_env t_sub la) p_sub t2 tau_x \<and> dir_subst_type (dir_list_add_env t_sub la) p_sub t3 tau_x) \<and>
                         dir_sol_sat (dir_list_add_env t_sub la) p_sub (semi_disj_crn r_m1 (comp_var_env r_s2a r_s3) d @ cl1 @ cl2 @ cl3))"
    (* P* inequality 1 *)
  apply (case_tac "\<not> leq_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb)
    (comp_use_env p_sub (comp_use_env p_suba p_subb)) r_s1) r_s")
   apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_tvar_range)
     apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and l="lb" and p_sub="comp_use_env p_sub (comp_use_env p_suba p_subb)"
                and r_sv="r_s1" and ds="ds2" in dir_list_add_cancel_use_env)
     apply (auto)
    apply (rule_tac ds'="ds3" in subset_fresh_list)
     apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and l="la" and p_sub="comp_use_env p_sub (comp_use_env p_suba p_subb)"
                and r_sv="r_s1" and ds="ds2" in dir_list_add_cancel_use_env)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_s_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and ?p_sub1.0="p_sub" and ?p_sub2.0="comp_use_env p_suba p_subb"
      and r_xv="r_s1" and ds="set_diff ds2 ds" and ds'="set_diff ds' ds2" in comp_psub_use_env1)
      apply (auto)
    apply (rule_tac comp_psub_dom)
     apply (rule_tac ds="set_diff ds3 ds2" in subset_psub_dom)
      apply (simp)
     apply (simp add: set_diff_def)
    apply (auto)
    apply (rule_tac ds="set_diff ds' ds3" in subset_psub_dom)
     apply (simp)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (simp add: set_diff_def)
    (* P* inequality 2 *)
  apply (case_tac "\<not> leq_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb)
    (comp_use_env p_sub (comp_use_env p_suba p_subb)) r_s2a) r_s2")
   apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
     apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_tvar_range)
     apply (auto)
   apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and l="lb" and p_sub="comp_use_env p_sub (comp_use_env p_suba p_subb)"
                and r_sv="r_s2a" and ds="ds3" in dir_list_add_cancel_use_env)
     apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_s_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and ?p_sub2.0="p_sub" and ?p_sub1.0="comp_use_env p_suba p_subb"
      and r_xv="r_s2a" and ds'="set_diff ds2 ds" and ds="set_diff ds' ds2" in comp_psub_use_env2)
      apply (auto)
     apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
      apply (simp)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and ?p_sub1.0="p_suba" and ?p_sub2.0="p_subb"
      and r_xv="r_s2a" and ds="set_diff ds3 ds2" and ds'="set_diff ds' ds3" in comp_psub_use_env1)
      apply (auto)
   apply (simp add: set_diff_def)
    (* P* inequality 3 *)
  apply (case_tac "\<not> leq_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb)
    (comp_use_env p_sub (comp_use_env p_suba p_subb)) r_s3) r_s2")
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds3" and e="e3" and ds'="ds'" in infer_s_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb" and ?p_sub2.0="p_sub" and
      ?p_sub1.0="comp_use_env p_suba p_subb" and r_xv="r_s3" and ds'="set_diff ds2 ds" and ds="set_diff ds' ds2" in comp_psub_use_env2)
      apply (auto)
     apply (rule_tac ds="set_diff ds' ds3" in subset_pvar_range)
      apply (simp)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb" and ?p_sub2.0="p_suba" and ?p_sub1.0="p_subb"
      and r_xv="r_s3" and ds'="set_diff ds3 ds2" and ds="set_diff ds' ds3" in comp_psub_use_env2)
      apply (auto)
   apply (simp add: set_diff_def)
    (* X* inequality 2 *)
  apply (case_tac "\<not> leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb)
    (comp_use_env p_sub (comp_use_env p_suba p_subb)) r_x2) r_ex) rx1")
   apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
     apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_tvar_range)
     apply (auto)
   apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and l="lb" and p_sub="comp_use_env p_sub (comp_use_env p_suba p_subb)"
                and r_sv="r_x2" and ds="ds3" in dir_list_add_cancel_use_env)
     apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_s_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and ?p_sub2.0="p_sub" and ?p_sub1.0="comp_use_env p_suba p_subb"
      and r_xv="r_x2" and ds'="set_diff ds2 ds" and ds="set_diff ds' ds2" in comp_psub_use_env2)
      apply (auto)
     apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
      apply (simp)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and ?p_sub1.0="p_suba" and ?p_sub2.0="p_subb"
      and r_xv="r_x2" and ds="set_diff ds3 ds2" and ds'="set_diff ds' ds3" in comp_psub_use_env1)
      apply (auto)
   apply (simp add: set_diff_def)
    (* X* inequality 3 *)
  apply (case_tac "\<not> leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb)
    (comp_use_env p_sub (comp_use_env p_suba p_subb)) r_x3) r_ex) rx2")
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds3" and e="e3" and ds'="ds'" in infer_s_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb" and ?p_sub2.0="p_sub" and
      ?p_sub1.0="comp_use_env p_suba p_subb" and r_xv="r_x3" and ds'="set_diff ds2 ds" and ds="set_diff ds' ds2" in comp_psub_use_env2)
      apply (auto)
     apply (rule_tac ds="set_diff ds' ds3" in subset_pvar_range)
      apply (simp)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb" and ?p_sub2.0="p_suba" and ?p_sub1.0="p_subb"
      and r_xv="r_x3" and ds'="set_diff ds3 ds2" and ds="set_diff ds' ds3" in comp_psub_use_env2)
      apply (auto)
   apply (simp add: set_diff_def)
    (* M* inequality 1 *)
  apply (case_tac "\<not> leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb)
    (comp_use_env p_sub (comp_use_env p_suba p_subb)) r_m1)) r_exa")
   apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_m_tvar_range)
     apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and l="lb" and p_sub="comp_use_env p_sub (comp_use_env p_suba p_subb)"
                and r_sv="r_m1" and ds="ds2" in dir_list_add_cancel_use_env)
     apply (auto)
    apply (rule_tac ds'="ds3" in subset_fresh_list)
     apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and l="la" and p_sub="comp_use_env p_sub (comp_use_env p_suba p_subb)"
                and r_sv="r_m1" and ds="ds2" in dir_list_add_cancel_use_env)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_m_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and ?p_sub1.0="p_sub" and ?p_sub2.0="comp_use_env p_suba p_subb"
      and r_xv="r_m1" and ds="set_diff ds2 ds" and ds'="set_diff ds' ds2" in comp_psub_use_env1)
      apply (auto)
    apply (rule_tac comp_psub_dom)
     apply (rule_tac ds="set_diff ds3 ds2" in subset_psub_dom)
      apply (simp)
     apply (simp add: set_diff_def)
    apply (auto)
    apply (rule_tac ds="set_diff ds' ds3" in subset_psub_dom)
     apply (simp)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (simp add: set_diff_def)
    (* M* inequality 2 *)
  apply (case_tac "\<not> leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb)
    (comp_use_env p_sub (comp_use_env p_suba p_subb)) r_m2)) r_ex")
   apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
     apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_m_tvar_range)
     apply (auto)
   apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and l="lb" and p_sub="comp_use_env p_sub (comp_use_env p_suba p_subb)"
                and r_sv="r_m2" and ds="ds3" in dir_list_add_cancel_use_env)
     apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_m_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and ?p_sub2.0="p_sub" and ?p_sub1.0="comp_use_env p_suba p_subb"
      and r_xv="r_m2" and ds'="set_diff ds2 ds" and ds="set_diff ds' ds2" in comp_psub_use_env2)
      apply (auto)
     apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
      apply (simp)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and ?p_sub1.0="p_suba" and ?p_sub2.0="p_subb"
      and r_xv="r_m2" and ds="set_diff ds3 ds2" and ds'="set_diff ds' ds3" in comp_psub_use_env1)
      apply (auto)
   apply (simp add: set_diff_def)
    (* M* inequality 3 *)
  apply (case_tac "\<not> leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb)
    (comp_use_env p_sub (comp_use_env p_suba p_subb)) r_m3)) r_ex")
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds3" and e="e3" and ds'="ds'" in infer_m_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb" and ?p_sub2.0="p_sub" and
      ?p_sub1.0="comp_use_env p_suba p_subb" and r_xv="r_m3" and ds'="set_diff ds2 ds" and ds="set_diff ds' ds2" in comp_psub_use_env2)
      apply (auto)
     apply (rule_tac ds="set_diff ds' ds3" in subset_pvar_range)
      apply (simp)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb" and ?p_sub2.0="p_suba" and ?p_sub1.0="p_subb"
      and r_xv="r_m3" and ds'="set_diff ds3 ds2" and ds="set_diff ds' ds3" in comp_psub_use_env2)
      apply (auto)
   apply (simp add: set_diff_def)
    (* proving type equivalence for t2 *)
  apply (case_tac "\<not> dir_subst_type (dir_list_add_env t_sub (lb @ la @ l)) (comp_use_env p_sub (comp_use_env p_suba p_subb)) t2 tau")
   apply (simp add: dir_list_append_eq)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
     apply (simp)
    apply (rule_tac infer_x_subset)
    apply (simp)
   apply (cut_tac tau_v="t2" and ds="ds2" and ds'="ds3" in infer_pvar_type)
     apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and l="lb" and p_sub="comp_use_env p_sub (comp_use_env p_suba p_subb)" and
        tau_v="t2" and tau="tau" in dir_list_add_subst_type)
     apply (rule_tac ds="set_diff ds' ds2" in comp_dir_subst_type2)
        apply (rule_tac ds="set_diff ds3 ds2" in comp_dir_subst_type1)
           apply (auto)
      apply (simp add: set_diff_def)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac x="x" and l="lb" in dom_list_contain)
    apply (simp)
   apply (cut_tac tau_v="t2" and ds'="ds3" and ds="ds2" in infer_tvar_type)
     apply (auto)
   apply (simp add: fresh_list_def)
   apply (auto)
    (* proving type equivalence for t3 *)
  apply (case_tac "\<not> dir_subst_type (dir_list_add_env t_sub (lb @ la @ l)) (comp_use_env p_sub (comp_use_env p_suba p_subb)) t3 tau")
   apply (simp add: dir_list_append_eq)
   apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
    apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds3" in subset_sub_range)
     apply (auto)
   apply (cut_tac tau_v="t3" and ds="ds3" and ds'="ds'" in infer_pvar_type)
     apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) lb" and
      p_sub="p_sub" and p_subx="comp_use_env p_suba p_subb" and ds="set_diff ds' ds2" in comp_dir_subst_type2)
       apply (rule_tac ds="set_diff ds' ds3" in comp_dir_subst_type2)
          apply (auto)
     apply (simp add: set_diff_def)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (simp add: set_diff_def)
  apply (rule_tac x="lb @ la @ l" in exI)
  apply (auto)
    (* type subst domain containment *)
     apply (simp add: dir_list_append_eq)
    (* freshness of lb, la, l *)
    apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (auto)
    apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
     apply (auto)
    apply (rule_tac t_sub="t_sub" and ds="ds" and ds'="ds3" in append_fresh_list2)
       apply (auto)
     apply (rule_tac ds="ds" and ds'="ds2" in append_fresh_list2)
        apply (auto)
    apply (simp add: dir_list_append_eq)
    (* tenv equality *)
   apply (simp add: dir_list_append_eq)
    (* defining new p_sub *)
  apply (rule_tac x="comp_use_env p_sub (comp_use_env p_suba p_subb)" in exI)
  apply (auto)
    (* p_sub containment *)
       apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
        apply (auto)
       apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
        apply (auto)
       apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
        apply (auto)
       apply (rule_tac comp_psub_dom)
        apply (rule_tac ds="set_diff ds2 ds" in subset_psub_dom)
         apply (simp)
        apply (rule_tac set_diff_subset)
         apply (auto)
       apply (rule_tac comp_psub_dom)
        apply (rule_tac ds="set_diff ds3 ds2" in subset_psub_dom)
         apply (simp)
        apply (rule_tac set_diff_subset)
         apply (auto)
       apply (rule_tac ds="set_diff ds' ds3" in subset_psub_dom)
        apply (simp)
       apply (rule_tac set_diff_subset)
        apply (auto)
    (* initial permission environment containment *)
      apply (simp add: dir_list_append_eq)
      apply (simp add: comp_sol_subst_penv)
      apply (rule_tac dist_comp_leq_use_env)
       apply (simp)
      apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (rule_tac dist_comp_leq_use_env)
       apply (simp_all)
    (* requirements containment *)
     apply (simp add: dir_list_append_eq)
     apply (simp add: comp_sol_subst_penv)
     apply (rule_tac lhs_dist_dcl_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac comp_leq_use_env1)
      apply (simp)
     apply (rule_tac comp_leq_use_env2)
     apply (simp)
    (* subtractant containment *)
    apply (simp add: dir_list_append_eq)
    apply (simp add: comp_sol_subst_penv)
    apply (rule_tac lhs_dist_cut_leq_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac r_sb="cut_use_env r_exa" in trans_leq_use_env)
      apply (rule_tac r_s="r_s" in dist_diff_leq_use_env_rev)
       apply (simp)
      apply (rule_tac t="diff_use_env r_s r_exa" and s="super_norm_use_env r_s r_s2" in subst)
       apply (simp)
      apply (rule_tac rhs_snorm_leq_use_env2)
       apply (rule_tac well_typed_perm_leq)
       apply (simp)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (rule_tac rhs_cut_leq_use_env)
     apply (simp)
    apply (rule_tac lhs_dist_cut_leq_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (simp_all)
    (* type equivalence *)
   apply (simp add: dir_list_append_eq)
   apply (cut_tac tau_v="t1" and ds="ds" and ds'="ds2" in infer_pvar_type)
     apply (auto)
   apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
    apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
     apply (simp_all)
   apply (cut_tac tau_v="t1" and ds'="ds2" and ds="ds" in infer_tvar_type)
     apply (auto)
   apply (rule_tac dir_list_add_subst_type)
    apply (rule_tac dir_list_add_subst_type)
     apply (rule_tac ds="set_diff ds2 ds" and ds'="set_diff ds' ds2" in comp_dir_subst_type1)
        apply (simp_all)
      apply (rule_tac comp_psub_dom)
       apply (rule_tac ds="set_diff ds3 ds2" in subset_psub_dom)
        apply (simp)
       apply (simp add: set_diff_def)
       apply (auto)
      apply (rule_tac ds="set_diff ds' ds3" in subset_psub_dom)
       apply (simp)
      apply (simp add: set_diff_def)
      apply (auto)
     apply (simp add: set_diff_def)
    apply (cut_tac x="x" and l="la" in dom_list_contain)
     apply (simp)
    apply (simp add: fresh_list_def)
    apply (auto)
   apply (cut_tac x="x" and l="lb" in dom_list_contain)
    apply (simp)
   apply (simp add: fresh_list_def)
   apply (auto)
    (* constraint list correctness. disjointness *)
  apply (simp add: dir_list_append_eq)
  apply (rule_tac sol_sat_split)
   apply (rule_tac sol_sat_mini_disj)
   apply (rule_tac cut_mini_disj_use_env)
   apply (rule_tac r_s="r_exa" in mini_disj_leq_use_env1)
    apply (rule_tac r_s="diff_use_env r_s r_exa" in mini_disj_leq_use_env2)
     apply (rule_tac mini_disj_diff_use_env)
    apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
     apply (rule_tac t="diff_use_env r_s r_exa" and s="super_norm_use_env r_s r_s2" in subst)
      apply (simp)
     apply (rule_tac rhs_snorm_leq_use_env2)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
   apply (simp add: comp_sol_subst_penv)
   apply (rule_tac dist_comp_leq_use_env)
    apply (simp_all)
    (* - constraint list 1 correctness *)
  apply (rule_tac sol_sat_split)
   apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
    apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
    apply (auto)
   apply (cut_tac c_list="cl1" and ds="ds" and ds'="ds2" in infer_tvar_crn_list)
     apply (auto)
   apply (cut_tac c_list="cl1" and ds="ds" and ds'="ds2" in infer_pvar_crn_list)
     apply (auto)
   apply (rule_tac dir_list_add_sol_sat)
    apply (rule_tac dir_list_add_sol_sat)
     apply (rule_tac ds="set_diff ds2 ds" and ds'="set_diff ds' ds2" in comp_psub_sol_sat1)
        apply (simp_all)
      apply (rule_tac comp_psub_dom)
       apply (rule_tac ds="set_diff ds3 ds2" in subset_psub_dom)
        apply (simp)
       apply (simp add: set_diff_def)
       apply (auto)
      apply (rule_tac ds="set_diff ds' ds3" in subset_psub_dom)
       apply (simp)
      apply (simp add: set_diff_def)
      apply (auto)
     apply (simp add: set_diff_def)
    apply (cut_tac x="x" and l="la" in dom_list_set_contain)
     apply (auto)
    apply (simp add: fresh_list_def)
    apply (auto)
   apply (cut_tac x="x" and l="lb" in dom_list_set_contain)
    apply (auto)
   apply (simp add: fresh_list_def)
   apply (auto)
    (* - constraint list 2 correctness *)
  apply (rule_tac sol_sat_split)
   apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
    apply (auto)
   apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
     apply (auto)
   apply (cut_tac c_list="cl2" and ds="ds2" and ds'="ds3" in infer_tvar_crn_list)
     apply (auto)
   apply (cut_tac c_list="cl2" and ds="ds2" and ds'="ds3" in infer_pvar_crn_list)
     apply (auto)
   apply (rule_tac dir_list_add_sol_sat)
    apply (rule_tac ds="set_diff ds' ds2" and ds'="set_diff ds2 ds" in comp_psub_sol_sat2)
    apply (rule_tac ds="set_diff ds3 ds2" in comp_psub_sol_sat1)
          apply (simp_all)
      apply (simp add: set_diff_def)
      apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac x="x" and l="lb" in dom_list_set_contain)
    apply (auto)
   apply (simp add: fresh_list_def)
   apply (auto)
    (* - constraint list 3 correctness *)
   apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
    apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds3" in subset_sub_range)
     apply (auto)
   apply (cut_tac c_list="cl3" and ds="ds3" and ds'="ds'" in infer_tvar_crn_list)
     apply (auto)
   apply (cut_tac c_list="cl3" and ds="ds3" and ds'="ds'" in infer_pvar_crn_list)
     apply (auto)
  apply (rule_tac ds="set_diff ds' ds2" and ds'="set_diff ds2 ds" in comp_psub_sol_sat2)
     apply (rule_tac ds="set_diff ds' ds3" in comp_psub_sol_sat2)
        apply (simp_all)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (simp add: set_diff_def)
   apply (auto)
  apply (simp add: set_diff_def)
  done
    
    
lemma ivr_if_case: "\<lbrakk>\<And>tau r_s r_x r_ex env env_v ds tau_v r_sv r_xv r_mv c_list ds' t_sub.
           \<lbrakk>well_typed env id r_s e1 tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e1 tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds\<rbrakk>
           \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list);
        \<And>tau r_s r_x r_ex env env_v ds tau_v r_sv r_xv r_mv c_list ds' t_sub.
           \<lbrakk>well_typed env id r_s e2 tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e2 tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds\<rbrakk>
           \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list);
        \<And>tau r_s r_x r_ex env env_v ds tau_v r_sv r_xv r_mv c_list ds' t_sub.
           \<lbrakk>well_typed env id r_s e3 tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e3 tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds\<rbrakk>
           \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list);
        spec_env env_v env t_sub; sub_range env_v ds; tsub_dom t_sub ds; well_typed env id r_s e1 BoolTy r_s2 rx'; infer_type env_v ds e1 t1 r_s1 r_x1 r_m1 cl1 ds2;
        well_typed env id r_s2 e2 tau (diff_use_env r_s r_ex) rx1; infer_type env_v ds2 e2 t2 r_s2a r_x2 r_m2 cl2 ds3;
        well_typed env id r_s2 e3 tau (diff_use_env r_s r_ex) rx2; infer_type env_v ds3 e3 t3 r_s3 r_x3 r_m3 cl3 ds';
        finite_dom (comp_var_env r_s1 (comp_var_env r_s2a r_s3)) d\<rbrakk>
       \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
               fresh_list ds (dom_list l) \<and>
               dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
               (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                        leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub (comp_var_env r_s1 (comp_var_env r_s2a r_s3))) r_s \<and>
                        leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub (comp_var_env r_x2 r_x3)) r_ex) (comp_use_env rx1 rx2) \<and>
                        leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub (comp_var_env r_m1 (comp_var_env r_m2 r_m3)))) r_ex \<and>
                        dir_subst_type (dir_list_add_env t_sub l) p_sub t2 tau \<and>
                        dir_subst_type (dir_list_add_env t_sub l) p_sub t1 BoolTy \<and>
                        (\<exists>tau_x. dir_subst_type (dir_list_add_env t_sub l) p_sub t2 tau_x \<and> dir_subst_type (dir_list_add_env t_sub l) p_sub t3 tau_x) \<and>
                        dir_sol_sat (dir_list_add_env t_sub l) p_sub (semi_disj_crn r_m1 (comp_var_env r_s2a r_s3) d @ cl1 @ cl2 @ cl3))" 
  apply (cut_tac r_s="r_s" and r_x="r_s2" in snorm_diff_use_env)
  apply (auto)
  apply (cut_tac e="e1" and env="env" and env_v="env_v" and t_sub="t_sub" and ds="ds" and r_s="r_s" and r_ex="r_exa" in ivric_coerce)
        apply (auto)
   apply (cut_tac env="env" and ?r_s1.0="r_s" and ?r_s2.0="r_s2" and e="e1" in well_typed_sstr_end_perm)
    apply (auto)
  apply (cut_tac e="e2" and env="dir_subst_tenv (dir_list_add_env t_sub l) env_v" and env_v="env_v" and
      t_sub="dir_list_add_env t_sub l" and ds="ds2" and r_s="r_s2" and r_ex="r_ex" in ivric_coerce)
        apply (auto)
     apply (rule_tac r_c="diff_use_env r_s r_ex" in well_typed_decr_end_perm)
       apply (auto)
      apply (rule_tac dist_diff_leq_use_env)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (rule_tac mini_disj_diff_leq_use_env2)
      apply (rule_tac r_sb="diff_use_env r_s r_ex" in trans_leq_use_env)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (rule_tac well_typed_perm_leqx)
      apply (auto)
     apply (rule_tac r_s="diff_use_env r_s r_ex" in mini_disj_leq_use_env2)
      apply (rule_tac mini_disj_diff_use_env)
     apply (rule_tac well_typed_perm_leqx)
     apply (auto)
    apply (rule_tac self_spec_env)
   apply (rule_tac ds="ds" in subset_sub_range)
    apply (simp)
   apply (rule_tac infer_x_subset)
   apply (auto)
  apply (cut_tac e="e3" and env="dir_subst_tenv (dir_list_add_env (dir_list_add_env t_sub l) la) env_v" and env_v="env_v" and
      t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and ds="ds3" and r_s="r_s2" and r_ex="r_ex" in ivric_coerce)
        apply (auto)
     apply (rule_tac r_c="diff_use_env r_s r_ex" in well_typed_decr_end_perm)
       apply (auto)
      apply (rule_tac dist_diff_leq_use_env)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (rule_tac mini_disj_diff_leq_use_env2)
      apply (rule_tac r_sb="diff_use_env r_s r_ex" in trans_leq_use_env)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (rule_tac well_typed_perm_leqx)
      apply (auto)
     apply (rule_tac r_s="diff_use_env r_s r_ex" in mini_disj_leq_use_env2)
      apply (rule_tac mini_disj_diff_use_env)
     apply (rule_tac well_typed_perm_leqx)
     apply (auto)
    apply (rule_tac eq_spec_env)
    apply (auto)
   apply (rule_tac ds="ds" in subset_sub_range)
    apply (simp)
   apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
    apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
  apply (rule_tac env_v="env_v" and r_s="r_s" and ?r_s3.0="r_s3" and ?e1.0="e1" and ?e2.0="e2" and ?e3.0="e3"
      and ?r_s1.0="r_s1" and ?r_x1.0="r_x1" and ?r_m1.0="r_m1" and ?r_s2.0="r_s2" and ?r_x2.0="r_x2" and ?r_m2.0="r_m2"
      and ?r_s3.0="r_s3" and ?r_x3.0="r_x3" and ?r_m3.0="r_m3" and t_sub="t_sub" and p_sub="p_sub" and p_suba="p_suba"
      and p_subb="p_subb" and l="l" and la="la" and lb="lb" and ds="ds" and ?ds2.0="ds2" and ?ds3.0="ds3" and ds'="ds'" in ivric_main)
                      apply (auto)
  done
  
lemma ivrlc_coerce: "\<lbrakk> \<And>tau r_s r_x r_ex env env_v ds tau_v r_sv r_xv r_mv c_list ds' t_sub.
           \<lbrakk>well_typed env id r_s e tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds\<rbrakk>
           \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list);
    well_typed env id r_s e tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds \<rbrakk> \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list)"
  apply (auto)
  done
    
lemma add_spec_env: "\<lbrakk> sub_range env_v ds; a \<notin> ds; spec_env env_v env t_sub \<rbrakk> \<Longrightarrow>
  spec_env (add_env env_v x a) (add_env env x tau) (dir_add_env t_sub a tau)"    
  apply (simp add: spec_env_def)
  apply (simp add: add_env_def)
  apply (auto)
   apply (simp add: dir_add_env_def)
  apply (erule_tac x="xa" in allE)
  apply (case_tac "env xa")
   apply (case_tac "env_v xa")
    apply (auto)
    apply (simp add: add_env_def)
   apply (simp add: add_env_def)
   apply (simp add: dir_add_env_def)
   apply (simp add: sub_range_def)
   apply (erule_tac x="xa" in allE)
   apply (auto)
  apply (case_tac "env_v xa")
   apply (auto)
  apply (simp add: add_env_def)
  apply (simp add: dir_add_env_def)
  apply (auto)
  apply (simp add: sub_range_def)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  done

    (* tau1 <: tau2 indicates that tau1 represents a stricter class of values. ie t1 can be used where t2 is used. *)
function sub_type :: "p_type \<Rightarrow> p_type \<Rightarrow> bool" where
  "sub_type IntTy s = (s = IntTy)"
| "sub_type UnitTy s = (s = UnitTy)"  
| "sub_type BoolTy s = (s = BoolTy)"  
| "sub_type (ArrayTy t) s = (s = ArrayTy t)"  
| "sub_type (PairTy t1 t2 r) s = (s = PairTy t1 t2 r)"
| "sub_type (FunTy t1 t2 r a) s = (case s of
    FunTy s1 s2 q b \<Rightarrow> sub_type s1 t1 \<and> sub_type t2 s2 \<and> leq_perm q r \<and> leq_perm (as_perm a) (as_perm b)
    | sx \<Rightarrow> False)"
| "sub_type (ChanTy t c_end) s = (s = ChanTy t c_end)"
by pat_completeness auto
termination
  apply (rule_tac R="measure (\<lambda> (t, s). max (size t) (size s))" in local.termination)
  apply (auto)
  done

fun weaken_type where 
  "weaken_type (FunTy t1 t2 r a) s = (case s of
    FunTy s1 s2 q b \<Rightarrow> t1 = s1 \<and> t2 = s2 \<and> r = q \<and> leq_perm (as_perm a) (as_perm b)
    | sx \<Rightarrow> False)"
| "weaken_type t s = (t = s)"

  
lemma dir_list_ex: "\<lbrakk> t_sub x = tau; fresh_list ds (dom_list l); x \<in> ds \<rbrakk> \<Longrightarrow> dir_list_add_env t_sub l x = tau"  
  apply (induct l)
   apply (auto)
  apply (case_tac "\<not> fresh_list ds (dom_list l)")
   apply (simp add: fresh_list_def)
  apply (auto)
  apply (simp add: dir_add_env_def)
  apply (simp add: fresh_list_def)
  apply (auto)
  done
    
lemma sol_sat_aff: "\<lbrakk> aff_use_env (dir_subst_penv t_sub p_sub r_s) (as_aff (sol_subst_perm p_sub p)) \<rbrakk> \<Longrightarrow>
  dir_sol_sat t_sub p_sub (aff_crn r_s p d)"    
  apply (induct d)
   apply (auto)
  apply (simp add: dir_subst_penv_def)
  apply (simp add: aff_use_env_def)
  apply (case_tac "sol_subst_perm p_sub p")
    apply (auto)
   apply (simp add: null_use_env_def)
  apply (simp add: weak_use_env_def)
  apply (case_tac "dir_subst_permx t_sub p_sub (r_s a)")
    apply (auto)
  done    
  
lemma ivrlc_main: "\<lbrakk>
                spec_env env_v env t_sub; sub_range env_v ds; tsub_dom t_sub ds; infer_type (add_env env_v (Var x1a) a) (insert a ds) e t2 r_s' r_x' r_m' cl ds2;
                well_typed (add_env env (Var x1a) t1) id (add_use_env rx (Var x1a) r) e t2a r_s'a r_end; aff_use_env rx aa; leq_use_env rx r_s;
                leq_use_env (diff_use_env r_s r_ex) (diff_use_env r_s r_exa); leq_use_env r_x (diff_use_env r_s r_ex); x1a \<notin> ref_vars e; leq_use_env r_exa r_s;
                leq_use_env (diff_use_env rx r_exa) r_x; finite_dom (rem_var_env r_s' (Var x1a)) d; a \<notin> ds; p \<noteq> q; p \<notin> ds2; q \<notin> ds2;
                tsub_dom (dir_list_add_env (dir_add_env t_sub a t1) l) ds2; fresh_list (insert a ds) (dom_list l);
                dir_subst_tenv (dir_list_add_env (dir_add_env t_sub a t1) l) (add_env env_v (Var x1a) a) = add_env env (Var x1a) t1;
                psub_dom p_sub (set_diff ds2 (insert a ds));
                leq_use_env (dir_subst_penv (dir_list_add_env (dir_add_env t_sub a t1) l) p_sub r_s') (add_use_env rx (Var x1a) r);
                leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env (dir_add_env t_sub a t1) l) p_sub r_x') (add_use_env rx (Var x1a) r))
                 (diff_use_env r_end (add_use_env rx (Var x1a) r));
                leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env (dir_add_env t_sub a t1) l) p_sub r_m')) (add_use_env rx (Var x1a) r);
                dir_subst_type (dir_list_add_env (dir_add_env t_sub a t1) l) p_sub t2 t2a; dir_sol_sat (dir_list_add_env (dir_add_env t_sub a t1) l) p_sub cl\<rbrakk>
               \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) (insert p (insert q ds2)) \<and>
                       fresh_list ds (dom_list l) \<and>
                       dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                       (\<exists>p_sub. psub_dom p_sub (set_diff (insert p (insert q ds2)) ds) \<and>
                                leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub (rem_var_env r_s' (Var x1a))) r_s \<and>
                                leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub (rem_var_env r_s' (Var x1a))) r_ex) r_x \<and>
                                leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub empty_var_env)) r_ex \<and>
                                dir_list_add_env t_sub l a = Some t1 \<and>
                                dir_subst_type (dir_list_add_env t_sub l) p_sub t2 t2a \<and>
                                r = p_sub p \<and>
                                aa = as_aff (p_sub q) \<and>
                                leq_perm (dir_subst_permx (dir_list_add_env t_sub l) p_sub (r_s' (Var x1a))) (p_sub p) \<and>
                                dir_sol_sat (dir_list_add_env t_sub l) p_sub (aff_crn (rem_var_env r_s' (Var x1a)) (SVar q) d @ cl))"  
    (* defining new type substitution *)
  apply (rule_tac x="l @ [(a, t1)]" in exI)
  apply (auto)
     apply (simp add: dir_list_append_eq)
     apply (rule_tac ds="ds2" in subset_tsub_dom)
      apply (auto)
    apply (rule_tac t_sub="t_sub" and ds'="insert a ds" in append_fresh_list2)
       apply (simp add: fresh_list_def)
      apply (auto)
    apply (rule_tac add_tsub_dom)
     apply (auto)
    apply (rule_tac ds="ds" in subset_tsub_dom)
     apply (auto)
   apply (cut_tac t_sub="t_sub" and l="l @ [(a, t1)]" and env_v="env_v" and ds="ds" in dir_list_cancel_add_eq_env)
     apply (simp)
    apply (rule_tac t_sub="t_sub" and ds'="insert a ds " in append_fresh_list2)
       apply (simp add: fresh_list_def)
      apply (auto)
    apply (rule_tac add_tsub_dom)
     apply (auto)
    apply (rule_tac ds="ds" in subset_tsub_dom)
     apply (auto)
   apply (rule_tac dir_subst_spec_env_ex)
   apply (simp)
    (* prelim: initial permission containment *)
  apply (case_tac "\<not> leq_use_env (dir_subst_penv (dir_list_add_env (dir_add_env t_sub a t1) l) (add_use_env (add_use_env p_sub p r) q (as_perm aa)) r_s')
    (add_use_env rx (Var x1a) r)")  
   apply (cut_tac t_sub="dir_list_add_env (dir_add_env t_sub a t1) l" and p_sub="add_use_env p_sub p r" and
            r_xv="r_s'" and ds="set_diff ds2 (insert a ds)" and x="q" and r="as_perm aa" in add_psub_use_env)
     apply (cut_tac ds="insert a ds" and ds'="ds2" in infer_s_sub_range)
      apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_add_env t_sub a t1) l" and p_sub="p_sub" and
            r_xv="r_s'" and ds="set_diff ds2 (insert a ds)" and x="p" and r="r" in add_psub_use_env)
     apply (cut_tac ds="insert a ds" and ds'="ds2" in infer_s_sub_range)
      apply (auto)
   apply (simp add: set_diff_def)
    (* defining new permission substitution *)
  apply (rule_tac x="add_use_env (add_use_env p_sub p r) q (as_perm aa)" in exI)
  apply (auto)
    (* p_sub containment *)
           apply (rule_tac add_psub_dom)
            apply (rule_tac add_psub_dom)
             apply (rule_tac ds="set_diff ds2 (insert a ds)" in subset_psub_dom)
              apply (simp)
             apply (simp add: set_diff_def)
             apply (auto)
            apply (simp add: set_diff_def)
            apply (cut_tac ds="insert a ds" and ds'="ds2" in infer_x_subset)
             apply (auto)
           apply (simp add: set_diff_def)
           apply (cut_tac ds="insert a ds" and ds'="ds2" in infer_x_subset)
            apply (auto)
    (* initial permission containment *)
          apply (rule_tac r_sb="rem_use_env (add_use_env rx (Var x1a) r) (Var x1a)"  in trans_leq_use_env)
           apply (rule_tac r="r" in rem_add_leq_use_env)
           apply (rule_tac dist_add_leq_use_env)
           apply (simp)
          apply (simp add: rem_sol_subst_penv)
          apply (rule_tac dist_rem_leq_use_env)
          apply (simp add: dir_list_append_eq)
    (* requirements containment *)
         apply (rule_tac r_sb="diff_use_env rx r_exa" in trans_leq_use_env)
          apply (simp)
         apply (rule_tac r_s="r_s" in crush_leq_use_env)
           apply (simp_all)
         apply (rule_tac diff_leq_use_env)
         apply (simp add: rem_sol_subst_penv)
         apply (rule_tac r="r" in rem_add_leq_use_env)
         apply (simp add: dir_list_append_eq)
         apply (cut_tac t_sub="dir_list_add_env (dir_add_env t_sub a t1) l" and p_sub="add_use_env p_sub p r" and
            r_xv="r_s'" and ds="set_diff ds2 (insert a ds)" and x="q" and r="as_perm aa" in add_psub_use_env)
           apply (cut_tac ds="insert a ds" and ds'="ds2" in infer_s_sub_range)
            apply (auto)
          apply (simp add: set_diff_def)
         apply (cut_tac t_sub="dir_list_add_env (dir_add_env t_sub a t1) l" and p_sub="p_sub" and
            r_xv="r_s'" and ds="set_diff ds2 (insert a ds)" and x="p" and r="r" in add_psub_use_env)
           apply (cut_tac ds="insert a ds" and ds'="ds2" in infer_s_sub_range)
            apply (auto)
         apply (simp add: set_diff_def)
    (* subtractant containment *)
        apply (rule_tac cut_leq_use_env)
        apply (rule_tac empty_leq_var_env)
    (* proof of a's type *)
       apply (simp add: dir_list_append_eq)
       apply (rule_tac ds="insert a ds" in dir_list_ex)
         apply (simp add: dir_add_env_def)
        apply (auto)
    (* correctness for t2 *)
      apply (simp add: dir_list_append_eq)
      apply (cut_tac ds="insert a ds" and ds'="ds2" in infer_pvar_type)
        apply (simp)
       apply (rule_tac add_sub_range)
       apply (simp)
      apply (rule_tac add_dir_subst_type)
       apply (rule_tac add_dir_subst_type)
        apply (simp)
       apply (simp add: set_diff_def)
       apply (auto)
      apply (simp add: set_diff_def)
      apply (auto)
    (* correctness of p + q *)
     apply (simp add: add_use_env_def)
    apply (simp add: add_use_env_def)
    apply (case_tac aa)
      apply (auto)
    (* correctness of p with respect to r_s' *)
   apply (case_tac "\<not> leq_perm ((dir_subst_penv (dir_list_add_env (dir_add_env t_sub a t1) l)
    (add_use_env (add_use_env p_sub p r) q (as_perm aa)) r_s') (Var x1a)) ((add_use_env rx (Var x1a) r) (Var x1a))")
    apply (simp add: leq_use_env_def)
   apply (simp add: dir_list_append_eq)
   apply (simp add: add_use_env_def)
   apply (simp add: dir_subst_penv_def)
    (* constraint list: affinity *)
  apply (rule_tac sol_sat_split)
   apply (rule_tac sol_sat_aff)
   apply (case_tac "\<not> as_aff (sol_subst_perm (add_use_env (add_use_env p_sub p r) q (as_perm aa)) (SVar q)) = aa")
    apply (simp add: add_use_env_def)
    apply (case_tac "aa")
      apply (auto)
   apply (rule_tac r_s="rx" in aff_leq_use_env)
    apply (simp)
   apply (simp add: dir_list_append_eq)
   apply (simp add: rem_sol_subst_penv)
   apply (rule_tac rem_add_leq_use_env)
   apply (simp)
    (* - sub-constraint list correctness *)
  apply (cut_tac c_list="cl" and ds="insert a ds" and ds'="ds2" in infer_pvar_crn_list)
    apply (auto)
   apply (rule_tac add_sub_range)
   apply (simp)
  apply (simp add: dir_list_append_eq)
  apply (rule_tac add_psub_sol_sat)
   apply (rule_tac add_psub_sol_sat)
    apply (simp)
   apply (simp add: set_diff_def)
   apply (auto)
  apply (simp add: set_diff_def)
  apply (auto)
  done
    
lemma ivr_lam_case: "\<lbrakk>\<And>tau r_s r_x r_ex env env_v ds tau_v r_sv r_xv r_mv c_list ds' t_sub.
           \<lbrakk>well_typed env id r_s e tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds\<rbrakk>
           \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list);
        spec_env env_v env t_sub; sub_range env_v ds; tsub_dom t_sub ds; infer_type (add_env env_v (Var x1a) a) (insert a ds) e t2 r_s' r_x' r_m' cl ds2;
        well_typed (add_env env (Var x1a) t1) id (add_use_env rx (Var x1a) r) e t2a r_s'a r_end; aff_use_env rx aa; leq_use_env rx r_s;
        leq_use_env (diff_use_env r_s r_ex) (diff_use_env r_s r_exa); leq_use_env r_x (diff_use_env r_s r_ex); x1a \<notin> ref_vars e; leq_use_env r_exa r_s;
        leq_use_env (diff_use_env rx r_exa) r_x; finite_dom (rem_var_env r_s' (Var x1a)) d; a \<notin> ds; p \<noteq> q; p \<notin> ds2; q \<notin> ds2\<rbrakk>
       \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) (insert p (insert q ds2)) \<and>
               fresh_list ds (dom_list l) \<and>
               dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
               (\<exists>p_sub. psub_dom p_sub (set_diff (insert p (insert q ds2)) ds) \<and>
                        leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub (rem_var_env r_s' (Var x1a))) r_s \<and>
                        leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub (rem_var_env r_s' (Var x1a))) r_ex) r_x \<and>
                        leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub empty_var_env)) r_ex \<and>
                        dir_list_add_env t_sub l a = Some t1 \<and>
                        dir_subst_type (dir_list_add_env t_sub l) p_sub t2 t2a \<and>
                        r = p_sub p \<and>
                        aa = as_aff (p_sub q) \<and>
                        leq_perm (dir_subst_permx (dir_list_add_env t_sub l) p_sub (r_s' (Var x1a))) (p_sub p) \<and>
                        dir_sol_sat (dir_list_add_env t_sub l) p_sub (aff_crn (rem_var_env r_s' (Var x1a)) (SVar q) d @ cl))"
    (* initial induction *)
  apply (cut_tac env_v="add_env env_v (Var x1a) a" and env="add_env env (Var x1a) t1" and e="e"
      and r_s="add_use_env rx (Var x1a) r" and r_ex="add_use_env rx (Var x1a) r" and ds="insert a ds" and t_sub="dir_add_env t_sub a t1" in ivrlc_coerce)
        apply (auto)
      apply (rule_tac well_typed_end_perm_lbound)
      apply (auto)
     apply (rule_tac ds="ds" in add_spec_env)
       apply (simp_all)
    apply (rule_tac add_sub_range)
    apply (simp_all)
   apply (rule_tac add_tsub_dom)
    apply (rule_tac ds="ds" in subset_tsub_dom)
     apply (auto)
    (* main lemma *)
  apply (rule_tac ivrlc_main)
                      apply (auto)
  done
    
lemma add_fresh_list_ex: "\<lbrakk> fresh_list ds (dom_list l); tsub_dom (dir_list_add_env t_sub l) ds';
  x \<notin> ds'; ds \<subseteq> ds' \<rbrakk> \<Longrightarrow> fresh_list ds (x # (dom_list l))" 
  apply (cut_tac x="x" and ds="ds" and l="l" and ds'="ds'" in add_fresh_list)
      apply (auto)
  done    
    
lemma ivrac_coerce: "\<lbrakk> \<And>tau r_s r_x r_ex env env_v ds tau_v r_sv r_xv r_mv c_list ds' t_sub.
           \<lbrakk>well_typed env id r_s e tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds\<rbrakk>
           \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list);
   well_typed env id r_s e tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds  \<rbrakk> \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list)"    
  apply (auto)
  done
    
lemma dir_add_cancel_use_env: "\<lbrakk> tvar_range r_sv ds; a \<notin> ds \<rbrakk> \<Longrightarrow>
  dir_subst_penv (dir_add_env t_sub a tau) p_sub r_sv = dir_subst_penv t_sub p_sub r_sv"
  apply (case_tac "\<forall> x. dir_subst_penv (dir_add_env t_sub a tau) p_sub r_sv x = dir_subst_penv t_sub p_sub r_sv x")
   apply (auto)
  apply (cut_tac t_sub="t_sub" and a="a" and r_sv="r_sv" and tau="tau" in dir_add_cancel_use_env_ih)
    apply (auto)
  done    
    
lemma ifz_sol_subst_penv_gen: "\<lbrakk> dir_subst_permx t_sub p_sub px = NoPerm \<rbrakk> \<Longrightarrow> dir_subst_penv t_sub p_sub (ifz_var_env px r_sv) = empty_use_env"    
  apply (case_tac "\<forall> x. dir_subst_penv t_sub p_sub (ifz_var_env px r_sv) x = empty_use_env x")   
   apply (auto)
  apply (simp add: dir_subst_penv_def)
  apply (simp add: ifz_var_env_def)
  apply (simp add: empty_use_env_def)
  apply (case_tac "r_sv x = XPerm (SPerm NoPerm)")
   apply (auto)
  done            
    
lemma ivrac_main: "\<lbrakk>
        spec_env env_v (dir_subst_tenv (dir_list_add_env t_sub l) env_v) t_sub; sub_range env_v ds; tsub_dom t_sub ds;
        infer_type env_v ds e1 tau_f r_s1 r_x1 r_m1 cl1 ds2;
        infer_type env_v ds2 e2 t1a r_s2a r_x2 r_m2 cl2 ds3; leq_use_env r_s3 r_s;
        leq_use_env (diff_use_env r_s r_ex) (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_exa));
        leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3; disj_use_env rx1 (lift_use_env rx2 r); leq_use_env r_x (diff_use_env r_s r_ex);
        leq_use_env r_exa r_s; leq_use_env (app_req rx1 rx2 r tau r_exa) r_x;
        finite_dom (comp_var_env (comp_var_env r_s1 r_x1) (comp_var_env r_s2a (lift_var_env r_x2 (SVar p)))) d; fresh_list ds3 [aa, p, q]; leq_use_env r_exaa r_s;
        leq_use_env r_exb (diff_use_env r_s r_exaa); super_norm_use_env r_s r_s3 = diff_use_env r_s (comp_use_env r_exaa r_exb);
        well_typed (dir_subst_tenv (dir_list_add_env t_sub l) env_v) id r_s e1 (FunTy t1 tau r a) (diff_use_env r_s r_exaa) rx1;
        well_typed (dir_subst_tenv (dir_list_add_env t_sub l) env_v) id (diff_use_env r_s r_exaa) e2 t1 (diff_use_env (diff_use_env r_s r_exaa) r_exb) rx2;
        tsub_dom (dir_list_add_env t_sub l) ds2; fresh_list ds (dom_list l); env = dir_subst_tenv (dir_list_add_env t_sub l) env_v;
        psub_dom p_sub (set_diff ds2 ds); leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_s1) r_s;
        leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_x1) r_exaa) rx1;
        leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_m1)) r_exaa;
        dir_subst_type (dir_list_add_env t_sub l) p_sub tau_f (FunTy t1 tau r a); dir_sol_sat (dir_list_add_env t_sub l) p_sub cl1;
        tsub_dom (dir_list_add_env (dir_list_add_env t_sub l) la) ds3; fresh_list ds2 (dom_list la);
        dir_subst_tenv (dir_list_add_env (dir_list_add_env t_sub l) la) env_v = dir_subst_tenv (dir_list_add_env t_sub l) env_v;
        psub_dom p_suba (set_diff ds3 ds2); leq_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba r_s2a) (diff_use_env r_s r_exaa);
        leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba r_x2) r_exb) rx2;
        leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba r_m2)) r_exb;
        dir_subst_type (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba t1a t1; dir_sol_sat (dir_list_add_env (dir_list_add_env t_sub l) la) p_suba cl2\<rbrakk>
       \<Longrightarrow> \<exists>la. tsub_dom (dir_list_add_env t_sub la) (insert aa (insert p (insert q ds3))) \<and>
                fresh_list ds (dom_list la) \<and>
                dir_subst_tenv (dir_list_add_env t_sub la) env_v = dir_subst_tenv (dir_list_add_env t_sub l) env_v \<and>
                (\<exists>p_sub. psub_dom p_sub (set_diff (insert aa (insert p (insert q ds3))) ds) \<and>
                         leq_use_env
                          (dir_subst_penv (dir_list_add_env t_sub la) p_sub
                            (comp_var_env (comp_var_env r_s1 r_x1) (comp_var_env r_s2a (lift_var_env r_x2 (SVar p)))))
                          r_s \<and>
                         leq_use_env
                          (diff_use_env
                            (dir_subst_penv (dir_list_add_env t_sub la) p_sub (ifz_var_env (XType aa) (comp_var_env r_x1 (lift_var_env r_x2 (SVar p))))) r_ex)
                          r_x \<and>
                         leq_use_env
                          (cut_use_env
                            (dir_subst_penv (dir_list_add_env t_sub la) p_sub
                              (comp_var_env (comp_var_env r_m1 r_x1) (comp_var_env r_m2 (lift_var_env r_x2 (SVar p))))))
                          r_ex \<and>
                         dir_list_add_env t_sub la aa = Some tau \<and>
                         (\<exists>tau_x. (\<exists>t1_x. dir_subst_type (dir_list_add_env t_sub la) p_sub t1a t1_x \<and>
                                          (\<exists>t2_x. dir_list_add_env t_sub la aa = Some t2_x \<and> tau_x = FunTy t1_x t2_x (p_sub p) (as_aff (p_sub q)))) \<and>
                                  dir_subst_type (dir_list_add_env t_sub la) p_sub tau_f tau_x) \<and>
                         dir_sol_sat (dir_list_add_env t_sub la) p_sub
                          (disj_crn r_x1 (lift_var_env r_x2 (SVar p)) d @ semi_disj_crn r_m2 r_x1 d @ semi_disj_crn r_m1 r_s2a d @ cl1 @ cl2))"
    (* prelim: type subst domain *)
  apply (cut_tac t_sub="t_sub" and ?l1.0="la" and ?l2.0="l" and ds="ds3" in append_tsub_dom)
    apply (rule_tac ds="ds" in list_add_tsub_dom)
      apply (auto)
     apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
      apply (auto)
     apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
      apply (auto)
    apply (cut_tac t_sub="t_sub" and l="l" and ds="ds2" in list_add_dls)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and l="la" and ds="ds3" in list_add_dls)
    apply (auto)
    (* defining new t_sub *)
  apply (rule_tac x="[(aa, tau)] @ la @ l" in exI)
  apply (auto)
     apply (rule_tac add_tsub_dom)
      apply (rule_tac ds="ds3" in subset_tsub_dom)
       apply (auto)
    apply (rule_tac t_sub="t_sub" and ds'="ds3" in add_fresh_list_ex)
       apply (rule_tac ds="ds" and ds'="ds2" in append_fresh_list2)
          apply (auto)
      apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
       apply (auto)
     apply (simp add: fresh_list_def)
     apply (auto)
    apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (auto)
   apply (rule_tac ds="ds" in dir_add_eq_env)
     apply (simp add: dir_list_append_eq)
    apply (simp)
   apply (case_tac "aa \<in> ds3")
    apply (simp add: fresh_list_def)
    apply (auto)
   apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
    apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
    (* p \<notin> ds3 *)
  apply (case_tac "p \<in> ds3")
   apply (simp add: fresh_list_def)
   apply (auto)
  apply (case_tac "aa \<in> ds3")
   apply (simp add: fresh_list_def)
   apply (auto)
  apply (case_tac "q \<in> ds3")
   apply (simp add: fresh_list_def)
   apply (auto)
    (* prelim: sub_range env_v ds2 *)
  apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
    apply (simp)
   apply (rule_tac infer_x_subset)
   apply (simp)
    (* P* inequality 1 *)
  apply (case_tac "\<not> leq_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
      (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_s1) r_s")
   apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_tvar_range)
     apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and a="aa" and tau="tau" and
      p_sub="add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)" and r_sv="r_s1" and ds="ds2" in dir_add_cancel_use_env)
     apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and l="la" and p_sub="add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)"
                and r_sv="r_s1" and ds="ds2" in dir_list_add_cancel_use_env)
     apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_s_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and p_sub="add_use_env (comp_use_env p_sub p_suba) p r" and r_xv="r_s1"
      and ds="set_diff ds2 ds" and x="q" and r="as_perm a" in add_psub_use_env)
     apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and p_sub="comp_use_env p_sub p_suba" and r_xv="r_s1" and ds="set_diff ds2 ds" and x="p" and r="r" in add_psub_use_env)
     apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and ?p_sub1.0="p_sub" and ?p_sub2.0="p_suba" and r_xv="r_s1" and ds="set_diff ds2 ds" in comp_psub_use_env1)
      apply (auto)
   apply (simp add: set_diff_def)
    (* P* inequality 2 *)
  apply (case_tac "\<not> leq_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
      (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_s2a) (diff_use_env r_s r_exaa)")
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_s_sub_range)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_tvar_range)
     apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and a="aa" and tau="tau" and
      p_sub="add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)" and r_sv="r_s2a" and ds="ds3" in dir_add_cancel_use_env)
     apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and p_sub="add_use_env (comp_use_env p_sub p_suba) p r" and
        r_xv="r_s2a" and ds="set_diff ds3 ds2" and x="q" and r="as_perm a" in add_psub_use_env)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and p_sub="comp_use_env p_sub p_suba" and r_xv="r_s2a" and ds="set_diff ds3 ds2" and x="p" and r="r" in add_psub_use_env)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and ?p_sub1.0="p_suba" and ?p_sub2.0="p_sub" and r_xv="r_s2a" and ds="set_diff ds3 ds2" in comp_psub_use_env2)
      apply (auto)
   apply (simp add: set_diff_def)
    (* X* inequality 1 *)
  apply (case_tac "\<not> leq_use_env (diff_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
      (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x1) r_exaa) rx1")
   apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_tvar_range)
     apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and a="aa" and tau="tau" and
      p_sub="add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)" and r_sv="r_x1" and ds="ds2" in dir_add_cancel_use_env)
     apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and l="la" and r_sv="r_x1" and ds="ds2" and
      p_sub="add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)" in dir_list_add_cancel_use_env)
     apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_s_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and p_sub="add_use_env (comp_use_env p_sub p_suba) p r" and
      r_xv="r_x1" and ds="set_diff ds2 ds" and x="q" and r="as_perm a" in add_psub_use_env)
     apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and p_sub="comp_use_env p_sub p_suba" and r_xv="r_x1" and ds="set_diff ds2 ds" and x="p" and r="r" in add_psub_use_env)
     apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and ?p_sub1.0="p_sub" and ?p_sub2.0="p_suba" and r_xv="r_x1" and ds="set_diff ds2 ds" in comp_psub_use_env1)
      apply (auto)
   apply (simp add: set_diff_def)
    (* X* inequality 2 *)
  apply (case_tac "\<not> leq_use_env (diff_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
    (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x2) r_exb) rx2")
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_s_sub_range)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_tvar_range)
     apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and a="aa" and tau="tau" and
      p_sub="add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)" and r_sv="r_x2" and ds="ds3" in dir_add_cancel_use_env)
     apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and p_sub="add_use_env (comp_use_env p_sub p_suba) p r" and
      r_xv="r_x2" and ds="set_diff ds3 ds2" and x="q" and r="as_perm a" in add_psub_use_env)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and p_sub="comp_use_env p_sub p_suba" and r_xv="r_x2" and ds="set_diff ds3 ds2" and x="p" and r="r" in add_psub_use_env)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and ?p_sub1.0="p_suba" and ?p_sub2.0="p_sub" and r_xv="r_x2" and ds="set_diff ds3 ds2" in comp_psub_use_env2)
      apply (auto)
   apply (simp add: set_diff_def)
    (* M* inequality 1 *)
  apply (case_tac "\<not> leq_use_env (cut_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
    (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_m1)) r_exaa")
   apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_m_tvar_range)
     apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and a="aa" and tau="tau" and
      p_sub="add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)" and r_sv="r_m1" and ds="ds2" in dir_add_cancel_use_env)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and l="la" and r_sv="r_m1" and ds="ds2" and
        p_sub="add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)" in dir_list_add_cancel_use_env)
     apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and e="e1" and ds'="ds2" in infer_m_sub_range)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and p_sub="add_use_env (comp_use_env p_sub p_suba) p r" and
      r_xv="r_m1" and ds="set_diff ds2 ds" and x="q" and r="as_perm a" in add_psub_use_env)
     apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and p_sub="comp_use_env p_sub p_suba" and r_xv="r_m1" and ds="set_diff ds2 ds" and x="p" and r="r" in add_psub_use_env)
     apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env t_sub l" and ?p_sub1.0="p_sub" and ?p_sub2.0="p_suba" and r_xv="r_m1" and ds="set_diff ds2 ds" in comp_psub_use_env1)
      apply (auto)
   apply (simp add: set_diff_def)
    (* M* inequality 2 *)
  apply (case_tac "\<not> leq_use_env (cut_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
    (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_m2)) r_exb")
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_m_sub_range)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds2" and e="e2" and ds'="ds3" in infer_m_tvar_range)
     apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and a="aa" and tau="tau" and
      p_sub="add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)" and r_sv="r_m2" and ds="ds3" in dir_add_cancel_use_env)
    apply (auto)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and p_sub="add_use_env (comp_use_env p_sub p_suba) p r" and
      r_xv="r_m2" and ds="set_diff ds3 ds2" and x="q" and r="as_perm a" in add_psub_use_env)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and p_sub="comp_use_env p_sub p_suba" and r_xv="r_m2" and ds="set_diff ds3 ds2" and x="p" and r="r" in add_psub_use_env)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (auto)
    apply (simp add: set_diff_def)
   apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and ?p_sub1.0="p_suba" and ?p_sub2.0="p_sub" and r_xv="r_m2" and ds="set_diff ds3 ds2" in comp_psub_use_env2)
      apply (auto)
   apply (simp add: set_diff_def)
    (* prelim: (t_sub, p_sub)(tau_f) = FunTy t1 tau r a *)
  apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and x="aa" and t="tau" and tau_v="tau_f" and
      p_sub="add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)" and tau="FunTy t1 tau r a" in dir_add_subst_type)
    apply (rule_tac dir_list_add_subst_type)
     apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
      apply (simp)
     apply (cut_tac tau_v="tau_f" and ds'="ds2" and ds="ds" in infer_pvar_type)
       apply (auto)
     apply (rule_tac add_dir_subst_type)
      apply (rule_tac add_dir_subst_type)
       apply (rule_tac ds="set_diff ds2 ds" in comp_dir_subst_type1)
          apply (simp)
         apply (rule_tac infer_pvar_type)
          apply (auto)
       apply (simp add: set_diff_def)
      apply (simp add: set_diff_def)
      apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (cut_tac x="x" and l="la" in dom_list_contain)
     apply (simp)
    apply (cut_tac tau_v="tau_f" and ds'="ds2" and ds="ds" in infer_tvar_type)
      apply (auto)
    apply (simp add: fresh_list_def)
    apply (auto)
   apply (cut_tac tau_v="tau_f" and ds'="ds2" and ds="ds" in infer_tvar_type)
     apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)  
    (* prelim: (t_sub, p_sub)(t1a) = t1 *)
  apply (cut_tac t_sub="dir_list_add_env (dir_list_add_env t_sub l) la" and x="aa" and t="tau" and tau_v="t1a" and
      p_sub="add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)" and tau="t1" in dir_add_subst_type)
    apply (rule_tac add_dir_subst_type)
     apply (rule_tac add_dir_subst_type)
      apply (rule_tac ds="set_diff ds3 ds2" in comp_dir_subst_type2)
         apply (simp)
        apply (rule_tac infer_pvar_type)
         apply (auto)
      apply (simp add: set_diff_def)
     apply (cut_tac tau_v="t1a" and ds'="ds3" and ds="ds2" in infer_pvar_type)
       apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (cut_tac tau_v="t1a" and ds="ds2" and ds'="ds3" in infer_pvar_type)
      apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac tau_v="t1a" and ds'="ds3" and ds="ds2" in infer_tvar_type)
     apply (auto)
    (* prelim: rewriting of lift r_x2 *)
  apply (case_tac "dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
            (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) (lift_var_env r_x2 (SVar p)) \<noteq>
        lift_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
            (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x2) r")
   apply (cut_tac t_sub="dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau"
      and p_sub="add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)" and r_s="r_x2" and r="SVar p" in lift_sol_subst_penv)
   apply (case_tac "add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a) p \<noteq> r")
    apply (simp add: add_use_env_def)
    apply (simp add: fresh_list_def)
   apply (auto)
    (* prelim: (t_sub, p_sub)( X1* ) \<le> P1 *)
  apply (cut_tac r_sc="dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
           (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x1"
      and r_sb="comp_use_env rx1 r_exaa" and r_sa="r_s" in trans_leq_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
      apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
       apply (simp_all)
    apply (rule_tac self_comp_leq_use_env1)
   apply (rule_tac st_diff_comp_leq_use_env)
   apply (simp)
    (* prelim: (t_sub, p_sub)(lift( X2* )) \<le> P1 *)
  apply (cut_tac r_sc="lift_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
          (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x2) r"
      and r_sb="comp_use_env (lift_use_env rx2 r) r_exb" and r_sa="r_s" in trans_leq_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
      apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
       apply (simp_all)
     apply (rule_tac self_comp_leq_use_env2)
    apply (rule_tac r_sb="diff_use_env r_s r_exaa" in trans_leq_use_env)
     apply (rule_tac self_diff_leq_use_env)
    apply (simp)
   apply (rule_tac st_diff_comp_leq_use_env)
   apply (rule_tac t="diff_use_env (lift_use_env
             (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
               (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x2) r) r_exb" and
          s="lift_use_env (diff_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
               (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x2) r_exb) r" in subst)
    apply (simp add: lift_diff_use_env)
   apply (rule_tac dist_lift_leq_use_env)
   apply (simp)
    (* defining new p_sub *)
  apply (rule_tac x="add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)" in exI)
  apply (auto)
    (* p_sub domain containment *)
        apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
         apply (auto)
        apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
         apply (auto)
        apply (rule_tac add_psub_dom)
         apply (rule_tac add_psub_dom)
          apply (rule_tac comp_psub_dom)
           apply (rule_tac ds="set_diff ds2 ds" in subset_psub_dom)
            apply (simp)
           apply (rule_tac set_diff_subset)
            apply (auto)
          apply (rule_tac ds="set_diff ds3 ds2" in subset_psub_dom)
           apply (simp)
          apply (rule_tac set_diff_subset)
           apply (auto)
         apply (simp add: set_diff_def)
         apply (auto)
        apply (simp add: set_diff_def)
        apply (auto)
    (* initial permission containment *)
       apply (simp add: dir_list_append_eq)
       apply (simp add: comp_sol_subst_penv)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (simp_all)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac r_sb="diff_use_env r_s r_exaa" in trans_leq_use_env)
         apply (rule_tac self_diff_leq_use_env)
        apply (simp_all)
    (* requirements containment. primitive case *)
      apply (case_tac "req_type tau = Prim")
       apply (cut_tac t_sub="dir_add_env (dir_list_add_env t_sub (la @ l)) aa tau" and r_sv="comp_var_env r_x1 (lift_var_env r_x2 (SVar p))"
        and p_sub="add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)" and px="XType aa" in ifz_sol_subst_penv_gen)
        apply (simp add: dir_add_env_def)
       apply (auto)
       apply (rule_tac diff_leq_use_env)
       apply (rule_tac leq_empty_use_env)
    (* - non-primitive case *)
      apply (simp add: app_req_def)
      apply (simp add: dir_list_append_eq)
      apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_exa)" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 (lift_use_env rx2 r)) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_exa)" in trans_leq_use_env)
       apply (rule_tac lhs_dist_dcl_use_env)
       apply (rule_tac rhs_dist_dcl_use_env)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac self_comp_leq_use_env1)
       apply (rule_tac comp_leq_use_env2)
       apply (rule_tac unroll_dcl_use_env)
       apply (rule_tac dist_diff_leq_use_env)
       apply (rule_tac lhs_flip_use_env)
       apply (rule_tac rhs_flip_use_env)
       apply (rule_tac unroll_dcl_use_env)
       apply (rule_tac dist_diff_leq_use_env)
       apply (rule_tac spec_diff_lift_leq_use_env)
      apply (rule_tac r_s="r_s" in crush_leq_use_env)
        apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_exa)" in trans_leq_use_env)
         apply (rule_tac dist_diff_leq_use_env)
         apply (simp_all)
        apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
        apply (simp_all)
      apply (rule_tac r_sb="diff_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
        (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) (comp_var_env r_x1 (lift_var_env r_x2 (SVar p)))) r_ex" in trans_leq_use_env)
       apply (rule_tac r_sb="diff_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
        (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a))
        (comp_var_env r_x1 (lift_var_env r_x2 (SVar p)))) (comp_use_env r_exaa r_exb)" in trans_leq_use_env)
        apply (simp add: comp_sol_subst_penv)
        apply (rule_tac lhs_dist_dcl_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac comp_leq_use_env1)
         apply (rule_tac lhs_unroll_dcl_use_env)
         apply (rule_tac diff_leq_use_env)
         apply (simp)
        apply (rule_tac comp_leq_use_env2)
        apply (rule_tac lhs_flip_use_env)
        apply (rule_tac lhs_unroll_dcl_use_env)
        apply (rule_tac diff_leq_use_env)
       apply (rule_tac t="diff_use_env (lift_use_env
             (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
               (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x2) r) r_exb" and
          s="lift_use_env (diff_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
               (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x2) r_exb) r" in subst)
         apply (simp add: lift_diff_use_env)
        apply (rule_tac dist_lift_leq_use_env)
        apply (simp)
       apply (rule_tac r_s="r_s" in crush_leq_use_env)
         apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_exa)" in trans_leq_use_env)
          apply (rule_tac t="diff_use_env r_s (comp_use_env r_exaa r_exb)" and s="super_norm_use_env r_s r_s3" in subst)
           apply (simp)
          apply (rule_tac rhs_snorm_leq_use_env2)
           apply (rule_tac self_diff_leq_use_env)
          apply (simp_all)
        apply (simp add: comp_sol_subst_penv)
        apply (rule_tac dist_comp_leq_use_env)
         apply (simp_all)
       apply (rule_tac self_diff_leq_use_env)
      apply (rule_tac dist_diff_leq_use_env)
      apply (rule_tac if_zero_leq_var_env)
      apply (rule_tac id_leq_use_env)
    (* subtractant containment *)
     apply (rule_tac r_sb="cut_use_env (comp_use_env (comp_use_env rx1 r_exaa) (comp_use_env (lift_use_env rx2 r) r_exb))" in trans_leq_use_env)
      apply (rule_tac r_s="r_s" in dist_diff_leq_use_env_rev)
       apply (rule_tac r_sb="comp_use_env r_s (comp_use_env rx1 (lift_use_env rx2 r))" in trans_leq_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac id_leq_use_env)
        apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
         apply (simp_all)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac comp_leq_use_env2)
         apply (rule_tac self_comp_leq_use_env1)
        apply (rule_tac comp_leq_use_env1)
        apply (simp)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac comp_leq_use_env2)
        apply (rule_tac self_comp_leq_use_env2)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac r_sb="diff_use_env r_s r_exaa" in trans_leq_use_env)
        apply (rule_tac self_diff_leq_use_env)
       apply (simp)
      apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_exa)" in trans_leq_use_env)
       apply (rule_tac r_sb="diff_use_env r_s (comp_use_env (comp_use_env r_exaa r_exb) (comp_use_env rx1 (lift_use_env rx2 r)))" in trans_leq_use_env)
        apply (rule_tac dist_diff_leq_use_env_gen)
         apply (rule_tac id_leq_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac dist_comp_leq_use_env)
          apply (rule_tac comp_leq_use_env2)
          apply (rule_tac self_comp_leq_use_env1)
         apply (rule_tac comp_leq_use_env1)
         apply (rule_tac self_comp_leq_use_env1)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac comp_leq_use_env2)
         apply (rule_tac self_comp_leq_use_env2)
        apply (rule_tac comp_leq_use_env1)
        apply (rule_tac self_comp_leq_use_env2)
       apply (rule_tac rhs_unroll_dcl_use_env)
       apply (rule_tac dist_diff_leq_use_env_gen)
        apply (rule_tac t="diff_use_env r_s (comp_use_env r_exaa r_exb)" and s="super_norm_use_env r_s r_s3" in subst)
         apply (simp)
        apply (rule_tac rhs_snorm_leq_use_env2)
         apply (rule_tac id_leq_use_env)
        apply (simp_all)
      apply (rule_tac self_comp_leq_use_env1)
     apply (rule_tac rhs_cut_leq_use_env)
     apply (simp add: dir_list_append_eq)
     apply (simp add: comp_sol_subst_penv)
     apply (rule_tac lhs_dist_cut_leq_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac lhs_dist_cut_leq_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac comp_leq_use_env2)
       apply (simp)
      apply (rule_tac cut_leq_use_env)
      apply (rule_tac comp_leq_use_env1)
      apply (rule_tac st_diff_comp_leq_use_env)
      apply (simp)
     apply (rule_tac lhs_dist_cut_leq_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac comp_leq_use_env2)
      apply (rule_tac comp_leq_use_env2)
      apply (simp)
     apply (rule_tac cut_leq_use_env)
     apply (rule_tac comp_leq_use_env2)
     apply (rule_tac st_diff_comp_leq_use_env)
     apply (rule_tac t="diff_use_env (lift_use_env
             (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
               (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x2) r) r_exb" and
          s="lift_use_env (diff_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
               (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x2) r_exb) r" in subst)
      apply (simp add: lift_diff_use_env)
     apply (rule_tac dist_lift_leq_use_env)
     apply (simp)
    (* correctness of expression type *)
    apply (simp add: dir_add_env_def)
    (* correctness of unification constraint *)
   apply (simp add: dir_list_append_eq)
   apply (rule_tac x="FunTy t1 tau r a" in exI)
   apply (auto)
     apply (simp add: dir_add_env_def)
    apply (simp add: add_use_env_def)
    apply (simp add: fresh_list_def)
   apply (simp add: add_use_env_def)
   apply (simp add: fresh_list_def)
   apply (case_tac a)
     apply (auto)
    (* correctness of constraints: disjointness *)
  apply (simp add: dir_list_append_eq)
  apply (rule_tac sol_sat_split)
   apply (rule_tac sol_sat_disj)
   apply (rule_tac r_s="comp_use_env rx1 (cut_use_env r_exaa)" in disj_leq_use_env1)
    apply (rule_tac r_s="comp_use_env (lift_use_env rx2 r) (cut_use_env r_exb)" in disj_leq_use_env2)
     apply (rule_tac disj_comp_use_env1)
      apply (rule_tac disj_comp_use_env2)
       apply (simp)
      apply (rule_tac cut_disj_use_env)
      apply (rule_tac r_s="diff_use_env r_s r_exb" in mini_disj_leq_use_env2)
       apply (rule_tac mini_disj_diff_use_env)
      apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
       apply (rule_tac r_sb="super_norm_use_env r_s r_s3" in trans_leq_use_env)
        apply (simp)
        apply (rule_tac dist_diff_leq_use_env_gen)
         apply (rule_tac id_leq_use_env)
        apply (rule_tac self_comp_leq_use_env2)
       apply (rule_tac rhs_snorm_leq_use_env2)
        apply (simp_all)
      apply (rule_tac self_comp_leq_use_env1)
     apply (rule_tac disj_comp_use_env2)
      apply (rule_tac comm_disj_use_env)
      apply (rule_tac cut_disj_use_env)
      apply (rule_tac r_s="diff_use_env r_s r_exaa" in mini_disj_leq_use_env2)
       apply (rule_tac mini_disj_diff_use_env)
      apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
       apply (rule_tac r_sb="super_norm_use_env r_s r_s3" in trans_leq_use_env)
        apply (simp)
        apply (rule_tac dist_diff_leq_use_env_gen)
         apply (rule_tac id_leq_use_env)
        apply (rule_tac self_comp_leq_use_env1)
       apply (rule_tac rhs_snorm_leq_use_env2)
        apply (simp_all)
      apply (rule_tac self_comp_leq_use_env2)
     apply (rule_tac comm_disj_use_env)
     apply (rule_tac cut_disj_use_env)
     apply (rule_tac r_s="diff_use_env r_s r_exaa" in mini_disj_leq_use_env2)
      apply (rule_tac mini_disj_diff_use_env)
     apply (rule_tac cut_leq_use_env)
     apply (simp)
    apply (rule_tac st_diff_comp_leq_use_env)
    apply (rule_tac r_sb="diff_use_env (lift_use_env
      (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
      (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x2) r) r_exb" in trans_leq_use_env)
     apply (rule_tac t="diff_use_env (lift_use_env
             (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
               (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x2) r) r_exb" and
          s="lift_use_env (diff_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
               (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x2) r_exb) r" in subst)
      apply (simp add: lift_diff_use_env)
     apply (rule_tac dist_lift_leq_use_env)
     apply (simp)
    apply (rule_tac dist_diff_leq_use_env_cut)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac st_diff_comp_leq_use_env)
   apply (rule_tac r_sb="diff_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
             (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x1) r_exaa" in trans_leq_use_env)
    apply (simp)
   apply (rule_tac dist_diff_leq_use_env_cut)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac id_leq_use_env)
    (* - semi-disjointness 1 *)
  apply (rule_tac sol_sat_split)
   apply (rule_tac sol_sat_mini_disj)
   apply (rule_tac cut_mini_disj_use_env)
   apply (rule_tac r_s="r_exb" in mini_disj_leq_use_env1)
    apply (rule_tac r_s="diff_use_env r_s r_exb" in mini_disj_leq_use_env2)
     apply (rule_tac mini_disj_diff_use_env)
    apply (rule_tac r_sb="comp_use_env (diff_use_env r_s r_exb) (cut_use_env r_exaa)" in trans_leq_use_env)
     apply (rule_tac dist_comp_leq_use_env)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac swap_diff_cut_leq_use_env)
      apply (simp_all)
   apply (rule_tac st_diff_comp_leq_use_env)
   apply (rule_tac r_sb="diff_use_env (dir_subst_penv (dir_add_env (dir_list_add_env (dir_list_add_env t_sub l) la) aa tau)
      (add_use_env (add_use_env (comp_use_env p_sub p_suba) p r) q (as_perm a)) r_x1) r_exaa" in trans_leq_use_env)
    apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (rule_tac mini_disj_diff_leq_use_env2)
       apply (simp)
      apply (rule_tac r_s="diff_use_env r_s r_exb" in mini_disj_leq_use_env2)
       apply (rule_tac mini_disj_diff_use_env)
      apply (rule_tac r_sb="super_norm_use_env r_s r_s3" in trans_leq_use_env)
       apply (simp)
       apply (rule_tac dist_diff_leq_use_env_gen)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac self_comp_leq_use_env2)
      apply (rule_tac rhs_snorm_leq_use_env2)
       apply (rule_tac id_leq_use_env)
      apply (simp_all)
    apply (rule_tac comp_leq_use_env1)
    apply (simp)
   apply (rule_tac dist_diff_leq_use_env_cut)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac id_leq_use_env)
    (* - semi-disjointness 2 *)
  apply (rule_tac sol_sat_split)
   apply (rule_tac sol_sat_mini_disj)
   apply (rule_tac cut_mini_disj_use_env)
   apply (rule_tac r_s="r_exaa" in mini_disj_leq_use_env1)
    apply (rule_tac r_s="diff_use_env r_s r_exaa" in mini_disj_leq_use_env2)
     apply (rule_tac mini_disj_diff_use_env)
    apply (simp_all)
    (* > constraint list 1 correctness *)
  apply (rule_tac sol_sat_split)
   apply (cut_tac c_list="cl1" and ds="ds" and ds'="ds2" in infer_tvar_crn_list)
     apply (auto)
   apply (cut_tac c_list="cl1" and ds="ds" and ds'="ds2" in infer_pvar_crn_list)
     apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (rule_tac dir_add_sol_sat)
    apply (rule_tac dir_list_add_sol_sat)
     apply (rule_tac add_psub_sol_sat)
      apply (rule_tac add_psub_sol_sat)
       apply (rule_tac ds="set_diff ds2 ds" in comp_psub_sol_sat1)
          apply (simp_all)
       apply (simp add: set_diff_def)
       apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (cut_tac x="x" and l="la" in dom_list_set_contain)
    apply (auto)
   apply (simp add: fresh_list_def)
   apply (auto)
    (* > constraint list 2 correctness *)
  apply (cut_tac c_list="cl2" and ds="ds2" and ds'="ds3" in infer_tvar_crn_list)
    apply (auto)
  apply (cut_tac c_list="cl2" and ds="ds2" and ds'="ds3" in infer_pvar_crn_list)
    apply (auto)
  apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
   apply (auto)
  apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
   apply (auto)
  apply (rule_tac dir_add_sol_sat)
   apply (rule_tac add_psub_sol_sat)
    apply (rule_tac add_psub_sol_sat)
     apply (rule_tac ds="set_diff ds3 ds2" in comp_psub_sol_sat2)
        apply (simp_all)
     apply (simp add: set_diff_def)
     apply (auto)
   apply (simp add: set_diff_def)
   apply (auto)
  apply (simp add: set_diff_def)
  apply (auto)
  done
    
lemma ivr_app_case: "\<lbrakk>\<And>tau r_s r_x r_ex env env_v ds tau_v r_sv r_xv r_mv c_list ds' t_sub.
           \<lbrakk>well_typed env id r_s e1 tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e1 tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds\<rbrakk>
           \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list);
        \<And>tau r_s r_x r_ex env env_v ds tau_v r_sv r_xv r_mv c_list ds' t_sub.
           \<lbrakk>well_typed env id r_s e2 tau (diff_use_env r_s r_ex) r_x; infer_type env_v ds e2 tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
            sub_range env_v ds; tsub_dom t_sub ds\<rbrakk>
           \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) ds' \<and>
                   fresh_list ds (dom_list l) \<and>
                   dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
                   (\<exists>p_sub. psub_dom p_sub (set_diff ds' ds) \<and>
                            leq_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv) r_s \<and>
                            leq_use_env (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_xv) r_ex) r_x \<and>
                            leq_use_env (cut_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub r_mv)) r_ex \<and>
                            dir_subst_type (dir_list_add_env t_sub l) p_sub tau_v tau \<and> dir_sol_sat (dir_list_add_env t_sub l) p_sub c_list);
        spec_env env_v env t_sub; sub_range env_v ds; tsub_dom t_sub ds; well_typed env id r_s e1 (FunTy t1 tau r a) r_s2 rx1;
        infer_type env_v ds e1 tau_f r_s1 r_x1 r_m1 cl1 ds2; well_typed env id r_s2 e2 t1 r_s3 rx2; infer_type env_v ds2 e2 t1a r_s2a r_x2 r_m2 cl2 ds3;
        leq_use_env (diff_use_env r_s r_ex) (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_exa));
        leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3; disj_use_env rx1 (lift_use_env rx2 r); leq_use_env r_x (diff_use_env r_s r_ex);
        leq_use_env r_exa r_s; leq_use_env (app_req rx1 rx2 r tau r_exa) r_x;
        finite_dom (comp_var_env (comp_var_env r_s1 r_x1) (comp_var_env r_s2a (lift_var_env r_x2 (SVar p)))) d; fresh_list ds3 [aa, p, q]\<rbrakk>
       \<Longrightarrow> \<exists>l. tsub_dom (dir_list_add_env t_sub l) (insert aa (insert p (insert q ds3))) \<and>
               fresh_list ds (dom_list l) \<and>
               dir_subst_tenv (dir_list_add_env t_sub l) env_v = env \<and>
               (\<exists>p_sub. psub_dom p_sub (set_diff (insert aa (insert p (insert q ds3))) ds) \<and>
                        leq_use_env
                         (dir_subst_penv (dir_list_add_env t_sub l) p_sub
                           (comp_var_env (comp_var_env r_s1 r_x1) (comp_var_env r_s2a (lift_var_env r_x2 (SVar p)))))
                         r_s \<and>
                        leq_use_env
                         (diff_use_env (dir_subst_penv (dir_list_add_env t_sub l) p_sub (ifz_var_env (XType aa) (comp_var_env r_x1 (lift_var_env r_x2 (SVar p)))))
                           r_ex)
                         r_x \<and>
                        leq_use_env
                         (cut_use_env
                           (dir_subst_penv (dir_list_add_env t_sub l) p_sub
                             (comp_var_env (comp_var_env r_m1 r_x1) (comp_var_env r_m2 (lift_var_env r_x2 (SVar p))))))
                         r_ex \<and>
                        dir_list_add_env t_sub l aa = Some tau \<and>
                        (\<exists>tau_x. (\<exists>t1_x. dir_subst_type (dir_list_add_env t_sub l) p_sub t1a t1_x \<and>
                                         (\<exists>t2_x. dir_list_add_env t_sub l aa = Some t2_x \<and> tau_x = FunTy t1_x t2_x (p_sub p) (as_aff (p_sub q)))) \<and>
                                 dir_subst_type (dir_list_add_env t_sub l) p_sub tau_f tau_x) \<and>
                        dir_sol_sat (dir_list_add_env t_sub l) p_sub
                         (disj_crn r_x1 (lift_var_env r_x2 (SVar p)) d @ semi_disj_crn r_m2 r_x1 d @ semi_disj_crn r_m1 r_s2a d @ cl1 @ cl2))" 
  apply (cut_tac env="env" and ?e1.0="e1" and ?e2.0="e2" in ivr_induct_format)
    apply (auto) 
  apply (cut_tac e="e1" and env_v="env_v" and t_sub="t_sub" and ds="ds" in ivrac_coerce)
        apply (auto)
  apply (cut_tac e="e2" and env_v="env_v" and t_sub="dir_list_add_env t_sub l" and ds="ds2" in ivrac_coerce)
        apply (auto)
    apply (rule_tac self_spec_env)
   apply (rule_tac ds="ds" in subset_sub_range)
    apply (simp)
   apply (rule_tac infer_x_subset)
   apply (auto)
  apply (rule_tac env_v="env_v" and r_s="r_s" and ?r_s3.0="r_s3" and ?e1.0="e1" and ?e2.0="e2" 
      and ?r_s1.0="r_s1" and ?r_x1.0="r_x1" and ?r_m1.0="r_m1" and r_s2a="r_s2a" and ?r_x2.0="r_x2" and ?r_m2.0="r_m2" in ivrac_main)
                      apply (auto)
  apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  apply (rule_tac well_typed_perm_leq)
  apply (auto)
  done
    
    (*
      [ Gamma, P |- e: tau, P - EX, Q \<and> Infer(Gamma*, X, e) = (tau*, P*, Q*, R*, K, X') \<and> \<sigma>( Gamma* ) = Gamma
        \<and> range( Gamma* ) \<subseteq> X \<and> dom(\<sigma>) \<subseteq> X ] \<Longrightarrow>
          (\<exists> \<sigma>* \<sigma>' \<rho>. \<sigma>' = \<sigma> o \<sigma>* \<and> dom(\<sigma>') \<subseteq> X \<and> fresh(\<sigma>*, X) \<and> \<sigma>'( Gamma* ) = Gamma
            \<and> dom( \<rho> ) \<subseteq> X' - X \<and> (\<sigma>', \<rho>)( P* ) \<le> P \<and> (\<sigma>', \<rho>)( Q* ) - EX \<le> Q \<and> (\<sigma>', \<rho>)( R* ) \<le> EX
            \<and> (\<sigma>', \<rho>)( tau* ) = tau \<and> (\<sigma>', \<rho>) |= K)
    *)
lemma ivr_partial: "\<lbrakk> well_typed env id r_s e tau (diff_use_env r_s r_ex) r_x;
  infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; spec_env env_v env t_sub;
  sub_range env_v ds; tsub_dom t_sub ds \<rbrakk> \<Longrightarrow>
  (\<exists> l t_subx p_sub. t_subx = dir_list_add_env t_sub l \<and> tsub_dom t_subx ds' \<and>
    fresh_list ds (dom_list l) \<and> dir_subst_tenv t_subx env_v = env \<and>
    psub_dom p_sub (set_diff ds' ds) \<and> leq_use_env (dir_subst_penv t_subx p_sub r_sv) r_s \<and>
    leq_use_env (diff_use_env (dir_subst_penv t_subx p_sub r_xv) r_ex) r_x \<and> leq_use_env (cut_use_env (dir_subst_penv t_subx p_sub r_mv)) r_ex \<and>
    dir_subst_type t_subx p_sub tau_v tau \<and> dir_sol_sat t_subx p_sub c_list)"  
  apply (induct e arbitrary: tau r_s r_x r_ex env env_v ds tau_v r_sv r_xv r_mv c_list ds' t_sub)
        apply (auto)
    (* const case *)
        apply (rule_tac ivr_const_case)
              apply (auto)
    (* op case *)
       apply (rule_tac ivr_op_case)
           apply (auto)
    (* var case *)
      apply (rule_tac ivr_var_case)
                   apply (auto)
    (* pair case *)
     apply (rule_tac ivr_pair_case)
                      apply (auto)
    (* if case *)
    apply (rule_tac ivr_if_case)
                apply (auto)
    (* lam case *)
   apply (rule_tac ivr_lam_case)
                    apply (auto)
    (* app case *)
  apply (rule_tac ivr_app_case)
                  apply (auto)
  done
    
definition no_mv_env where
  "no_mv_env env = (\<forall> x. case x of
    Var x \<Rightarrow> True
    | Loc y \<Rightarrow> env (Loc y) = None
  )"
    
lemma well_typed_id_delta: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; no_mv_env env \<rbrakk> \<Longrightarrow> well_typed env id r_s1 e tau r_s2 rx"    
  apply (induct e arbitrary: env delta r_s1 tau r_s2 rx)
        apply (auto)
    (* var case *)
      apply (case_tac x)
       apply (auto)
       apply (simp add: no_mv_env_def)
       apply (erule_tac x="Loc x2" in allE)
       apply (auto)
      apply (simp add: no_mv_env_def)
      apply (erule_tac x="Loc x2" in allE)
      apply (auto)
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
    (* lam case *)
   apply (case_tac "\<not> no_mv_env (add_env env (Var x1a) t1)")
    apply (simp add: no_mv_env_def)
    apply (auto)
    apply (erule_tac x="x" in allE)
    apply (case_tac x)
     apply (auto)
    apply (simp add: add_env_def)
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
    
lemma infer_valid_right: "\<lbrakk> well_typed empty_env delta r_s1 e tau r_s2 rx; infer_type empty_env ds e tau_v r_sv r_xv r_mv c_list ds' \<rbrakk> \<Longrightarrow> \<exists> t_sub p_sub. dir_sol_sat t_sub p_sub c_list"
  apply (cut_tac env="empty_env" and env_v="empty_env" and e="e" and r_s="r_s1" and r_x="diff_use_env rx r_s1" and r_ex="r_s1" and t_sub="empty_env" in ivr_partial)
       apply (auto)
     apply (rule_tac well_typed_end_perm_lbound)
     apply (rule_tac well_typed_id_delta)
      apply (simp)
     apply (simp add: no_mv_env_def)
     apply (auto)
     apply (case_tac x)
      apply (auto)
     apply (simp add: empty_env_def)
    apply (simp add: spec_env_def)
    apply (simp add: empty_env_def)
   apply (simp add: sub_range_def)
   apply (simp add: empty_env_def)
  apply (simp add: tsub_dom_def)
  apply (simp add: empty_env_def)
  done

end