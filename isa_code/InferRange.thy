theory InferRange
  imports InferDef
begin
  
    (* ##### random mechnical lemmas *)
  
lemma trip_convert: "as_aff (as_perm a) = a"    
  apply (case_tac a)
    apply (auto)
  done  
    
lemma infer_x_subset_ih: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; x \<in> ds \<rbrakk> \<Longrightarrow> x \<in> ds'"    
  apply (induct e arbitrary: env_v ds tau_v r_sv r_xv r_mv c_list ds')
        apply (auto)
  apply (case_tac xa)
              apply (auto)
  done
    
lemma infer_x_subset: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds' \<rbrakk> \<Longrightarrow> ds \<subseteq> ds'"    
  apply (auto)
  apply (rule_tac infer_x_subset_ih)
   apply (auto)
  done  
  
    (*  ##### direct type substitution composition *)
  
definition dir_add_env where
  "dir_add_env t_sub a tau = (\<lambda> a'. if a' = a then Some tau else t_sub a')"  
  
fun dir_list_add_env where
  "dir_list_add_env t_sub [] = t_sub"  
| "dir_list_add_env t_sub ((a, tau) # a_t) = dir_add_env (dir_list_add_env t_sub a_t) a tau"
  
  
    (* #### domain / range based lemmas *)

definition sub_range where
  "sub_range env_v ds = (\<forall> x. case env_v x of
    None \<Rightarrow> True
    | Some a \<Rightarrow> a \<in> ds
  )"  
  
definition tsub_dom where
  "tsub_dom t_sub ds = (\<forall> a. t_sub a \<noteq> None \<longrightarrow> a \<in> ds)"

definition psub_dom where
  "psub_dom p_sub ds = (\<forall> a. p_sub a \<noteq> NoPerm \<longrightarrow> a \<in> ds)"
  
definition set_diff :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "set_diff s1 s2 = s1 - s2"  
  
fun dom_list where
  "dom_list [] = []"  
| "dom_list ((x, v) # t) = x # (dom_list t)"  
  
fun dom_list_set where
  "dom_list_set [] = {}"  
| "dom_list_set ((x, v) # t) = ({x} \<union> dom_list_set t)"    
  
lemma dir_add_eq_env: "\<lbrakk> dir_subst_tenv t_sub env_v = env; sub_range env_v ds; a \<notin> ds \<rbrakk> \<Longrightarrow>
  dir_subst_tenv (dir_add_env t_sub a tau) env_v = env"    
  apply (auto)
  apply (case_tac "\<forall> x. dir_subst_tenv (dir_add_env t_sub a tau) env_v x = env x")
   apply (auto)
  apply (simp add: dir_subst_tenv_def)
  apply (simp add: sub_range_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "env_v x")
   apply (auto)
  apply (simp add: dir_add_env_def)
  apply (case_tac "a = aa")
   apply (auto)
  done  
    
lemma dir_list_append_eq_env_ih: "dir_subst_tenv (dir_list_add_env t_sub (l @ la)) env_v x = dir_subst_tenv (dir_list_add_env (dir_list_add_env t_sub la) l) env_v x"    
  apply (induct l)
   apply (auto)
  apply (simp add: dir_subst_tenv_def)
  apply (case_tac "env_v x")
   apply (auto)
  apply (simp add: dir_add_env_def)
  done
  
lemma dir_list_append_eq_env: "dir_subst_tenv (dir_list_add_env t_sub (l @ la)) env_v = dir_subst_tenv (dir_list_add_env (dir_list_add_env t_sub la) l) env_v"
  apply (case_tac "\<forall> x. dir_subst_tenv (dir_list_add_env t_sub (l @ la)) env_v x = dir_subst_tenv (dir_list_add_env (dir_list_add_env t_sub la) l) env_v x")
   apply (auto)
  apply (cut_tac t_sub="t_sub" and x="x" in dir_list_append_eq_env_ih)
  apply (auto)
  done

lemma dir_list_dist_add_eq_env_ih: "\<lbrakk> dir_subst_tenv t_sub env_v x = dir_subst_tenv t_sub' env_v x \<rbrakk> \<Longrightarrow>
  dir_subst_tenv (dir_list_add_env t_sub l) env_v x = dir_subst_tenv (dir_list_add_env t_sub' l) env_v x"
  apply (induct l)
   apply (auto)
  apply (simp add: dir_subst_tenv_def)
  apply (case_tac "env_v x")
   apply (auto)
  apply (simp add: dir_add_env_def)
  done
    
lemma dir_list_dist_add_eq_env: "\<lbrakk> dir_subst_tenv t_sub env_v = dir_subst_tenv t_sub' env_v \<rbrakk> \<Longrightarrow>
  dir_subst_tenv (dir_list_add_env t_sub l) env_v = dir_subst_tenv (dir_list_add_env t_sub' l) env_v"
  apply (case_tac "\<forall> x. dir_subst_tenv (dir_list_add_env t_sub l) env_v x = dir_subst_tenv (dir_list_add_env t_sub' l) env_v x")
   apply (auto)
  apply (cut_tac t_sub="t_sub" and x="x" and t_sub'="t_sub'" in dir_list_dist_add_eq_env_ih)
   apply (auto)
  done
    
lemma dir_list_cancel_add_eq_env_ih: "\<lbrakk> sub_range env_v ds; fresh_list ds (dom_list l) \<rbrakk> \<Longrightarrow>
  dir_subst_tenv (dir_list_add_env t_sub l) env_v x = dir_subst_tenv t_sub env_v x"      
  apply (induct l)
   apply (auto)
  apply (simp add: dir_subst_tenv_def)
  apply (case_tac "env_v x")
   apply (auto)
  apply (simp add: dir_add_env_def)
  apply (auto)
   apply (simp add: sub_range_def)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (simp add: fresh_list_def)
   apply (auto)
  apply (case_tac "\<not> fresh_list ds (dom_list l)")
   apply (auto)
  apply (simp add: fresh_list_def)
  done
    
lemma dir_list_cancel_add_eq_env: "\<lbrakk> sub_range env_v ds; fresh_list ds (dom_list l) \<rbrakk> \<Longrightarrow>
  dir_subst_tenv (dir_list_add_env t_sub l) env_v = dir_subst_tenv t_sub env_v"    
  apply (case_tac "\<forall> x. dir_subst_tenv (dir_list_add_env t_sub l) env_v x = dir_subst_tenv t_sub env_v x")
   apply (auto)
  apply (cut_tac t_sub="t_sub" and x="x" in dir_list_cancel_add_eq_env_ih)
    apply (auto)
  done
    
  
lemma subset_tsub_dom: "\<lbrakk> tsub_dom t_sub ds; ds \<subseteq> ds' \<rbrakk> \<Longrightarrow> tsub_dom t_sub ds'"    
  apply (simp add: tsub_dom_def)
  apply (auto)
  done
  
lemma add_tsub_dom: "\<lbrakk> tsub_dom t_sub ds; x \<in> ds \<rbrakk> \<Longrightarrow> tsub_dom (dir_add_env t_sub x tau) ds"        
  apply (simp add: tsub_dom_def)
  apply (simp add: dir_add_env_def)
  done

lemma add_tsub_dom_rev: "\<lbrakk> tsub_dom (dir_add_env t_sub x tau) ds \<rbrakk> \<Longrightarrow> tsub_dom t_sub ds"        
  apply (simp add: tsub_dom_def)
  apply (simp add: dir_add_env_def)
  done    
    
lemma list_add_tsub_dom: "\<lbrakk> tsub_dom t_sub ds; ds \<subseteq> ds'; dom_list_set l \<subseteq> ds' \<rbrakk> \<Longrightarrow> tsub_dom (dir_list_add_env t_sub l) ds'"    
  apply (induct l)
   apply (auto)
   apply (simp add: subset_tsub_dom)
  apply (rule_tac add_tsub_dom)
   apply (auto)
  done
 
lemma list_add_tsub_dom_rev: "\<lbrakk> tsub_dom (dir_list_add_env t_sub l) ds \<rbrakk> \<Longrightarrow> tsub_dom t_sub ds"       
  apply (induct l)
   apply (auto)
  apply (cut_tac t_sub="dir_list_add_env t_sub l" and x="a" in add_tsub_dom_rev)
   apply (auto)
  done
  
lemma append_tsub_dom: "\<lbrakk> tsub_dom (dir_list_add_env t_sub l2) ds; dom_list_set l1 \<subseteq> ds \<rbrakk> \<Longrightarrow> tsub_dom (dir_list_add_env t_sub (l1 @ l2)) ds"     
  apply (induct l1)
   apply (auto)
  apply (rule_tac add_tsub_dom)
   apply (auto)
  done
  
lemma subset_psub_dom: "\<lbrakk> psub_dom p_sub ds; ds \<subseteq> ds' \<rbrakk> \<Longrightarrow> psub_dom p_sub ds'"    
  apply (simp add: psub_dom_def)
  apply (auto)
  done
  
lemma empty_psub_dom: "psub_dom empty_use_env ds"       
  apply (simp add: psub_dom_def)
  apply (simp add: empty_use_env_def)
  done
    
lemma add_psub_dom: "\<lbrakk> psub_dom p_sub ds; x \<in> ds \<rbrakk> \<Longrightarrow> psub_dom (add_use_env p_sub x p) ds"        
  apply (simp add: psub_dom_def)
  apply (simp add: add_use_env_def)
  done    
 
lemma comp_psub_dom: "\<lbrakk> psub_dom p_sub1 ds; psub_dom p_sub2 ds \<rbrakk> \<Longrightarrow> psub_dom (comp_use_env p_sub1 p_sub2) ds"        
  apply (simp add: psub_dom_def)
  apply (auto)
  apply (simp add: comp_use_env_def)
  apply (case_tac "p_sub1 a = NoPerm")
   apply (auto)
  apply (case_tac "p_sub2 a = NoPerm")
   apply (auto)
  done        
    
lemma subset_sub_range: "\<lbrakk> sub_range env_v ds; ds \<subseteq> ds' \<rbrakk> \<Longrightarrow> sub_range env_v ds'"    
  apply (simp add: sub_range_def)
  apply (auto)
  apply (case_tac "env_v x")
   apply (auto)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done
    
lemma list_add_dls: "\<lbrakk> tsub_dom (dir_list_add_env t_sub l) ds \<rbrakk> \<Longrightarrow> dom_list_set l \<subseteq> ds"      
  apply (induct l)
   apply (auto)
   apply (simp add: tsub_dom_def)
   apply (simp add: dir_add_env_def)
  apply (cut_tac t_sub="dir_list_add_env t_sub l" and x="a" in add_tsub_dom_rev)
   apply (auto)
  done    
    
  
    (* #### p_exp range *)
    
fun pvar_set_perm where
  "pvar_set_perm (SPerm p) = {}"
| "pvar_set_perm (SVar x) = {x}" 
  
fun pvar_set where
  "pvar_set (XPerm p) = pvar_set_perm p"
| "pvar_set (XType a) = {}"
| "pvar_set (XComp px qx) = (pvar_set px \<union> pvar_set qx)"
| "pvar_set (XLift px q) = (pvar_set px \<union> pvar_set_perm q)"    
| "pvar_set (XIfZero px qx) = (pvar_set px \<union> pvar_set qx)"  
  
definition pvar_range where
  "pvar_range r_sv ds = (\<forall> a. pvar_set (r_sv a) \<subseteq> ds)"  
  
lemma empty_pvar_range: "pvar_range empty_var_env ds"  
  apply (simp add: pvar_range_def)
  apply (simp add: empty_var_env_def)
  done
    
lemma comp_pvar_range: "\<lbrakk> pvar_range r_sv ds; pvar_range r_xv ds \<rbrakk> \<Longrightarrow> pvar_range (comp_var_env r_sv r_xv) ds"    
  apply (simp add: pvar_range_def)
  apply (simp add: comp_var_env_def)
  done
    
lemma lift_pvar_range: "\<lbrakk> pvar_range r_sv ds; pvar_set_perm p \<subseteq> ds \<rbrakk> \<Longrightarrow> pvar_range (lift_var_env r_sv p) ds"    
  apply (simp add: pvar_range_def)
  apply (simp add: lift_var_env_def)
  done

fun tvar_set where
  "tvar_set (XPerm p) = {}"
| "tvar_set (XType a) = {a}"
| "tvar_set (XComp px qx) = (tvar_set px \<union> tvar_set qx)"
| "tvar_set (XLift px q) = (tvar_set px)"    
| "tvar_set (XIfZero px qx) = (tvar_set px \<union> tvar_set qx)"  
  
definition tvar_range where
  "tvar_range r_sv ds = (\<forall> a. tvar_set (r_sv a) \<subseteq> ds)"      
 
lemma empty_tvar_range: "tvar_range empty_var_env ds"  
  apply (simp add: tvar_range_def)
  apply (simp add: empty_var_env_def)
  done
    
lemma comp_tvar_range: "\<lbrakk> tvar_range r_sv ds; tvar_range r_xv ds \<rbrakk> \<Longrightarrow> tvar_range (comp_var_env r_sv r_xv) ds"    
  apply (simp add: tvar_range_def)
  apply (simp add: comp_var_env_def)
  done
    
lemma lift_tvar_range: "\<lbrakk> tvar_range r_sv ds; tvar_set_perm p \<subseteq> ds \<rbrakk> \<Longrightarrow> tvar_range (lift_var_env r_sv p) ds"    
  apply (simp add: tvar_range_def)
  apply (simp add: lift_var_env_def)
  done    
  
lemma subset_pvar_range: "\<lbrakk> pvar_range p_sub ds; ds \<subseteq> ds' \<rbrakk> \<Longrightarrow> pvar_range p_sub ds'"  
  apply (simp add: pvar_range_def)
  apply (auto)
  done  
  
lemma set_diff_subset: "\<lbrakk> ds3 \<subseteq> ds4; ds \<subseteq> ds2 \<rbrakk> \<Longrightarrow> set_diff ds3 ds2 \<subseteq> set_diff ds4 ds"    
  apply (simp add: set_diff_def)
  apply (auto)
  done
    
lemma ifz_pvar_range: "\<lbrakk> pvar_range r_sv ds; pvar_set px \<subseteq> ds \<rbrakk> \<Longrightarrow> pvar_range (ifz_var_env px r_sv) ds"    
  apply (simp add: pvar_range_def)
  apply (simp add: ifz_var_env_def)
  done      

lemma rem_pvar_range: "\<lbrakk> pvar_range r_sv ds \<rbrakk> \<Longrightarrow> pvar_range (rem_var_env r_sv x) ds"    
  apply (simp add: pvar_range_def)
  apply (simp add: rem_var_env_def)
  done     
    
lemma comp_pvar_range_rev1: "\<lbrakk> pvar_range (comp_var_env r_sv r_xv) ds \<rbrakk> \<Longrightarrow> pvar_range r_sv ds"    
  apply (simp add: pvar_range_def)
  apply (simp add: comp_var_env_def)
  apply (auto)
  apply (erule_tac x="a" in allE)
  apply (case_tac "r_sv a = XPerm (SPerm NoPerm) \<and> r_xv a = XPerm (SPerm NoPerm)")
   apply (auto)
  done

lemma comp_pvar_range_rev2: "\<lbrakk> pvar_range (comp_var_env r_sv r_xv) ds \<rbrakk> \<Longrightarrow> pvar_range r_xv ds"    
  apply (simp add: pvar_range_def)
  apply (simp add: comp_var_env_def)
  apply (auto)
  apply (erule_tac x="a" in allE)
  apply (case_tac "r_sv a = XPerm (SPerm NoPerm) \<and> r_xv a = XPerm (SPerm NoPerm)")
   apply (auto)
  done
    
lemma dir_add_eq_permx: "\<lbrakk> tvar_set px \<subseteq> ds; a \<notin> ds \<rbrakk> \<Longrightarrow>
  dir_subst_permx (dir_add_env t_sub a tau) p_sub px = dir_subst_permx t_sub p_sub px"    
  apply (induct px)
      apply (auto)
  apply (case_tac "t_sub x")
   apply (auto)
   apply (simp_all add: dir_add_env_def)
   apply (auto)
  done
    
lemma dir_add_cancel_use_env_ih: "\<lbrakk> tvar_range r_sv ds; a \<notin> ds \<rbrakk> \<Longrightarrow>
  dir_subst_penv (dir_add_env t_sub a tau) p_sub r_sv x = dir_subst_penv t_sub p_sub r_sv x"       
  apply (simp add: dir_subst_penv_def)
  apply (cut_tac t_sub="t_sub" and a="a" and ds="ds" and px="r_sv x" in dir_add_eq_permx)
    apply (simp add: tvar_range_def)
   apply (simp_all)
  done
    
lemma dir_list_add_cancel_use_env_ih: "\<lbrakk> tvar_range r_sv ds; fresh_list ds (dom_list l) \<rbrakk> \<Longrightarrow>
  dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv x = dir_subst_penv t_sub p_sub r_sv x"       
  apply (induct l)
   apply (auto)
  apply (simp add: dir_subst_penv_def)
  apply (cut_tac t_sub="dir_list_add_env t_sub l" and p_sub="p_sub" and a="a" and tau="b" and x="x" and ds="ds" in dir_add_cancel_use_env_ih)
    apply (auto)
   apply (simp add: fresh_list_def)
   apply (auto)
  apply (simp add: dir_subst_penv_def)
  apply (simp add: fresh_list_def)
  done
    
lemma dir_list_add_cancel_use_env: "\<lbrakk> tvar_range r_sv ds; fresh_list ds (dom_list l) \<rbrakk> \<Longrightarrow>
  dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv = dir_subst_penv t_sub p_sub r_sv"    
  apply (case_tac "\<forall> x. dir_subst_penv (dir_list_add_env t_sub l) p_sub r_sv x = dir_subst_penv t_sub p_sub r_sv x")
   apply (auto)
  apply (cut_tac t_sub="t_sub" and x="x" in dir_list_add_cancel_use_env_ih)
    apply (auto)
  done    
    
lemma ifz_tvar_range: "\<lbrakk> tvar_range r_sv ds; tvar_set px \<subseteq> ds \<rbrakk> \<Longrightarrow> tvar_range (ifz_var_env px r_sv) ds"    
  apply (simp add: tvar_range_def)
  apply (simp add: ifz_var_env_def)
  done         
    
lemma infer_s_sub_range: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds' \<rbrakk> \<Longrightarrow> pvar_range r_sv (set_diff ds' ds) \<and> pvar_range r_xv (set_diff ds' ds)"    
  apply (induct e arbitrary: env_v ds tau_v r_sv r_xv r_mv c_list ds')
        apply (auto)
    (* const + op + var cases *)
             apply (rule_tac empty_pvar_range)
            apply (rule_tac empty_pvar_range)
           apply (simp add: pvar_range_def)
           apply (simp add: one_var_env_def)
          apply (simp add: pvar_range_def)
          apply (simp add: one_var_env_def)
    (* pair case *)
         apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
          apply (auto)
         apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
          apply (auto)
         apply (rule_tac comp_pvar_range)
          apply (rule_tac comp_pvar_range)
           apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
            apply (simp)
           apply (simp add: set_diff_def)
           apply (auto)
          apply (rule_tac lift_pvar_range)
           apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
            apply (simp)
           apply (simp add: set_diff_def)
           apply (auto)
          apply (simp add: set_diff_def)
          apply (auto)
          apply (rule_tac comp_pvar_range)
          apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
           apply (simp)
          apply (simp add: set_diff_def)
          apply (auto)
         apply (rule_tac lift_pvar_range)
          apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
           apply (simp)
          apply (simp add: set_diff_def)
          apply (auto)
         apply (simp add: set_diff_def)
         apply (auto)
        apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
         apply (auto)
        apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
         apply (auto)
        apply (rule_tac ifz_pvar_range)
         apply (rule_tac comp_pvar_range)
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
        apply (simp add: set_diff_def)
        apply (auto)
    (* if case *)
       apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
        apply (auto)
       apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
        apply (auto)
       apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
        apply (auto)
       apply (rule_tac comp_pvar_range)
        apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
         apply (simp)
        apply (simp add: set_diff_def)
        apply (auto)
       apply (rule_tac comp_pvar_range)
        apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
         apply (simp)
        apply (simp add: set_diff_def)
        apply (auto)
       apply (rule_tac ds="set_diff ds' ds3" in subset_pvar_range)
        apply (simp)
       apply (simp add: set_diff_def)
       apply (auto)
      apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
       apply (auto)
      apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
       apply (auto)
      apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
       apply (auto)
      apply (rule_tac comp_pvar_range)
       apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
        apply (auto)
       apply (simp add: set_diff_def)
       apply (auto)
      apply (rule_tac ds="set_diff ds' ds3" in subset_pvar_range)
       apply (auto)
      apply (simp add: set_diff_def)
      apply (auto)
    (* lam case *)
     apply (cut_tac ds="insert a ds" and ds'="ds2" in infer_x_subset)
      apply (auto)
     apply (rule_tac rem_pvar_range)
     apply (rule_tac ds="set_diff ds2 (insert a ds)" in subset_pvar_range)
      apply (simp)
     apply (simp add: set_diff_def)
    apply (auto)
    apply (cut_tac ds="insert a ds" and ds'="ds2" in infer_x_subset)
     apply (auto)
    apply (rule_tac rem_pvar_range)
    apply (rule_tac ds="set_diff ds2 (insert a ds)" in subset_pvar_range)
     apply (simp)
    apply (simp add: set_diff_def)
    apply (auto)
    (* app case *)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
    apply (auto)
   apply (rule_tac comp_pvar_range)
    apply (rule_tac comp_pvar_range)
     apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
      apply (simp)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
     apply (simp)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (rule_tac comp_pvar_range)
    apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
     apply (simp)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (rule_tac lift_pvar_range)
    apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
     apply (simp)
    apply (simp add: set_diff_def)
    apply (auto)
   apply (simp add: set_diff_def)
   apply (auto)
   apply (case_tac "p \<in> ds3")
    apply (simp add: fresh_list_def)
    apply (auto)
  apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
   apply (auto)
  apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
   apply (auto)
  apply (rule_tac ifz_pvar_range)
   apply (rule_tac comp_pvar_range)
    apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
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
   apply (case_tac "p \<in> ds3")
    apply (simp add: fresh_list_def)
    apply (auto)(*
  apply (simp add: set_diff_def)
  apply (case_tac "p_a \<in> ds3")
   apply (simp add: fresh_list_def)
   apply (auto)*)
  done

lemma add_sub_range: "\<lbrakk> sub_range env_v ds \<rbrakk> \<Longrightarrow> sub_range (add_env env_v x a) (insert a ds)"      
  apply (simp add: sub_range_def)
  apply (simp add: add_env_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (case_tac "env_v xa")
   apply (auto)
  done
    
lemma infer_m_sub_range: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds' \<rbrakk> \<Longrightarrow> pvar_range r_mv (set_diff ds' ds)"    
  apply (induct e arbitrary: env_v ds tau_v r_sv r_xv r_mv c_list ds')
        apply (auto)
    (* const + op + var cases *)
        apply (rule_tac empty_pvar_range)
       apply (rule_tac empty_pvar_range)
      apply (simp add: pvar_range_def)
      apply (simp add: one_var_env_def)
    (* pair case *)
     apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
      apply (auto)
     apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
      apply (auto)
     apply (rule_tac comp_pvar_range)
      apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
       apply (simp)
      apply (simp add: set_diff_def)
      apply (auto)
     apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
      apply (simp)
     apply (simp add: set_diff_def)
     apply (auto)
    (* if case *)
    apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (auto)
    apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
     apply (auto)
    apply (rule_tac comp_pvar_range)
     apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
      apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (rule_tac comp_pvar_range)
     apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
      apply (auto)
     apply (simp add: set_diff_def)
     apply (auto)
    apply (rule_tac ds="set_diff ds' ds3" in subset_pvar_range)
     apply (auto)
    apply (simp add: set_diff_def)
    apply (auto)
    (* lam case *)
   apply (rule_tac empty_pvar_range)
    (* app case *)
  apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
   apply (auto)
  apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
   apply (auto)
  apply (rule_tac comp_pvar_range)
   apply (rule_tac ds="set_diff ds2 ds" in subset_pvar_range)
    apply (rule_tac comp_pvar_range)
     apply (auto)
    apply (cut_tac env_v="env_v" and r_xv="r_x1" and ds'="ds2" in infer_s_sub_range)
     apply (auto)
   apply (simp add: set_diff_def)
   apply (auto)
  apply (rule_tac comp_pvar_range)
   apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
    apply (auto)
   apply (simp add: set_diff_def)
   apply (auto)
  apply (rule_tac lift_pvar_range)
   apply (rule_tac ds="set_diff ds3 ds2" in subset_pvar_range)
    apply (auto)
    apply (cut_tac env_v="env_v" and r_xv="r_x2" and ds'="ds3" in infer_s_sub_range)
     apply (auto)
   apply (simp add: set_diff_def)
   apply (auto)
  apply (case_tac "p \<in> ds3")
   apply (simp add: fresh_list_def)
   apply (auto)
  apply (simp add: set_diff_def)
  apply (auto)
  done
    
lemma rem_tvar_range: "\<lbrakk> tvar_range r_sv ds \<rbrakk> \<Longrightarrow> tvar_range (rem_var_env r_sv x) ds"    
  apply (simp add: tvar_range_def)
  apply (simp add: rem_var_env_def)
  done      
    
lemma subset_tvar_range: "\<lbrakk> tvar_range r_sv ds; ds \<subseteq> ds' \<rbrakk> \<Longrightarrow> tvar_range r_sv ds'"
  apply (simp add: tvar_range_def)
  apply (auto)
  done
    
lemma infer_tvar_range: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; sub_range env_v ds \<rbrakk> \<Longrightarrow>
    tvar_range r_sv ds' \<and> tvar_range r_xv ds'" 
  apply (induct e arbitrary: env_v ds tau_v r_sv r_xv r_mv c_list ds')
        apply (auto)
    (* const + op + var cases *)
             apply (rule_tac empty_tvar_range)
            apply (rule_tac empty_tvar_range)
           apply (simp add: tvar_range_def)
           apply (simp add: one_var_env_def)
           apply (simp add: sub_range_def)
           apply (erule_tac x="Var x'" in allE)
           apply (auto)
          apply (simp add: tvar_range_def)
          apply (simp add: one_var_env_def)
          apply (simp add: sub_range_def)
          apply (erule_tac x="Var x'" in allE)
          apply (auto)
    (* pair case *)
         apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
          apply (auto)
         apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
          apply (auto)
         apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
           apply (auto)
         apply (rule_tac comp_tvar_range)
          apply (rule_tac ds="ds2" in subset_tvar_range)
           apply (auto)
          apply (rule_tac comp_tvar_range)
           apply (simp)
          apply (rule_tac lift_tvar_range)
           apply (auto)
         apply (rule_tac ds="ds3" in subset_tvar_range)
          apply (auto)
         apply (rule_tac comp_tvar_range)
          apply (simp)
         apply (rule_tac lift_tvar_range)
          apply (auto)
        apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
         apply (auto)
        apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
         apply (auto)
        apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
          apply (auto)
        apply (rule_tac ifz_tvar_range)
         apply (rule_tac comp_tvar_range)
          apply (rule_tac lift_tvar_range)
           apply (rule_tac ds="ds2" in subset_tvar_range)
            apply (auto)
        apply (rule_tac lift_tvar_range)
         apply (auto)
        apply (rule_tac ds="ds3" in subset_tvar_range)
         apply (auto)
    (* if case *)
       apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
        apply (auto)
       apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
        apply (auto)
       apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
        apply (auto)
       apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
         apply (auto)
       apply (cut_tac env_v="env_v" and ds="ds2" and ds'="ds3" in subset_sub_range)
         apply (auto)
       apply (rule_tac comp_tvar_range)
        apply (rule_tac ds="ds2" in subset_tvar_range)
         apply (auto)
       apply (rule_tac comp_tvar_range)
        apply (auto)
       apply (rule_tac ds="ds3" in subset_tvar_range)
        apply (auto)
      apply (rule_tac ds="ds'" in subset_tvar_range)
       apply (auto)
      apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
       apply (auto)
      apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
       apply (auto)
      apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
       apply (auto)
      apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
        apply (auto)
      apply (cut_tac env_v="env_v" and ds="ds2" and ds'="ds3" in subset_sub_range)
        apply (auto)
      apply (rule_tac comp_tvar_range)
       apply (auto)
      apply (rule_tac ds="ds3" in subset_tvar_range)
       apply (auto)
    (* lam case *)
     apply (cut_tac env_v="env_v" and ds="ds" and x="Var x1a" and a="a" in add_sub_range)
      apply (auto)
     apply (rule_tac rem_tvar_range)
     apply (rule_tac ds="ds2" in subset_tvar_range)
      apply (auto)
    apply (cut_tac env_v="env_v" and ds="ds" and x="Var x1a" and a="a" in add_sub_range)
     apply (auto)
    apply (rule_tac rem_tvar_range)
    apply (rule_tac ds="ds2" in subset_tvar_range)
     apply (auto)
    (* app case *)
   apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
    apply (auto)
   apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
    apply (auto)
   apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
     apply (auto)
   apply (rule_tac comp_tvar_range)
    apply (rule_tac ds="ds2" in subset_tvar_range)
     apply (auto)
    apply (rule_tac comp_tvar_range)
     apply (auto)
   apply (rule_tac ds="ds3" in subset_tvar_range)
    apply (auto)
   apply (rule_tac comp_tvar_range)
    apply (auto)
   apply (rule_tac lift_tvar_range)
    apply (auto)
  apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
   apply (auto)
  apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
   apply (auto)
  apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
    apply (auto)
  apply (rule_tac ifz_tvar_range)
   apply (rule_tac comp_tvar_range)
    apply (rule_tac ds="ds2" in subset_tvar_range)
     apply (auto)
  apply (rule_tac lift_tvar_range)
   apply (rule_tac ds="ds3" in subset_tvar_range)
    apply (auto)
  done  

lemma infer_m_tvar_range: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; sub_range env_v ds \<rbrakk> \<Longrightarrow> tvar_range r_mv ds'"    
  apply (induct e arbitrary: env_v ds tau_v r_sv r_xv r_mv c_list ds')
        apply (auto)
    (* const + op + var cases *)
        apply (rule_tac empty_tvar_range)
       apply (rule_tac empty_tvar_range)
      apply (simp add: tvar_range_def)
      apply (simp add: one_var_env_def)
      apply (simp add: sub_range_def)
      apply (erule_tac x="Var x'" in allE)
      apply (auto)
    (* pair case *)
     apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
      apply (auto)
     apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
      apply (auto)
     apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
       apply (auto)
     apply (rule_tac comp_tvar_range)
      apply (rule_tac ds="ds2" in subset_tvar_range)
       apply (auto)
     apply (rule_tac ds="ds3" in subset_tvar_range)
      apply (auto)
    (* if case *)
    apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
     apply (auto)
    apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
     apply (auto)
    apply (cut_tac ds="ds3" and ds'="ds'" in infer_x_subset)
     apply (auto)
    apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
      apply (auto)
    apply (cut_tac env_v="env_v" and ds="ds2" and ds'="ds3" in subset_sub_range)
      apply (auto)
    apply (rule_tac comp_tvar_range)
     apply (rule_tac ds="ds2" in subset_tvar_range)
      apply (auto)
    apply (rule_tac comp_tvar_range)
     apply (rule_tac ds="ds3" in subset_tvar_range)
      apply (auto)
    (* lam case *)
  apply (rule_tac empty_tvar_range)
    (* app case *)
  apply (cut_tac ds="ds" and ds'="ds2" in infer_x_subset)
   apply (auto)
  apply (cut_tac ds="ds2" and ds'="ds3" in infer_x_subset)
   apply (auto)
  apply (cut_tac env_v="env_v" and ds="ds" and ds'="ds2" in subset_sub_range)
    apply (auto)
  apply (rule_tac comp_tvar_range)
   apply (rule_tac ds="ds2" in subset_tvar_range)
    apply (rule_tac comp_tvar_range)
     apply (auto)
   apply (cut_tac env_v="env_v" and r_xv="r_x1" and ds'="ds2" in infer_tvar_range)
     apply (auto)
  apply (rule_tac comp_tvar_range)
   apply (rule_tac ds="ds3" in subset_tvar_range)
    apply (auto)
  apply (rule_tac lift_tvar_range)
   apply (rule_tac ds="ds3" in subset_tvar_range)
    apply (auto)
  apply (cut_tac env_v="env_v" and ds="ds2" and r_xv="r_x2" and ds'="ds3" in infer_tvar_range)
    apply (auto)
  done    
    
fun tvar_type where
  "tvar_type IntScheme = {}"
  | "tvar_type BoolScheme = {}"
  | "tvar_type UnitScheme = {}"
  | "tvar_type (VarScheme a) = {a}"
  | "tvar_type (ArrayScheme tau) = tvar_type tau"
  | "tvar_type (PairScheme t1 t2 p) = tvar_type t1 \<union> tvar_type t2"
  | "tvar_type (FunScheme t1 t2 p a) = tvar_type t1 \<union> tvar_type t2"
  | "tvar_type (ChanScheme tau c_end) = tvar_type tau"     
    
end
