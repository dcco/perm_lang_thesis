theory SolverInfer
  imports InferSound InferComplete SolverP3
begin

fun no_mem_val where
  "no_mem_val (VarExp x) = (case x of
    VarType x \<Rightarrow> True
    | LocType x \<Rightarrow> False
  )"
| "no_mem_val (PairExp e1 e2) = (no_mem_val e1 \<and> no_mem_val e2)"
| "no_mem_val (IfExp e1 e2 e3) = (no_mem_val e1 \<and> no_mem_val e2 \<and> no_mem_val e3)"
| "no_mem_val (LamExp x e) = no_mem_val e"
| "no_mem_val (AppExp e1 e2) = (no_mem_val e1 \<and> no_mem_val e2)"
| "no_mem_val e = True"
  
definition unique_env where
  "unique_env env_v = (\<forall> x. case env_v x of
    None \<Rightarrow> True
    | Some a \<Rightarrow> (\<forall> y. case env_v y of
      None \<Rightarrow> True
      | Some b \<Rightarrow> x = y \<or> a \<noteq> b
    )
  )"
  
definition dom_cover where
  "dom_cover env_v ds = (\<forall> x. x \<in> ds \<longrightarrow> env_v x \<noteq> None)"  
  
definition dom_ex_cover where
  "dom_ex_cover env_v ds = (\<forall> x. (x \<in> ds) = (env_v x \<noteq> None))"
  
definition same_dom_env where
  "same_dom_env env_v env = (\<forall> x. (env_v x = None) = (env x = None))"  

definition rev_map where
  "rev_map env_v = (\<lambda> a. { x | x. env_v x = Some a })"
  
definition unique_rev_map where
  "unique_rev_map f f' = (\<forall> a. f a \<subseteq> {f' a})"  
  
lemma unique_rev_map_ex: "\<lbrakk> unique_env env_v \<rbrakk> \<Longrightarrow> (\<exists> f. unique_rev_map (rev_map env_v) f)"
  apply (simp add: unique_rev_map_def)
  apply (rule_tac Hilbert_Choice.choice)
  apply (auto)
  apply (simp add: unique_env_def)
  apply (case_tac "\<exists> x. env_v x = Some a")
   apply (auto)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (rule_tac x="x" in exI)
   apply (simp add: rev_map_def)
   apply (auto)
   apply (erule_tac x="xa" in allE)
   apply (auto)
  apply (simp add: rev_map_def)
  done
    
lemma unique_spec_env: "\<lbrakk> same_dom_env env_v env; unique_env env_v \<rbrakk> \<Longrightarrow> (\<exists> t_sub. spec_env env_v env t_sub)"
  apply (cut_tac env_v="env_v" in unique_rev_map_ex)
   apply (auto)
  apply (rule_tac x="\<lambda> x. env (f x)" in exI)
  apply (simp add: spec_env_def)
  apply (auto)
  apply (simp add: same_dom_env_def)
  apply (erule_tac x="x" in allE)
  apply (case_tac "env_v x")
   apply (auto)
  apply (simp add: unique_rev_map_def)
  apply (simp add: rev_map_def)
  apply (erule_tac x="a" in allE)
  apply (auto)
  done
    
lemma restr_spec_env: "\<lbrakk> spec_env env_v env t_sub; sub_range env_v ds \<rbrakk> \<Longrightarrow> \<exists> t_subx. (spec_env env_v env t_subx \<and> tsub_dom t_subx ds)"    
  apply (rule_tac x="\<lambda> x. if x \<in> ds then t_sub x else None" in exI)
  apply (auto)
   apply (simp add: spec_env_def)
   apply (auto)
   apply (erule_tac x="x" in allE)
   apply (case_tac "env_v x")
    apply (auto)
   apply (simp add: sub_range_def)
   apply (erule_tac x="x" in allE)
   apply (auto)
  apply (simp add: tsub_dom_def)
  done

definition set_restr_env where
  "set_restr_env env ds = (\<lambda> x. if x \<in> ds then env x else None)"
    
fun all_vars :: "owner_env \<Rightarrow> p_exp \<Rightarrow> res_id set" where
  "all_vars delta (ConstExp c) = {}"
| "all_vars delta (OpExp xop) = {}"
| "all_vars delta (VarExp v) = (case v of
  VarType x \<Rightarrow> {Var x}
  | LocType x \<Rightarrow> {Loc x, Loc (delta x)}
)"
| "all_vars delta (PairExp e1 e2) = all_vars delta e1 \<union> all_vars delta e2"
| "all_vars delta (IfExp e1 e2 e3) = all_vars delta e1 \<union> all_vars delta e2 \<union> all_vars delta e3"
| "all_vars delta (LamExp x e) = all_vars delta e - {Var x}"
| "all_vars delta (AppExp e1 e2) = all_vars delta e1 \<union> all_vars delta e2"  
  
lemma add_set_restr_env: "add_env (set_restr_env env ds) x tau = set_restr_env (add_env env x tau) (ds \<union> {x})"  
  apply (case_tac "\<forall> x'. add_env (set_restr_env env ds) x tau x' = set_restr_env (add_env env x tau) (ds \<union> {x}) x'")
   apply (auto)
  apply (simp add: add_env_def)
  apply (simp add: set_restr_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  apply (simp add: set_restr_env_def)
  apply (case_tac "x' \<in> ds")
   apply (auto)
  done
    
lemma well_typed_set_restr: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; all_vars delta e \<subseteq> ds \<rbrakk> \<Longrightarrow>
  well_typed (set_restr_env env ds) delta r_s1 e tau r_s2 rx"  
  apply (induct e arbitrary: env r_s1 tau r_s2 rx ds)
        apply (auto)
    (* var case *)
       apply (simp add: set_restr_env_def)
       apply (case_tac x)
        apply (auto)
      apply (simp add: set_restr_env_def)
      apply (case_tac x)
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
   apply (rule_tac x="rxa" in exI)
   apply (auto)
   apply (rule_tac x="r_end" in exI)
   apply (rule_tac x="r_s'" in exI)
   apply (simp add: add_set_restr_env)
   apply (case_tac "\<not> (all_vars delta e \<subseteq> ds \<union> {Var x1a})")
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
    
lemma add_dom_cover: "\<lbrakk> dom_cover (add_env env x tau) ds \<rbrakk> \<Longrightarrow> dom_cover env (ds - {x})"    
  apply (simp add: dom_cover_def)
  apply (auto)
  apply (simp add: add_env_def)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  done
    
lemma well_typed_dom_cover: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx \<rbrakk> \<Longrightarrow> dom_cover env (all_vars delta e)"    
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
    (* const + op + var cases *)
        apply (simp add: dom_cover_def)
       apply (simp add: dom_cover_def)
      apply (simp add: dom_cover_def)
      apply (auto)
      apply (case_tac x)
       apply (auto)
    (* pair case *)
     apply (simp add: dom_cover_def)
    (* if case *)
    apply (simp add: dom_cover_def)
    (* lam case *)
   apply (rule_tac tau="t1" in add_dom_cover)
   apply (auto)
    (* app case *)
  apply (simp add: dom_cover_def)
  done
    
lemma cover_same_dom_env: "\<lbrakk> dom_ex_cover env_v ds; dom_cover (set_restr_env env ds) ds \<rbrakk> \<Longrightarrow> same_dom_env env_v (set_restr_env env ds)"    
  apply (simp add: same_dom_env_def)
  apply (auto)
  apply (simp add: dom_ex_cover_def)
  apply (simp add: set_restr_env_def)
  apply (simp add: set_restr_env_def)
  apply (case_tac "x \<in> ds")
   apply (auto)
   apply (simp add: dom_cover_def)
   apply (erule_tac x="x" in allE)
   apply (auto)
  apply (simp add: dom_ex_cover_def)
  done
    (*
lemma append_no_mv_crn: "\<lbrakk> no_mv_crn cl1; no_mv_crn cl2 \<rbrakk> \<Longrightarrow> no_mv_crn (cl1 @ cl2)"    
  apply (induct cl1)
   apply (auto)
  apply (case_tac a)
       apply (auto)
  done
  
lemma disj_no_mv_crn: "no_mv_crn (disj_crn r_s r_x d)"    
  apply (induct d)
   apply (auto)
  done
    
lemma semi_disj_no_mv_crn: "no_mv_crn (semi_disj_crn r_s r_x d)"    
  apply (induct d)
   apply (auto)
  done
    
lemma aff_no_mv_crn: "no_mv_crn (aff_crn r_s r d)"    
  apply (induct d)
   apply (auto)
  done
  
lemma infer_no_mem_val_crn: "\<lbrakk> no_mem_val e; infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds' \<rbrakk> \<Longrightarrow> no_mv_crn c_list"    
  apply (induct e arbitrary: env_v ds tau_v r_sv r_xv r_mv c_list ds')
        apply (auto)
    (* const case *)
      apply (case_tac x)
                  apply (auto)
    (* pair case *)
     apply (rule_tac append_no_mv_crn)
      apply (rule_tac disj_no_mv_crn)
     apply (rule_tac append_no_mv_crn)
      apply (rule_tac semi_disj_no_mv_crn)
     apply (rule_tac append_no_mv_crn)
      apply (rule_tac semi_disj_no_mv_crn)
     apply (rule_tac append_no_mv_crn)
      apply (auto)
    (* if case *)
    apply (rule_tac append_no_mv_crn)
     apply (rule_tac semi_disj_no_mv_crn)
    apply (rule_tac append_no_mv_crn)
     apply (simp)
    apply (rule_tac append_no_mv_crn)
     apply (auto)
    (* lam case *)
   apply (rule_tac append_no_mv_crn)
    apply (rule_tac aff_no_mv_crn)
   apply (simp)
    (* app case *)
   apply (rule_tac append_no_mv_crn)
   apply (rule_tac disj_no_mv_crn)
  apply (rule_tac append_no_mv_crn)
   apply (rule_tac semi_disj_no_mv_crn)
  apply (rule_tac append_no_mv_crn)
   apply (rule_tac semi_disj_no_mv_crn)
  apply (rule_tac append_no_mv_crn)
   apply (auto)
  done
    *)
lemma no_mem_val_no_loc: "\<lbrakk> no_mem_val e \<rbrakk> \<Longrightarrow> Loc a \<notin> all_vars delta e"    
  apply (induct e)
        apply (auto)
  apply (case_tac x)
   apply (auto)
  done
  
lemma set_restr_no_mv_env: "\<lbrakk> no_mem_val e \<rbrakk> \<Longrightarrow> no_mv_env (set_restr_env env (all_vars delta e))"    
  apply (simp add: no_mv_env_def)
  apply (auto)
  apply (case_tac x)
   apply (auto)
  apply (simp add: set_restr_env_def)
  apply (cut_tac a="x2" in no_mem_val_no_loc)
   apply (auto)
  done
    
    (* requires e to not have memory values, and for env_v / ds to be constructed under certain constraints *)
lemma infer_unsat: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; no_mem_val e;
  dom_ex_cover env_v (all_vars delta e); unique_env env_v; sub_range env_v ds; \<not> solve_crn_list c_list \<rbrakk> \<Longrightarrow>
  \<not> well_typed env delta r_s1 e tau r_s2 rx"    
  apply (auto)
    (* first we want to restrict env to only free variables *)
  apply (cut_tac env="env" and e="e" and ds="all_vars delta e" in well_typed_set_restr)
    apply (auto)
    (* using this we can show that env_v is a specialization of env *)
  apply (cut_tac env_v="env_v" and env="set_restr_env env (all_vars delta e)" in unique_spec_env)
    apply (rule_tac cover_same_dom_env)
     apply (simp)
    apply (rule_tac well_typed_dom_cover)
    apply (auto)
    (* we improve the specialization so that its domain fits in ds *)
  apply (cut_tac env_v="env_v" and env="set_restr_env env (all_vars delta e)" and t_sub="t_sub" and ds="ds" in restr_spec_env)
    apply (auto)
    (* next we manipulate the permission bounds of e to call the inference lemma *)
  apply (cut_tac env="set_restr_env env (all_vars delta e)" and ?r_s1.0="r_s1" and e="e" and tau="tau" and ?r_s2.0="r_s2" and rx="rx" in well_typed_end_perm_lbound)
   apply (auto)
  apply (cut_tac env="set_restr_env env (all_vars delta e)" and r_s="r_s1" and r_ex="r_s1" and r_x="diff_use_env rx r_s1" and e="e"
      and env_v="env_v" and ds="ds" and c_list="c_list" in ivr_partial)
       apply (auto)
   apply (rule_tac well_typed_id_delta)
    apply (auto)
   apply (rule_tac set_restr_no_mv_env)
   apply (auto)
    (* since our solver returns false, the constraints are unsolvable, a contradiction *)
  apply (cut_tac t_sub="dir_list_add_env t_subx l" and p_sub="p_sub" and c_list="c_list" in solve_crn_list_unsat)
    apply (auto)(*
  apply (rule_tac infer_no_mem_val_crn)
   apply (auto)*)
  done
    
lemma infer_sat: "\<lbrakk> infer_type env_v ds e tau_v r_sv r_xv r_mv c_list ds'; no_mem_val e; solve_crn_list c_list \<rbrakk> \<Longrightarrow>
  (\<exists> env delta r_s1 tau r_s2 rx. well_typed env delta r_s1 e tau r_s2 rx)"
  apply (cut_tac c_list="c_list" in solve_crn_list_sat)
    apply (auto)(*
   apply (rule_tac infer_no_mem_val_crn)
    apply (auto)*)
  apply (cut_tac tau_n="IntTy" and delta="id" in infer_valid_left)  
     apply (auto)
  apply (rule_tac x="dir_subst_tenv (fill_tsub t_sub IntTy) env_v" in exI)
  apply (rule_tac x="id" in exI)
  apply (auto)
  done
    
end