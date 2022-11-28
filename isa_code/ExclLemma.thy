theory ExclLemma
  imports RedSafeCV ProcCVars ProcDef
begin
  
definition can_access where
  "can_access e x = (x \<in> ref_vars e)"

lemma wts_excl_dom_use_env: "\<lbrakk> well_typed_system env delta p_map s p_set; u \<noteq> v; p_set u = Some e; p_set v = Some e';
  p_map u = Some r_sa; p_map v = Some r_sb; well_typed env delta r_sa e UnitTy r_se r_xe; well_typed env delta r_sb e' UnitTy r_se' r_xe' \<rbrakk> \<Longrightarrow>
  strong_disj_use_env (np_dom_use_env env delta e) (np_dom_use_env env delta e')"    
  apply (simp add: strong_disj_use_env_def)
  apply (auto)
  apply (simp add: np_dom_use_env_def)
  apply (simp add: dom_use_env_def)
  apply (case_tac "x \<in> non_prim_vars env delta e'")
   apply (auto)
  apply (case_tac "r_sa x = NoPerm")
   apply (cut_tac x="x" and env="env" and e="e" and ?r_s1.0="r_sa" in well_typed_no_npv_use)
     apply (auto)
  apply (case_tac "r_sb x = NoPerm")
   apply (cut_tac x="x" and env="env" and e="e'" and ?r_s1.0="r_sb" in well_typed_no_npv_use)
     apply (auto)
  apply (simp add: well_typed_system_def)
  apply (simp add: well_typed_proc_set_def)
  apply (simp add: disj_nres_map_def)
  apply (auto)
  apply (erule_tac x="u" in allE)
  apply (erule_tac x="v" in allE)
  apply (erule_tac x="v" in allE)
  apply (auto)
  apply (simp add: nres_lookup_def)
  apply (simp add: strong_disj_use_env_def)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done

lemma ref_res_vars: "\<lbrakk> x \<in> ref_vars e \<rbrakk> \<Longrightarrow> Loc (delta x) \<in> res_vars delta e"
  apply (induct e)
        apply (auto)
  apply (case_tac xa)
   apply (auto)
  done
    
lemma well_typed_no_dom_use: "\<lbrakk> well_typed_state s env delta; p_set u = Some e; p_map u = Some r_s;
  well_typed env delta r_s e UnitTy r_se r_xe; x \<in> ref_vars e \<rbrakk> \<Longrightarrow> np_dom_use_env env delta e (Loc (delta x)) \<noteq> NoPerm"
    (* we prove that the owner is non-primitive *)
  apply (case_tac "Loc (delta x) \<notin> non_prim_vars env delta e")
   apply (cut_tac x="x" and delta="delta" in ref_res_vars)
    apply (auto)
   apply (case_tac "env (Loc x) = None")
    apply (cut_tac env="env" and x="x" and e="e" in well_typed_rv_env_use)
      apply (auto)
   apply (cut_tac env="env" and delta="delta" in wts_well_formed_delta)
    apply (auto)
   apply (case_tac "env (Loc (delta x)) = None")
    apply (simp add: well_formed_delta_def)
    apply (erule_tac x="x" in allE)
    apply (auto)
   apply (cut_tac s="s" and env="env" and delta="delta" in wts_mem_val_env)
    apply (simp)
   apply (simp add: mem_val_env_def)
   apply (erule_tac x="Loc (delta x)" in allE)
   apply (auto)
   apply (simp add: non_prim_vars_def)
   apply (simp add: non_prim_entry_def)
    apply (case_tac ya)
         apply (auto)
    (* as a result, it is in the dominator *)
  apply (simp add: np_dom_use_env_def)
  apply (simp add: dom_use_env_def)
  done
    
lemma excl_safe_lemma: "\<lbrakk> well_typed_system env delta p_map s p_set; p_set u = Some e; can_access e x;
  p_set v = Some e'; u \<noteq> v \<rbrakk> \<Longrightarrow> \<not> can_access e' x"
    (* prelim: p_map u + v has an entry *)
  apply (case_tac "p_map u = None \<or> p_map v = None")
   apply (simp add: well_typed_system_def)
   apply (simp add: well_typed_proc_set_def)
   apply (auto)
    apply (erule_tac x="u" in allE)
    apply (auto)
   apply (erule_tac x="v" in allE)
   apply (auto)
    (* prelim: e must be well-typed *)
  apply (case_tac "\<not> (\<exists> r_s rx. well_typed env delta y e UnitTy r_s rx)")
   apply (simp add: well_typed_system_def)
   apply (simp add: well_typed_proc_set_def)
   apply (auto)
   apply (erule_tac x="u" in allE)
   apply (auto)
    (* prelim: e' is also well-typed *)
  apply (case_tac "\<not> (\<exists> r_s rx. well_typed env  delta ya e' UnitTy r_s rx)")
   apply (simp add: well_typed_system_def)
   apply (simp add: well_typed_proc_set_def)
   apply (auto)
   apply (erule_tac x="v" in allE)
   apply (auto)
    (* from here, we know that x is in the completion of y + ya *)
  apply (cut_tac env="env" and delta="delta" and e="e" and x="x" and r_s="y" and s="s" in well_typed_no_dom_use)
        apply (auto)
    apply (simp add: well_typed_system_def)
   apply (simp add: can_access_def)
  apply (cut_tac env="env" and delta="delta" and e="e'" and x="x" and r_s="ya" and s="s" in well_typed_no_dom_use)
        apply (auto)
    apply (simp add: well_typed_system_def)
   apply (simp add: can_access_def)
    (* this is a contradiction by dominator exlcusion *)
  apply (cut_tac env="env" and delta="delta" and e="e" and e'="e'" and u="u" and v="v" and p_map="p_map" and s="s" and
      p_set="p_set" in wts_excl_dom_use_env)
          apply (auto)
  apply (simp add: strong_disj_use_env_def)
  apply (auto)
  done
    
end