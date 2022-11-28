theory RedSafeHoleLemma
  imports AltFlatLemma ReduceAction
begin
  
datatype p_hole =
  ExpHole
  | AppHole1 p_hole p_exp
  | AppHole2 p_exp p_hole
  | IfHole p_hole p_exp p_exp
  | PairHole1 p_hole p_exp
  | PairHole2 p_exp p_hole

fun wf_hole where
  "wf_hole ExpHole = True"
| "wf_hole (AppHole1 h e) = wf_hole h"
| "wf_hole (AppHole2 v h) = (is_value v \<and> wf_hole h)"
| "wf_hole (IfHole h e1 e2) = wf_hole h"  
| "wf_hole (PairHole1 h e2) = wf_hole h"  
| "wf_hole (PairHole2 v h) = (is_value v \<and> wf_hole h)"
  
fun app_hole where
  "app_hole ExpHole e = e"
| "app_hole (AppHole1 h e2) e = AppExp (app_hole h e) e2"
| "app_hole (AppHole2 v h) e = AppExp v (app_hole h e)"      
| "app_hole (IfHole h e2 e3) e = IfExp (app_hole h e) e2 e3"
| "app_hole (PairHole1 h e2) e = PairExp (app_hole h e) e2" 
| "app_hole (PairHole2 e1 h) e = PairExp e1 (app_hole h e)"
  
  
lemma trans_sub_use_env: "\<lbrakk> sub_use_env s r_s; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> sub_use_env s r_x"  
  apply (simp add: sub_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
lemma gsre_coerce: "\<lbrakk> \<And>env r_s1 e1 tau r_s2 rx e2.
           \<lbrakk>well_typed env delta r_s1 (app_hole h e1) tau r_s2 rx; well_typed_state s1 env delta; r_exp are (s1, e1) ax (s2, e2); leq_use_env r_s1 r_f\<rbrakk>
           \<Longrightarrow> \<exists>g_ax. well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) (app_hole h e2) tau (end_red_use_env r_s2 g_ax) (end_red_use_env rx g_ax) \<and>
                      well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
                      sub_use_env s2 (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax;
    well_typed env delta r_s1 (app_hole h e1) tau r_s2 rx; well_typed_state s1 env delta; sub_use_env s1 r_f;
    r_exp are (s1, e1) ax (s2, e2); valid_reduct r_exp; wf_hole h; leq_use_env r_s1 r_f
   \<rbrakk> \<Longrightarrow> \<exists>g_ax. well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) (app_hole h e2) tau (end_red_use_env r_s2 g_ax) (end_red_use_env rx g_ax) \<and>
                      well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
                      sub_use_env s2 (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax"
  apply (auto)
  done
  
lemma self_disj_weak_use_env: "\<lbrakk> disj_use_env r_x r_s; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> weak_use_env r_x"    
  apply (simp add: leq_use_env_def)
  apply (simp add: weak_use_env_def)
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done
    
lemma add_diff_use_env: "diff_use_env (add_use_env r_s x r) (add_use_env r_x x OwnPerm) = rem_use_env (diff_use_env r_s r_x) x"    
  apply (case_tac "\<forall> x'. diff_use_env (add_use_env r_s x r) (add_use_env r_x x OwnPerm) x' = rem_use_env (diff_use_env r_s r_x) x x'")  
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: add_use_env_def)
  apply (simp add: rem_use_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done

lemma add_lift_use_env: "lift_use_env (add_use_env r_s x OwnPerm) r = add_use_env (lift_use_env r_s r) x OwnPerm"    
  apply (case_tac "\<forall> x'. lift_use_env (add_use_env r_s x OwnPerm) r x' = add_use_env (lift_use_env r_s r) x OwnPerm x'")
   apply (auto)
  apply (simp add: add_use_env_def)
  apply (case_tac r)
    apply (auto)
  done
 
lemma infl_strong_disj_use_env: "\<lbrakk> leq_use_env r_x (infl_use_env r_c r_s) \<rbrakk> \<Longrightarrow> strong_disj_use_env r_s r_x"    
  apply (simp add: leq_use_env_def)
  apply (simp add: infl_use_env_def)
  apply (simp add: strong_disj_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_c x = OwnPerm \<and> r_s x = NoPerm")
   apply (auto)
   apply (case_tac "r_x x")
     apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done    
    
lemma gsre_wt_red_delta: "\<lbrakk> well_typed env delta (comp_use_env rx (infl_use_env r_s1 r_s2)) e tau (comp_use_env rx (infl_use_env r_s1 r_s2)) (comp_use_env rx (infl_use_env r_s1 r_s2));
  well_formed_delta env delta; leq_use_env r_s1 r_f; safe_act s (infl_use_env r_f (comp_use_env r_s3 (infl_use_env r_s1 r_s2))) g_ax;
  leq_use_env r_s3 r_s2; leq_use_env r_s2 r_s1; leq_use_env rx r_s3; is_value e; sub_env s env; mem_val_env env \<rbrakk> \<Longrightarrow>
  well_typed env (red_delta delta g_ax) r_s1 e tau r_s1 (comp_use_env rx (infl_use_env r_s1 r_s2))"       
  apply (cut_tac env="env" and e="e" and r_s="comp_use_env rx (infl_use_env r_s1 r_s2)" and r_c="r_s1" in well_typed_incr_simul_perm)
    apply (auto)
   apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
     apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
      apply (auto)
   apply (rule_tac self_infl_leq_use_env)
  apply (case_tac g_ax)
  apply (auto)
    apply (rule_tac well_typed_add_delta)
     apply (simp)
    apply (simp add: sub_env_def)
    apply (auto)
    apply (rule_tac well_typed_add_delta)
    apply (rule_tac well_typed_add_delta)
     apply (simp)
    apply (simp add: sub_env_def)
    apply (auto)
   apply (simp add: sub_env_def)
   apply (auto)
  apply (rule_tac well_typed_ext_deltax)
     apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac r_c="r_f" in infl_strong_disj_use_env)
  apply (rule_tac r_sb="infl_use_env r_f (comp_use_env r_s3 (infl_use_env r_s1 r_s2))" in trans_leq_use_env)
   apply (rule_tac dist_infl_leq_use_env)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac comp_leq_use_env1)
    apply (simp)
   apply (rule_tac self_comp_leq_use_env2)
  apply (auto)
  done
    
lemma gsre_wt_end_red_perms_x: "\<lbrakk> well_typed env delta r_s1 e tau r_s1 (comp_use_env rx (infl_use_env r_s1 r_s2)); well_formed_delta env delta; leq_use_env r_s1 r_f;
  safe_act s (infl_use_env r_f (comp_use_env r_s3 (infl_use_env r_s1 r_s2))) g_ax; leq_use_env r_s3 r_s2; leq_use_env r_s2 r_s1; leq_use_env rx r_s3; is_value e \<rbrakk> \<Longrightarrow>
  well_typed env delta (end_red_use_env r_s1 g_ax) e tau (end_red_use_env r_s1 g_ax) (end_red_use_env (comp_use_env rx (infl_use_env r_s1 r_s2)) g_ax)"    
  apply (case_tac g_ax)
      apply (auto)
  apply (rule_tac well_typed_diff_perms)
   apply (auto)
  apply (simp add: own_env_vars_def)
  apply (cut_tac x="x" and r_x="x52" and r_s="infl_use_env r_f (comp_use_env r_s3 (infl_use_env r_s1 r_s2))" in leq_use_own)
    apply (auto)
  apply (case_tac "\<not> (r_f x = OwnPerm \<and> (comp_use_env r_s3 (infl_use_env r_s1 r_s2)) x = NoPerm)")
   apply (simp add: infl_use_env_def)
   apply (auto)
  apply (case_tac "r_s1 x = NoPerm")
   apply (cut_tac x="x" and env="env" and e="e" and ?r_s1.0="r_s1" in well_typed_no_npv_use)
     apply (auto)
  apply (cut_tac e="e" and env="env" and ?r_s1.0="r_s1" and rx="comp_use_env rx (infl_use_env r_s1 r_s2)" in wt_sexp_req_use)
      apply (auto)
   apply (rule_tac value_is_sexp)
   apply (simp)
  apply (cut_tac r_x="comp_use_env rx (infl_use_env r_s1 r_s2)" and r_s="comp_use_env r_s3 (infl_use_env r_s1 r_s2)" and x="x" in leq_use_none)
    apply (auto)
  apply (rule_tac dist_comp_leq_use_env)
   apply (rule_tac comp_leq_use_env1)
   apply (simp)
  apply (rule_tac self_comp_leq_use_env2)
  done 
  
lemma add_well_formed_delta: "\<lbrakk> well_formed_delta env delta; env (Loc x) = None \<rbrakk> \<Longrightarrow> well_formed_delta env (add_delta delta x x)"    
  apply (simp add: well_formed_delta_def)
  apply (auto)
  apply (case_tac "env (Loc xa)")
   apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  apply (simp add: add_delta_def)
  apply (auto)
  done
    
lemma ext_well_formed_delta: "\<lbrakk> well_formed_delta env delta; env (Loc (delta x)) \<noteq> None; mem_val_env env \<rbrakk> \<Longrightarrow> well_formed_delta env (ext_delta delta (delta x) r_s)"    
  apply (simp add: well_formed_delta_def)
  apply (auto)
  apply (case_tac "env (Loc xa)")
   apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  apply (simp add: ext_delta_def)
  apply (auto)
  apply (simp add: mem_val_env_def)
  apply (erule_tac x="Loc (delta x)" in allE)
  apply (auto)
  apply (case_tac y)
        apply (auto)
  done
    
lemma gsre_wt_end_red_comp: "\<lbrakk> well_typed env delta (comp_use_env rx (infl_use_env r_s1 r_s2)) e tau (comp_use_env rx (infl_use_env r_s1 r_s2)) (comp_use_env rx (infl_use_env r_s1 r_s2));
  well_typed_state s env delta; leq_use_env r_s1 r_f; safe_act s (infl_use_env r_f (comp_use_env r_s3 (infl_use_env r_s1 r_s2))) g_ax;
  leq_use_env r_s3 r_s2; leq_use_env r_s2 r_s1; leq_use_env rx r_s3; is_value e \<rbrakk> \<Longrightarrow>
  well_typed env (red_delta delta g_ax) (end_red_use_env r_s1 g_ax) e tau (end_red_use_env r_s1 g_ax) (end_red_use_env (comp_use_env rx (infl_use_env r_s1 r_s2)) g_ax)"
  apply (cut_tac env="env" in wts_mem_val_env)
   apply (auto)
  apply (cut_tac delta="delta" in wts_well_formed_delta)
   apply (auto)
  apply (case_tac "\<not> sub_env s env")
   apply (simp add: well_typed_state_def)
  apply (auto)
  apply (rule_tac gsre_wt_end_red_perms_x)
         apply (auto)
   apply (rule_tac gsre_wt_red_delta)
            apply (auto)
  apply (case_tac g_ax)
      apply (auto)
    apply (rule_tac add_well_formed_delta)
     apply (auto)
    apply (simp add: sub_env_def)
    apply (auto)
   apply (rule_tac add_well_formed_delta)
    apply (rule_tac add_well_formed_delta)
     apply (auto)
    apply (simp add: sub_env_def)
    apply (auto)
   apply (simp add: sub_env_def)
   apply (auto)
  apply (rule_tac ext_well_formed_delta)
    apply (auto)
  apply (simp add: well_typed_state_def)
  apply (auto)
  apply (simp add: proper_delta_def)
  apply (erule_tac x="x51" in allE)
  apply (auto)
  apply (case_tac "env (Loc (delta x51)) = None")
   apply (erule_tac x="delta x51" in allE)
  apply (auto)
  done
    
lemma well_typed_red_deltax: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; safe_act s (infl_use_env r_f r_c) g_ax;
  strong_disj_use_env r_f r_s1; sub_env s env; mem_val_env env \<rbrakk> \<Longrightarrow>
  well_typed env (red_delta delta g_ax) r_s1 e tau r_s2 rx"        
  apply (case_tac g_ax)
      apply (auto)
    apply (rule_tac well_typed_add_delta)
     apply (auto)
    apply (simp add: sub_env_def)
    apply (auto)
   apply (rule_tac well_typed_add_delta)
    apply (rule_tac well_typed_add_delta)
     apply (auto)
    apply (simp add: sub_env_def)
    apply (auto)
   apply (simp add: sub_env_def)
   apply (auto)
  apply (rule_tac well_typed_ext_delta)
    apply (auto)
  apply (rule_tac r_s="r_f" in strong_disj_leq_use_env2)
   apply (rule_tac comm_strong_disj_use_env)
   apply (simp)
  apply (rule_tac r_sb="infl_use_env r_f r_c" in trans_leq_use_env)
   apply (rule_tac self_infl_leq_use_env)
  apply (simp)
  done

lemma well_typed_red_delta: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; safe_act s (infl_use_env r_f r_s1) g_ax;
  leq_use_env r_s1 r_f; sub_env s env; mem_val_env env \<rbrakk> \<Longrightarrow>
  well_typed env (red_delta delta g_ax) r_s1 e tau r_s2 rx"    
  apply (case_tac g_ax)
      apply (auto)
    apply (rule_tac well_typed_add_delta)
     apply (auto)
    apply (simp add: sub_env_def)
    apply (auto)
   apply (rule_tac well_typed_add_delta)
    apply (rule_tac well_typed_add_delta)
     apply (auto)
    apply (simp add: sub_env_def)
    apply (auto)
   apply (simp add: sub_env_def)
   apply (auto)
    apply (rule_tac well_typed_ext_delta)
    apply (auto)
  apply (rule_tac infl_strong_disj_use_env)
  apply (auto)
  done
    
lemma well_typed_end_red_perms: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; safe_act s (infl_use_env r_f r_s1) g_ax; leq_use_env r_s1 r_f \<rbrakk> \<Longrightarrow>
  well_typed env delta (end_red_use_env r_s1 g_ax) e tau (end_red_use_env r_s2 g_ax) (end_red_use_env rx g_ax)"
  apply (case_tac g_ax)
      apply (auto)
  apply (rule_tac well_typed_diff_perms)
   apply (auto)
  apply (simp add: own_env_vars_def)
  apply (cut_tac x="x" and r_x="x52" and r_s="infl_use_env r_f r_s1" in leq_use_own)
    apply (auto)
  apply (case_tac "\<not> (r_f x = OwnPerm \<and> r_s1 x = NoPerm)")
   apply (simp add: infl_use_env_def)
  apply (auto)
  apply (cut_tac x="x" and env="env" and ?r_s1.0="r_s1" and e="e" in well_typed_no_npv_use)
    apply (auto)
  done
    
lemma lift_end_red_use_env: "lift_use_env (end_red_use_env r_s g_ax) r = end_red_use_env (lift_use_env r_s r) g_ax"    
  apply (case_tac g_ax)
      apply (auto)
  apply (simp add: lift_diff_use_env)
  done
  
lemma comp_end_red_use_env: "comp_use_env (end_red_use_env r_x g_ax) (end_red_use_env r_s g_ax) = 
  end_red_use_env (comp_use_env r_x r_s) g_ax"    
  apply (case_tac g_ax)
      apply (auto)
  apply (simp add: dist_diff_comp_use_env)
  done
  
lemma diff_end_red_use_env: "diff_use_env (end_red_use_env r_s g_ax) (end_red_use_env r_x g_ax) =
  end_red_use_env (diff_use_env r_s r_x) g_ax"    
  apply (case_tac g_ax)
      apply (auto)
  apply (cut_tac r_s="r_s" and r_x="r_x" and r_ex="x52" in dist_sq_diff_use_env)
  apply (auto)
  done
    
lemma self_end_red_leq_use_env: "leq_use_env (end_red_use_env r_s g_ax) r_s"    
  apply (case_tac g_ax)
      apply (simp_all add: id_leq_use_env)
  apply (rule_tac self_diff_leq_use_env)
  done
    
lemma end_red_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (end_red_use_env r_x g_ax) r_s"
  apply (case_tac g_ax)
      apply (auto)
  apply (rule_tac diff_leq_use_env)
  apply (simp)
  done
  
lemma dist_end_red_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (end_red_use_env r_x g_ax) (end_red_use_env r_s g_ax)"    
  apply (case_tac g_ax)
      apply (auto)
  apply (rule_tac dist_diff_leq_use_env)
  apply (simp)
  done
    
lemma exp_red_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (end_red_use_env r_x g_ax) (exp_red_use_env r_s g_ax)"    
  apply (case_tac g_ax)
      apply (auto)
    apply (rule_tac rhs_add_leq_use_env)
     apply (auto)
   apply (rule_tac rhs_add_leq_use_env)
    apply (rule_tac rhs_add_leq_use_env)
     apply (auto)
  apply (rule_tac dist_diff_leq_use_env)
  apply (simp)
  done
  
lemma dist_exp_red_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (exp_red_use_env r_x g_ax) (exp_red_use_env r_s g_ax)"    
  apply (case_tac g_ax)
      apply (auto)
    apply (rule_tac dist_add_leq_use_env)
    apply (simp)
   apply (rule_tac dist_add_leq_use_env)
   apply (rule_tac dist_add_leq_use_env)
   apply (simp)
  apply (rule_tac dist_diff_leq_use_env)
  apply (simp)
  done    
(*
lemma add_proper_exp: "\<lbrakk> proper_exp rs_map e; leq_use_env (nres_lookup rs_map x) r_s \<rbrakk> \<Longrightarrow> proper_exp (add_env rs_map x r_s) e"    
  apply (simp add: proper_exp_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (erule_tac x="y" in allE)
  apply (auto)
  apply (rule_tac l="l" in add_vars_path_lookup)
   apply (auto)
  done

lemma add_proper_exp_none: "\<lbrakk> proper_exp rs_map e; rs_map x = None \<rbrakk> \<Longrightarrow> proper_exp (add_env rs_map x r_s) e"      
  apply (rule_tac add_proper_exp)
   apply (simp)
  apply (simp add: nres_lookup_def)
  apply (rule_tac leq_empty_use_env)
  done
  
lemma red_proper_exp: "\<lbrakk> safe_act s r_f g_ax; valid_nres_map s rs_map; proper_exp rs_map e \<rbrakk> \<Longrightarrow> proper_exp (red_nres_map rs_map g_ax) e"    
  apply (case_tac g_ax)
      apply (auto)
    apply (rule_tac add_proper_exp_none)
     apply (simp)
    apply (simp add: valid_nres_map_def)
    apply (simp add: full_nres_map_def)
   apply (rule_tac add_proper_exp_none)
    apply (rule_tac add_proper_exp_none)
     apply (simp)
    apply (simp add: valid_nres_map_def)
    apply (simp add: full_nres_map_def)
   apply (simp add: add_env_def)
   apply (simp add: valid_nres_map_def)
   apply (simp add: full_nres_map_def)
  apply (rule_tac add_proper_exp)
   apply (simp)
  apply (rule_tac self_comp_leq_use_env1)
  done*)

lemma gsre_lac_coerce: "\<lbrakk> \<And>env r_s1 e1 tau r_s2 rx e2.
           \<lbrakk>well_typed env delta r_s1 (app_hole h e1) tau r_s2 rx; well_typed_state s1 env delta; r_exp are (s1, e1) ax (s2, e2);
            leq_use_env r_s1 r_f\<rbrakk>
           \<Longrightarrow> \<exists>g_ax. well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) (app_hole h e2) tau (end_red_use_env r_s2 g_ax) (end_red_use_env rx g_ax) \<and>
                      well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
                      sub_use_env s2 (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax;
    well_typed env delta r_s1 (app_hole h e1) tau r_s2 rx; well_typed_state s1 env delta; r_exp are (s1, e1) ax (s2, e2);
            leq_use_env r_s1 r_f \<rbrakk> \<Longrightarrow> \<exists>g_ax. well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) (app_hole h e2) tau (end_red_use_env r_s2 g_ax) (end_red_use_env rx g_ax) \<and>
                      well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
                      sub_use_env s2 (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax"    
  apply (auto)
  done
    
lemma gsre_lhs_app_case: "\<lbrakk>\<And>env r_s1 e1 tau r_s2 rx e2.
           \<lbrakk>well_typed env delta r_s1 (app_hole h e1) tau r_s2 rx;  well_typed_state s1 env delta; r_exp are (s1, e1) ax (s2, e2);
            leq_use_env r_s1 r_f\<rbrakk>
           \<Longrightarrow> \<exists>g_ax. well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) (app_hole h e2) tau (end_red_use_env r_s2 g_ax) (end_red_use_env rx g_ax) \<and>
                      well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
                      sub_use_env s2 (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax;
        well_typed_state s1 env delta; sub_use_env s1 r_f; wf_hole h;
        r_exp are (s1, e1) ax (s2, e2); valid_reduct r_exp; leq_use_env r_s1 r_f; well_typed env delta r_s1 (app_hole h e1) (FunTy t1 tau r a) r_s2a rx1;
        well_typed env delta r_s2a x2 t1 r_s3 rx2; leq_use_env r_s2 (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex));
        (*safe_use_lift rx2 r; safe_type t1 r;*) leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3; disj_use_env rx1 (lift_use_env rx2 r);
        leq_use_env rx r_s2; leq_use_env r_ex r_s1; leq_use_env (app_req rx1 rx2 r tau r_ex) rx\<rbrakk>
       \<Longrightarrow> \<exists>g_ax. (\<exists>t1 r a r_s2a rx1.
                      well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) (app_hole h e2) (FunTy t1 tau r a) r_s2a rx1 \<and>
                      (\<exists>rx2 r_s3.
                          well_typed (red_env env g_ax) (red_delta delta g_ax) r_s2a x2 t1 r_s3 rx2 \<and>
                          (\<exists>r_ex. leq_use_env (end_red_use_env r_s2 g_ax) (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)) \<and>
                                 (*safe_use_lift rx2 r \<and>
                                  safe_type t1 r \<and>*)
                                  leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3 \<and>
                                  disj_use_env rx1 (lift_use_env rx2 r) \<and>
                                  leq_use_env (end_red_use_env rx g_ax) (end_red_use_env r_s2 g_ax) \<and>
                                  leq_use_env r_ex (exp_red_use_env r_s1 g_ax) \<and> leq_use_env (app_req rx1 rx2 r tau r_ex) (end_red_use_env rx g_ax)))) \<and>
                  well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
                  sub_use_env s2 (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax"    
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and ?e1.0="e1" and ?e2.0="e2" and tau="FunTy t1 tau r a" and ?r_s2.0="r_s2a" and
      r_f="r_f" and ?s2.0="s2" and ax="ax" and r_exp="r_exp" in gsre_lac_coerce)
       apply (auto)
  apply (rule_tac x="g_ax" in exI)
  apply (auto)
    apply (rule_tac x="t1" in exI)
    apply (rule_tac x="r" in exI)
    apply (rule_tac x="a" in exI)
    apply (rule_tac x="end_red_use_env r_s2a g_ax" in exI)
    apply (rule_tac x="end_red_use_env rx1 g_ax" in exI)
    apply (auto)
    (* - typing e2 *)
    apply (rule_tac x="end_red_use_env rx2 g_ax" in exI)
    apply (rule_tac x="end_red_use_env r_s3 g_ax" in exI)
    apply (auto)
     apply (rule_tac env'="env" in well_typed_contain_env)
      apply (rule_tac s="s1" in red_contain_env)
       apply (simp)
      apply (simp add: well_typed_state_def)
     apply (rule_tac r_f="r_f" in well_typed_end_red_perms)
      apply (auto)
     apply (rule_tac well_typed_red_delta)
         apply (auto)
       apply (rule_tac r_sb="r_s1" in trans_leq_use_env)
        apply (simp)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (simp add: well_typed_state_def)
     apply (rule_tac wts_mem_val_env)
     apply (auto)
    apply (rule_tac r_sb="r_s1" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
    (* - bounds *)
    apply (simp add: lift_end_red_use_env)
    apply (simp add: comp_end_red_use_env)
    apply (rule_tac x="end_red_use_env r_ex g_ax" in exI)
    apply (auto)
         apply (simp add: comp_end_red_use_env)
         apply (simp add: diff_end_red_use_env)
         apply (rule_tac dist_end_red_leq_use_env)
         apply (simp)
        apply (rule_tac dist_end_red_leq_use_env)
        apply (simp)
       apply (rule_tac r_s="rx1" in disj_leq_use_env1)
        apply (rule_tac r_s="lift_use_env rx2 r" in disj_leq_use_env2)
         apply (simp)
        apply (rule_tac self_end_red_leq_use_env)
       apply (rule_tac self_end_red_leq_use_env)
      apply (rule_tac dist_end_red_leq_use_env)
      apply (simp)
     apply (rule_tac exp_red_leq_use_env)
     apply (simp)
    apply (simp add: app_req_def)
    apply (auto)
     apply (rule_tac leq_empty_use_env)
    apply (simp add: lift_end_red_use_env)
    apply (simp add: comp_end_red_use_env)
    apply (simp add: diff_end_red_use_env)
    apply (rule_tac dist_end_red_leq_use_env)
    apply (simp)
    (* properness *)(*
   apply (cut_tac rs_map="rs_map" and g_ax="g_ax" and e="x2" and s="s1" in red_proper_exp)
      apply (auto)
     apply (simp add: well_typed_state_def)
    apply (simp add: proper_exp_def)
   apply (simp add: proper_exp_def)*)
    (* action safety / correspondence *)
  apply (rule_tac r_x="infl_use_env r_f r_s2a" in leq_safe_act)
   apply (simp)
  apply (rule_tac dist_infl_leq_use_env)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
   apply (rule_tac diff_leq_use_env)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
  done    
  
lemma gsre_rhs_app_case: "\<lbrakk>\<And>env r_s1 e1 tau r_s2 rx e2.
           \<lbrakk>well_typed env delta r_s1 (app_hole h e1) tau r_s2 rx; well_typed_state s1 env delta; r_exp are (s1, e1) ax (s2, e2);
            leq_use_env r_s1 r_f\<rbrakk>
           \<Longrightarrow> \<exists>g_ax. well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) (app_hole h e2) tau (end_red_use_env r_s2 g_ax) (end_red_use_env rx g_ax) \<and>
                      well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
                      sub_use_env s2 (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax;
        well_typed_state s1 env delta; sub_use_env s1 r_f; r_exp are (s1, e1) ax (s2, e2);
        valid_reduct r_exp; leq_use_env r_s1 r_f; is_value x1; wf_hole h; well_typed env delta r_s1 x1 (FunTy t1 tau r a) r_s2a rx1;
        well_typed env delta r_s2a (app_hole h e1) t1 r_s3 rx2; leq_use_env r_s2 (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex));
        (*safe_use_lift rx2 r; safe_type t1 r;*) leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3; disj_use_env rx1 (lift_use_env rx2 r);
        leq_use_env rx r_s2; leq_use_env r_ex r_s1; leq_use_env (app_req rx1 rx2 r tau r_ex) rx\<rbrakk>
       \<Longrightarrow> \<exists>g_ax. (\<exists>t1 r a r_s2a rx1.
                      well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) x1 (FunTy t1 tau r a) r_s2a rx1 \<and>
                      (\<exists>rx2 r_s3.
                          well_typed (red_env env g_ax) (red_delta delta g_ax) r_s2a (app_hole h e2) t1 r_s3 rx2 \<and>
                          (\<exists>r_ex. leq_use_env (end_red_use_env r_s2 g_ax) (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)) \<and>
                                  (*safe_use_lift rx2 r \<and>
                                  safe_type t1 r \<and>*)
                                  leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3 \<and>
                                  disj_use_env rx1 (lift_use_env rx2 r) \<and>
                                  leq_use_env (end_red_use_env rx g_ax) (end_red_use_env r_s2 g_ax) \<and>
                                  leq_use_env r_ex (exp_red_use_env r_s1 g_ax) \<and> leq_use_env (app_req rx1 rx2 r tau r_ex) (end_red_use_env rx g_ax)))) \<and>
                  well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
                  sub_use_env s2 (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax"    
  apply (case_tac "\<exists>g_ax. well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) (app_hole h e2) t1
        (end_red_use_env (comp_use_env r_s3 (infl_use_env r_s1 r_s2a)) g_ax) (end_red_use_env rx2 g_ax) \<and>
        well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
        sub_use_env s2 (exp_red_use_env r_f g_ax) \<and>
        safe_act s1 (infl_use_env r_f (comp_use_env r_s3 (infl_use_env r_s1 r_s2a))) g_ax \<and> corr_act ax g_ax")
   apply (erule_tac exE)
   apply (rule_tac x="g_ax" in exI)
   apply (auto)
    apply (rule_tac x="t1" in exI)
    apply (rule_tac x="r" in exI)
    apply (rule_tac x="a" in exI)
    apply (rule_tac x="exp_red_use_env r_s1 g_ax" in exI)
    apply (rule_tac x="end_red_use_env (comp_use_env rx1 (infl_use_env r_s1 r_s2a)) g_ax" in exI)
    apply (auto)
     apply (rule_tac env'="env" in well_typed_contain_env)
      apply (rule_tac red_contain_env)
       apply (simp add: well_typed_state_def)
      apply (simp add: well_typed_state_def)
     apply (rule_tac r_s="end_red_use_env r_s1 g_ax" in well_typed_incr_simul_perm)
      apply (rule_tac exp_red_leq_use_env)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac gsre_wt_end_red_comp)
            apply (auto)
        apply (rule_tac infl_sexp_wp)
          apply (simp_all)
         apply (rule_tac wts_well_formed_delta)
         apply (auto)
        apply (rule_tac value_is_sexp)
        apply (simp)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
      apply (simp)
     apply (rule_tac self_comp_leq_use_env1)
    apply (rule_tac x="end_red_use_env rx2 g_ax" in exI)
    apply (rule_tac x="end_red_use_env (comp_use_env r_s3 (infl_use_env r_s1 r_s2a)) g_ax" in exI)
    apply (auto)
    (* existentials *)
         apply (simp add: lift_end_red_use_env)
         apply (simp add: comp_end_red_use_env)
         apply (rule_tac x="end_red_use_env r_ex g_ax" in exI)
         apply (auto)
      (* - end perm bound *)
               apply (rule_tac r_sb="end_red_use_env (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)) g_ax" in trans_leq_use_env)
                apply (simp add: comp_end_red_use_env)
                apply (simp add: diff_end_red_use_env)
                apply (rule_tac dist_end_red_leq_use_env)
                apply (rule_tac lhs_pull_comp_use_env)
                apply (rule_tac rhs_pull_comp_use_env)
                apply (rule_tac unroll_dcl_use_env)
                apply (rule_tac dist_diff_leq_use_env)
                apply (rule_tac rhs_unroll_dcl_use_env)
                apply (rule_tac disj_diff_leq_use_env)
                 apply (rule_tac comm_disj_use_env)
                 apply (rule_tac infl_disj_use_env)
                 apply (rule_tac diff_leq_use_env)
                 apply (rule_tac well_typed_perm_leq)
             apply (auto)
            apply (rule_tac dist_diff_leq_use_env)
            apply (rule_tac self_comp_leq_use_env1)
           apply (rule_tac dist_end_red_leq_use_env)
           apply (simp)
    (* - lift safety *)(*
              apply (rule_tac r_s="rx2" in safe_lift_leq_use_env)
               apply (rule_tac self_end_red_leq_use_env)
              apply (simp)*)
    (* - containment bound *)
             apply (rule_tac dist_end_red_leq_use_env)
             apply (rule_tac dist_comp_leq_use_env)
              apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac comp_leq_use_env1)
        apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
         apply (simp)
        apply (rule_tac self_comp_leq_use_env1)
       apply (rule_tac self_comp_leq_use_env2)
      apply (rule_tac comp_leq_use_env1)
      apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac self_comp_leq_use_env2)
    (* - disjointness *)
        apply (rule_tac r_s="comp_use_env rx1 (infl_use_env r_s1 r_s2a)" in disj_leq_use_env1)
         apply (rule_tac r_s="lift_use_env rx2 r" in disj_leq_use_env2)
       apply (rule_tac disj_comp_use_env1)
        apply (simp)
       apply (rule_tac comm_disj_use_env)
       apply (rule_tac infl_disj_use_env)
       apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
       apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
        apply (simp)
          apply (rule_tac self_comp_leq_use_env2)
         apply (rule_tac self_end_red_leq_use_env)
        apply (rule_tac self_end_red_leq_use_env)
    (* - in-between bound *)
       apply (rule_tac dist_end_red_leq_use_env)
       apply (simp)
    (* - subtractibility bound *)
      apply (rule_tac exp_red_leq_use_env)
      apply (auto)
    (* - requirements bound *)
     apply (simp add: app_req_def)
     apply (auto)
      apply (rule_tac leq_empty_use_env)
     apply (rule_tac r_sb="end_red_use_env (diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)) g_ax" in trans_leq_use_env)
      apply (rule_tac dist_end_red_leq_use_env)
      apply (simp)
     apply (simp add: lift_end_red_use_env)
     apply (simp add: comp_end_red_use_env)
     apply (simp add: diff_end_red_use_env)
     apply (rule_tac dist_end_red_leq_use_env)
   apply (rule_tac lhs_dist_dcl_use_env)
   apply (rule_tac rhs_dist_dcl_use_env)
   apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac comp_leq_use_env1)
    apply (rule_tac lhs_dist_dcl_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac unroll_dcl_use_env)
     apply (rule_tac dist_diff_leq_use_env)
     apply (rule_tac unroll_dcl_use_env)
     apply (rule_tac dist_diff_leq_use_env)
     apply (rule_tac lhs_unroll_dcl_use_env)
     apply (rule_tac self_diff_leq_use_env)
    apply (rule_tac r_sb="diff_use_env (infl_use_env r_s1 r_s2a) (infl_use_env r_s1 r_s2a)" in trans_leq_use_env)
     apply (rule_tac r_sb="empty_use_env" in trans_leq_use_env)
      apply (rule_tac leq_empty_use_env)
     apply (rule_tac diff_infl_leq_use_env)
    apply (rule_tac dist_diff_leq_use_env_gen)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac comp_leq_use_env1)
    apply (rule_tac comp_leq_use_env1)
    apply (rule_tac self_comp_leq_use_env2)
   apply (rule_tac comp_leq_use_env2)
   apply (rule_tac unroll_dcl_use_env)
   apply (rule_tac dist_diff_leq_use_env)
   apply (rule_tac unroll_dcl_use_env)
   apply (rule_tac dist_diff_leq_use_env)
   apply (rule_tac lhs_unroll_dcl_use_env)
     apply (rule_tac self_diff_leq_use_env)
    (* properness *)(*
    apply (cut_tac rs_map="rs_map" and g_ax="g_ax" and s="s1" and e="x1" in red_proper_exp)
       apply (simp)
      apply (simp add: well_typed_state_def)
     apply (simp add: proper_exp_def)
    apply (simp add: proper_exp_def)*)
    (* safe action *)
   apply (rule_tac r_x="infl_use_env r_f (comp_use_env r_s3 (infl_use_env r_s1 r_s2a))" in leq_safe_act)
    apply (simp)
   apply (rule_tac dist_infl_leq_use_env)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
    apply (rule_tac comp_leq_use_env1)
    apply (rule_tac self_diff_leq_use_env)
   apply (simp)
    (* induction *)
  apply (cut_tac env="env" and ?s1.0="s1" and h="h" and ?e1.0="e1" and r_exp="r_exp" and ax="ax" and ?s2.0="s2" and ?e2.0="e2"
      and tau="t1" and r_f="r_f" and ?r_s1.0="r_s1" and ?r_s2.0="comp_use_env r_s3 (infl_use_env r_s1 r_s2a)" and rx="rx2" in gsre_coerce)
           apply (auto)
   apply (rule_tac ?r_s1.0="comp_use_env r_s2a (infl_use_env r_s1 r_s2a)" in well_typed_incr_start_perm)
    apply (rule_tac well_typed_comp_perms_gen)
     apply (simp)
    apply (rule_tac gen_mini_disj_use_env1)
    apply (rule_tac infl_disj_use_env)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac lhs_infl_leq_use_env)
  apply (rule_tac id_leq_use_env)
  done
    
lemma cancel_refl_leq_use_env: "leq_use_env (diff_use_env (refl_use_env r_s r_x r) (infl_use_env r_s r_x)) rx"  
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: infl_use_env_def)
  apply (simp add: refl_use_env_def)
  done
  
lemma gsre_rhs_pair_case: "\<lbrakk>\<And>env r_s1 e1 tau r_s2 rx e2.
           \<lbrakk>well_typed env delta r_s1 (app_hole h e1) tau r_s2 rx; well_typed_state s1 env delta; r_exp are (s1, e1) ax (s2, e2); leq_use_env r_s1 r_f\<rbrakk>
           \<Longrightarrow> \<exists>g_ax. well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) (app_hole h e2) tau (end_red_use_env r_s2 g_ax) (end_red_use_env rx g_ax) \<and>
                      well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
                      sub_use_env s2 (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax;
        well_typed_state s1 env delta; sub_use_env s1 r_f; r_exp are (s1, e1) ax (s2, e2);
        valid_reduct r_exp; leq_use_env r_s1 r_f; is_value x1;
        wf_hole h; well_typed env delta r_s1 x1 t1 r_s2a rx1; well_typed env delta r_s2a (app_hole h e1) t2 r_s3 rx2; leq_use_env (lift_use_env rx1 r) r_s3;
        leq_use_env (lift_use_env rx2 r) r_s3; (* r \<noteq> NoPerm; safe_use_lift rx1 r; safe_use_lift rx2 r; safe_type t1 r; safe_type t2 r;*)
        disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r); leq_use_env r_s2 (diff_use_env r_s3 r_ex); leq_use_env rx r_s2; leq_use_env r_ex r_s1;
        leq_use_env (pair_req (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex (PairTy t1 t2 r)) rx\<rbrakk>
       \<Longrightarrow> \<exists>g_ax. (\<exists>r_s2a r_s3 rx1.
                      well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) x1 t1 r_s2a rx1 \<and>
                      (\<exists>rx2. well_typed (red_env env g_ax) (red_delta delta g_ax) r_s2a (app_hole h e2) t2 r_s3 rx2 \<and>
                             leq_use_env (lift_use_env rx1 r) r_s3 \<and>
                             leq_use_env (lift_use_env rx2 r) r_s3 \<and>
                              (*safe_use_lift rx1 r \<and>
                             safe_use_lift rx2 r \<and>*)
                             disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r) \<and>
                             (\<exists>r_ex. leq_use_env (end_red_use_env r_s2 g_ax) (diff_use_env r_s3 r_ex) \<and>
                                     leq_use_env (end_red_use_env rx g_ax) (end_red_use_env r_s2 g_ax) \<and>
                                     leq_use_env r_ex (exp_red_use_env r_s1 g_ax) \<and>
                                     leq_use_env (pair_req (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex (PairTy t1 t2 r))
                                      (end_red_use_env rx g_ax)))) \<and>
                  well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
                  sub_use_env s2 (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax"
    (* initial induction *)  
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and h="h" and ?e1.0="e1" and ?r_s2.0="comp_use_env r_s3 (infl_use_env r_s1 r_s2a)" and 
      tau="t2" and rx="rx2" and r_exp="r_exp" and ?s1.0="s1" and ?s2.0="s2" and r_f="r_f" and ax="ax" in gsre_coerce)
           apply (auto)
    apply (rule_tac ?r_s1.0="comp_use_env r_s2a (infl_use_env r_s1 r_s2a)" in well_typed_incr_start_perm)
     apply (rule_tac well_typed_comp_perms)
      apply (simp)
     apply (rule_tac infl_disj_use_env)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (rule_tac self_infl_leq_use_env)
    (* first well-typedness statement *)
  apply (rule_tac x="g_ax" in exI)
  apply (auto)
   apply (rule_tac x="exp_red_use_env r_s1 g_ax" in exI)
   apply (rule_tac x="end_red_use_env (comp_use_env r_s3 (infl_use_env r_s1 r_s2a)) g_ax" in exI)
   apply (rule_tac x="end_red_use_env (comp_use_env rx1 (infl_use_env r_s1 r_s2a)) g_ax" in exI)
   apply (auto)
    apply (rule_tac r_s="end_red_use_env r_s1 g_ax" in well_typed_incr_simul_perm)
     apply (rule_tac exp_red_leq_use_env)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac env'="env" in well_typed_contain_env)
     apply (rule_tac red_contain_env)
      apply (auto)
     apply (simp add: well_typed_state_def)
    apply (rule_tac gsre_wt_end_red_comp)
           apply (auto)
       apply (rule_tac infl_sexp_wp)
         apply (simp_all)
        apply (rule_tac wts_well_formed_delta)
        apply (auto)
       apply (rule_tac value_is_sexp)
       apply (simp)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (rule_tac r_sb="lift_use_env rx1 r" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac self_lift_leq_use_env)
   apply (case_tac "\<not> leq_perm r r")
    apply (case_tac r)
      apply (auto)
    (* second well-typedness *)
   apply (rule_tac x="end_red_use_env rx2 g_ax" in exI)
   apply (auto)
    (* boundaries: rx1 containment *)
        apply (simp add: lift_end_red_use_env)
        apply (rule_tac dist_end_red_leq_use_env)
        apply (simp add: lift_comp_use_env)
        apply (rule_tac dist_comp_leq_use_env)
         apply (rule_tac comp_leq_use_env1)
         apply (simp)
        apply (simp add: infl_lift_use_env)
        apply (rule_tac self_comp_leq_use_env2)
    (* - rx2 containment *)
       apply (simp add: lift_end_red_use_env)
       apply (rule_tac dist_end_red_leq_use_env)
       apply (rule_tac comp_leq_use_env1)
       apply (simp)
    (* - lift safety 1 *)(*
      apply (rule_tac r_s="comp_use_env rx1 (refl_use_env r_s1 r_s2a r)" in safe_lift_leq_use_env)
       apply (rule_tac self_end_red_leq_use_env)
      apply (rule_tac safe_lift_comp_use_env)
       apply (simp)
      apply (rule_tac safe_lift_refl_use_env)
      apply (simp)
    (* - lift safety 2 *)    
     apply (rule_tac r_s="rx2" in safe_lift_leq_use_env)
      apply (rule_tac self_end_red_leq_use_env)
     apply (simp)*)
    (* - disjointness *)
    apply (simp add: lift_end_red_use_env)
    apply (rule_tac r_s="lift_use_env (comp_use_env rx1 (infl_use_env r_s1 r_s2a)) r" in disj_leq_use_env1)
     apply (rule_tac r_s="lift_use_env rx2 r" in disj_leq_use_env2)
      apply (simp add: lift_comp_use_env)
      apply (rule_tac disj_comp_use_env1)
       apply (simp)
      apply (simp add: infl_lift_use_env)
      apply (rule_tac comm_disj_use_env)
      apply (rule_tac infl_disj_use_env)
      apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
     apply (rule_tac self_end_red_leq_use_env)
    apply (rule_tac self_end_red_leq_use_env)
    (* further bounds *)
   apply (simp add: lift_end_red_use_env)
   apply (simp add: comp_end_red_use_env)
   apply (rule_tac x="comp_use_env (end_red_use_env r_ex g_ax) (end_red_use_env (infl_use_env r_s1 r_s2a) g_ax)" in exI)
   apply (auto)
      apply (rule_tac rhs_unroll_dcl_use_env)
      apply (rule_tac disj_diff_leq_use_env)
       apply (rule_tac r_s="infl_use_env r_s1 r_s2a" in disj_leq_use_env1)
        apply (rule_tac comm_disj_use_env)
        apply (rule_tac infl_disj_use_env)
        apply (rule_tac end_red_leq_use_env)
        apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
         apply (rule_tac diff_leq_use_env)
         apply (rule_tac well_typed_perm_leq)
         apply (auto)
       apply (rule_tac self_end_red_leq_use_env)
      apply (simp add: diff_end_red_use_env)
      apply (rule_tac dist_end_red_leq_use_env)
      apply (rule_tac rhs_dist_dcl_use_env)
      apply (rule_tac comp_leq_use_env1)
      apply (simp)
     apply (rule_tac dist_end_red_leq_use_env)
     apply (simp)
    apply (simp add: comp_end_red_use_env)
    apply (rule_tac exp_red_leq_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (simp)
    apply (rule_tac lhs_infl_leq_use_env)
    apply (rule_tac id_leq_use_env)
   apply (case_tac "req_type (PairTy t1 t2 r) = Prim")
    apply (simp add: pair_req_def)
    apply (rule_tac leq_empty_use_env)
   apply (simp add: pair_req_def)
   apply (simp add: comp_end_red_use_env)
   apply (simp add: diff_end_red_use_env)
   apply (rule_tac dist_end_red_leq_use_env)
   apply (rule_tac lhs_dist_dcl_use_env)
   apply (rule_tac dist_comp_leq_use_env)
    apply (simp add: lift_comp_use_env)
    apply (rule_tac lhs_dist_dcl_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac r_sb="diff_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex" in trans_leq_use_env)
      apply (simp)
     apply (rule_tac dist_diff_leq_use_env_gen)
      apply (rule_tac self_comp_leq_use_env1)
     apply (rule_tac self_comp_leq_use_env1)
    apply (simp add: infl_lift_use_env)
    apply (rule_tac r_sb="diff_use_env (infl_use_env r_s1 r_s2a) (infl_use_env r_s1 r_s2a)" in trans_leq_use_env)
     apply (rule_tac diff_infl_leq_use_env)
    apply (rule_tac dist_diff_leq_use_env_gen)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac self_comp_leq_use_env2)
   apply (rule_tac r_sb="diff_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex" in trans_leq_use_env)
    apply (simp)
   apply (rule_tac dist_diff_leq_use_env_gen)
    apply (rule_tac self_comp_leq_use_env2)
    apply (rule_tac self_comp_leq_use_env1)
    (* properness *)(*
   apply (cut_tac rs_map="rs_map" and s="s1" and g_ax="g_ax" and e="x1" in red_proper_exp)
      apply (simp)
     apply (simp add: well_typed_state_def)
    apply (simp add: proper_exp_def)
   apply (simp add: proper_exp_def)*)
    (* action safety *)
  apply (rule_tac r_x="infl_use_env r_f (comp_use_env r_s3 (infl_use_env r_s1 r_s2a))" in leq_safe_act)
   apply (simp)
  apply (rule_tac dist_infl_leq_use_env)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac comp_leq_use_env1)
  apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
   apply (rule_tac self_diff_leq_use_env)
  apply (simp)
  done

lemma well_typed_exp_red_perms: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; safe_act s (infl_use_env r_f r_s1) g_ax;
  leq_use_env r_s1 r_f; sub_env s env; sub_use_env s r_s1 \<rbrakk> \<Longrightarrow>
  well_typed env delta (exp_red_use_env r_s1 g_ax) e tau (exp_red_use_env r_s2 g_ax) (end_red_use_env rx g_ax)"    
  apply (case_tac g_ax)
      apply (auto)
    (* make case *)
    apply (case_tac "env (Loc x21) \<noteq> None")
     apply (simp add: sub_env_def)
     apply (erule_tac x="Loc x21" in allE)
     apply (auto)
    apply (case_tac "r_s1 (Loc x21) \<noteq> NoPerm")
     apply (simp add: sub_use_env_def)
     apply (erule_tac x="Loc x21" in allE)
     apply (auto)
    apply (rule_tac well_typed_add_perms)
       apply (auto)
     apply (simp add: non_prim_vars_def)
     apply (simp add: non_prim_entry_def)
    apply (rule_tac r_s="r_s1" in leq_use_none)
     apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
    apply (rule_tac well_typed_perm_leqx)
    apply (auto)
    (* mk 2 case *)   
   apply (cut_tac r_sc="rx" and r_sb="r_s2" and r_sa="r_s1" in trans_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (rule_tac well_typed_perm_leqx)
    apply (auto)
   apply (rule_tac well_typed_add_perms)
      apply (rule_tac well_typed_add_perms)
         apply (auto)
      apply (simp add: non_prim_vars_def)
      apply (simp add: non_prim_entry_def)
      apply (simp add: sub_env_def)
      apply (erule_tac x="Loc x31" in allE)
      apply (auto)
     apply (rule_tac r_s="r_s1" in leq_use_none)
      apply (simp)
     apply (simp add: sub_use_env_def)
     apply (erule_tac x="Loc x31" in allE)
     apply (auto)
    apply (simp add: non_prim_vars_def)
    apply (simp add: non_prim_entry_def)
    apply (simp add: sub_env_def)
    apply (erule_tac x="Loc x32" in allE)
    apply (auto)
   apply (rule_tac r_s="r_s1" in leq_use_none)
    apply (simp)
   apply (simp add: sub_use_env_def)
   apply (erule_tac x="Loc x32" in allE)
   apply (auto)
    (* write act *)
  apply (rule_tac well_typed_diff_perms)
   apply (auto)
  apply (simp add: own_env_vars_def)
  apply (cut_tac x="x" and r_x="x52" and r_s="infl_use_env r_f r_s1" in leq_use_own)
    apply (auto)
  apply (case_tac "\<not> (r_f x = OwnPerm \<and> r_s1 x = NoPerm)")
   apply (simp add: infl_use_env_def)
  apply (auto)
  apply (cut_tac x="x" and env="env" and ?r_s1.0="r_s1" and e="e" in well_typed_no_npv_use)
    apply (auto)
  done    
    
lemma gen_safe_red_exp: "\<lbrakk> well_typed env delta r_s1 (app_hole h e1) tau r_s2 rx; well_typed_state s1 env delta;
  sub_use_env s1 r_f; wf_hole h; r_exp are (s1, e1) ax (s2, e2); valid_reduct r_exp; leq_use_env r_s1 r_f \<rbrakk> \<Longrightarrow> (\<exists> g_ax.
    well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) (app_hole h e2) tau (end_red_use_env r_s2 g_ax) (end_red_use_env rx g_ax) \<and>
    well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
    sub_use_env s2 (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax)"
  apply (induct h arbitrary: env r_s1 e1 tau r_s2 rx e2)
    (* base case *)
     apply (auto)
     apply (simp add: valid_reduct_def)
    (* lhs induct *)
       apply (rule_tac gsre_lhs_app_case)
                      apply (auto)
    (* rhs induct *)
       apply (rule_tac gsre_rhs_app_case)
                      apply (auto)
    (* if induct *)
    apply (cut_tac env="env" and ?r_s1.0="r_s1" and h="h" and ?e1.0="e1" and r_exp="r_exp" and ?s1.0="s1" and ?s2.0="s2" and r_f="r_f" and
      ax="ax" and ?e2.0="e2" in gsre_coerce)
             apply (auto)
      apply (rule_tac x="g_ax" in exI)
      apply (auto)
     apply (rule_tac x="end_red_use_env rx' g_ax" in exI)
     apply (rule_tac x="end_red_use_env r_s2a g_ax" in exI)
     apply (auto)
     apply (rule_tac x="end_red_use_env rx1 g_ax" in exI)
      apply (auto)
       apply (rule_tac env'="env" in well_typed_contain_env)
        apply (rule_tac red_contain_env)
         apply (auto)
        apply (simp add: well_typed_state_def)
       apply (rule_tac s="s1" and r_f="r_f" in well_typed_end_red_perms)
        apply (auto)
       apply (rule_tac well_typed_red_delta)
           apply (auto)
         apply (rule_tac r_sb="r_s1" in trans_leq_use_env)
          apply (simp)
         apply (rule_tac well_typed_perm_leq)
         apply (auto)
        apply (simp add: well_typed_state_def)
       apply (rule_tac wts_mem_val_env)
       apply (auto)
      apply (rule_tac r_sb="r_s1" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (rule_tac x="end_red_use_env rx2 g_ax" in exI)
     apply (auto)
     apply (rule_tac env'="env" in well_typed_contain_env)
      apply (rule_tac red_contain_env)
       apply (auto)
       apply (simp add: well_typed_state_def)
       apply (rule_tac s="s1" and r_f="r_f" in well_typed_end_red_perms)
         apply (auto)
       apply (rule_tac well_typed_red_delta)
           apply (auto)
         apply (rule_tac r_sb="r_s1" in trans_leq_use_env)
          apply (simp)
         apply (rule_tac well_typed_perm_leq)
         apply (auto)
        apply (simp add: well_typed_state_def)
       apply (rule_tac wts_mem_val_env)
       apply (auto)
      apply (rule_tac r_sb="r_s1" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (simp add: comp_end_red_use_env)
    apply (rule_tac r_x="infl_use_env r_f r_s2a" in leq_safe_act)
     apply (simp)
    apply (rule_tac dist_infl_leq_use_env)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
    (* lhs pair induct *)
    apply (cut_tac env="env" and ?r_s1.0="r_s1" and h="h" and ?e1.0="e1" and r_exp="r_exp" and ?s1.0="s1" and ?s2.0="s2" and r_f="r_f" and
      ax="ax" and ?e2.0="e2" in gsre_coerce)
             apply (auto)
    apply (rule_tac x="g_ax" in exI)
    apply (auto)
    apply (rule_tac x="end_red_use_env r_s2a g_ax" in exI)
    apply (rule_tac x="end_red_use_env r_s3 g_ax" in exI)
    apply (rule_tac x="end_red_use_env rx1 g_ax" in exI)
     apply (auto)
    apply (rule_tac x="end_red_use_env rx2 g_ax" in exI)
     apply (auto)
     apply (rule_tac env'="env" in well_typed_contain_env)
         apply (rule_tac red_contain_env)
          apply (simp)
         apply (simp add: well_typed_state_def)
        apply (rule_tac s="s1" and r_f="r_f" in well_typed_end_red_perms)
          apply (auto)
         apply (rule_tac well_typed_red_delta)
             apply (auto)
           apply (rule_tac r_sb="r_s1" in trans_leq_use_env)
            apply (simp)
           apply (rule_tac well_typed_perm_leq)
           apply (auto)
          apply (simp add: well_typed_state_def)
         apply (rule_tac wts_mem_val_env)
         apply (auto)
        apply (rule_tac r_sb="r_s1" in trans_leq_use_env)
         apply (simp)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
       apply (simp add: lift_end_red_use_env)
       apply (rule_tac dist_end_red_leq_use_env)
       apply (simp)
      apply (simp add: lift_end_red_use_env)
      apply (rule_tac dist_end_red_leq_use_env)
      apply (simp)
(*
        apply (rule_tac r_s="rx1" in safe_lift_leq_use_env)
         apply (rule_tac self_end_red_leq_use_env)
        apply (simp)
       apply (rule_tac r_s="rx2" in safe_lift_leq_use_env)
        apply (rule_tac self_end_red_leq_use_env)
       apply (simp)*)
      apply (simp add: lift_end_red_use_env)
      apply (rule_tac r_s="lift_use_env rx1 r" in disj_leq_use_env1)
       apply (rule_tac r_s="lift_use_env rx2 r" in disj_leq_use_env2)
        apply (simp)
       apply (rule_tac self_end_red_leq_use_env)
      apply (rule_tac self_end_red_leq_use_env)
     apply (simp add: lift_end_red_use_env)
     apply (simp add: comp_end_red_use_env)
     apply (rule_tac x="end_red_use_env r_ex g_ax" in exI)
     apply (auto)
        apply (simp add: diff_end_red_use_env)
        apply (rule_tac dist_end_red_leq_use_env)
        apply (simp)
       apply (rule_tac dist_end_red_leq_use_env)
       apply (simp)
      apply (rule_tac exp_red_leq_use_env)
      apply (simp)
     apply (case_tac "req_type (PairTy t1 t2 r) = Prim")
      apply (simp add: pair_req_def)
      apply (rule_tac leq_empty_use_env)
     apply (simp add: pair_req_def)
     apply (simp add: diff_end_red_use_env)
     apply (rule_tac dist_end_red_leq_use_env)
     apply (simp)
   apply (simp add: well_typed_state_def)
   apply (rule_tac r_x="infl_use_env r_f r_s2a" in leq_safe_act)
    apply (simp)
    apply (rule_tac dist_infl_leq_use_env)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
     apply (rule_tac diff_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    (* pair case 2 *)
  apply (rule_tac gsre_rhs_pair_case)
                  apply (auto)
  done
    
fun full_red_exp where
  "full_red_exp are (s1, e1) ax (s2, e2) = (\<exists> h ex1 ex2. e1 = app_hole h ex1 \<and> e2 = app_hole h ex2 \<and>
    wf_hole h \<and> app_red_exp are (s1, ex1) ax (s2, ex2))"
    
lemma complete_full_red_exp: "\<lbrakk> app_red_exp are (s1, e1) ax (s2, e2) \<rbrakk> \<Longrightarrow> full_red_exp are (s1, e1) ax (s2, e2)"  
  apply (auto)
  apply (rule_tac x="ExpHole" in exI)
  apply (auto)
  done
    
lemma safe_full_red_exp: "\<lbrakk> well_typed env delta r_s1 e1 tau r_s2 rx; well_typed_state s1 env delta;
  sub_use_env s1 r_f; full_red_exp are (s1, e1) ax (s2, e2); valid_reduct app_red_exp; leq_use_env r_s1 r_f \<rbrakk> \<Longrightarrow> (\<exists> g_ax.
    well_typed (red_env env g_ax) (red_delta delta g_ax) (exp_red_use_env r_s1 g_ax) e2 tau (end_red_use_env r_s2 g_ax) (end_red_use_env rx g_ax) \<and>
    well_typed_state s2 (red_env env g_ax) (red_delta delta g_ax) \<and>
    sub_use_env s2 (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax)"
  apply (auto)
  apply (rule_tac are="are" in gen_safe_red_exp)
        apply (auto)
  done
  
end