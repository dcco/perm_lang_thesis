theory AltLBoundLemma
  imports AltSuperNormEnv AltFlatLemma
begin
  
lemma rhs_norm_leq_use_env: "\<lbrakk> leq_use_env r_x r_s; leq_use_env r_x r_ex \<rbrakk> \<Longrightarrow> leq_use_env r_x (norm_use_env r_s r_ex)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: norm_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  done

lemma rhs_norm_leq_use_env2: "\<lbrakk> leq_use_env r_ex r_s; leq_use_env r_x r_ex \<rbrakk> \<Longrightarrow> leq_use_env r_x (norm_use_env r_s r_ex)"     
  apply (rule_tac rhs_norm_leq_use_env)
   apply (rule_tac r_sb="r_ex" in trans_leq_use_env)
    apply (auto)
  done
    
lemma dist_norm_leq_use_env: "\<lbrakk> leq_use_env r_ex r_exa; leq_use_env r_ex r_exb \<rbrakk> \<Longrightarrow> leq_use_env (norm_use_env r_s r_ex) (norm_use_env (norm_use_env r_s r_exa) r_exb)"
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (simp add: norm_use_env_def)
  apply (auto)
    apply (case_tac "r_ex x")
      apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done
  
lemma comm_diff_use_env: "diff_use_env (diff_use_env r_s r_x) r_ex = diff_use_env (diff_use_env r_s r_ex) r_x"    
  apply (case_tac "\<forall> x. diff_use_env (diff_use_env r_s r_x) r_ex x = diff_use_env (diff_use_env r_s r_ex) r_x x")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (case_tac "r_ex x")
    apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done
    
definition eq_wrap where
  "eq_wrap r_s r_x = (r_s = r_x)"

lemma wtepl_diff_remove_lemma_ex: "\<lbrakk> eq_wrap (diff_use_env r_s1 r_ex) (super_norm_use_env r_s1 r_s2a); leq_use_env r_s2a r_s1; r_ex x = OwnPerm \<rbrakk> \<Longrightarrow> r_s2a x = NoPerm"
  apply (case_tac "r_s1 x = NoPerm")
   apply (rule_tac r_s="r_s1" in leq_use_none)
    apply (auto)
  apply (case_tac "diff_use_env r_s1 r_ex x \<noteq> NoPerm")
   apply (simp add: diff_use_env_def)
  apply (case_tac "super_norm_use_env r_s1 r_s2a x = NoPerm")
   apply (simp add: super_norm_use_env_def)
   apply (case_tac "r_s1 x = OwnPerm \<and> r_s2a x = NoPerm")
    apply (auto)
  apply (simp add: eq_wrap_def)
  done

lemma wtepl_diff_remove_lemma: "\<lbrakk> diff_use_env r_s1 r_ex = super_norm_use_env r_s1 r_s2a; leq_use_env r_s2a r_s1; r_ex x = OwnPerm \<rbrakk> \<Longrightarrow> r_s2a x = NoPerm"
  apply (rule_tac r_ex="r_ex" and r_s2a="r_s2a" in wtepl_diff_remove_lemma_ex)
    apply (auto)
  apply (simp add: eq_wrap_def)
  done
    
lemma wtepl_diff_comp_use_env: "diff_use_env r_s r_s = comp_use_env (diff_use_env r_s r_s) (diff_use_env r_s r_s)"
  apply (case_tac "\<forall> x. diff_use_env r_s r_s x = comp_use_env (diff_use_env r_s r_s) (diff_use_env r_s r_s) x")
   apply (auto)
  apply (simp add: diff_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
lemma wtepl_conversion: "\<lbrakk> well_typed env delta r_s2a e tau r_s3 rx; leq_use_env r_s2a r_s1;
  well_typed env delta r_s1 e tau (diff_use_env r_s1 r_s1) (diff_use_env rx r_s1) \<rbrakk> \<Longrightarrow>
  well_typed env delta (super_norm_use_env r_s1 r_s2a) e tau (diff_use_env r_s1 r_s1) (diff_use_env rx r_s1)"
  apply (cut_tac r_s="r_s1" and r_x="r_s2a" in snorm_diff_use_env)
  apply (auto)    
  apply (case_tac "\<not> diff_use_env r_s1 r_s1 = diff_use_env (diff_use_env r_s1 r_s1) r_ex")
   apply (auto)
   apply (cut_tac r_s="r_s1" and r_c="r_s1" and r_x="r_ex" in cancel_diff_use_env)
    apply (simp)
   apply (cut_tac r_s="r_s1" and r_x="r_s1" and r_ex="r_ex" in comm_diff_use_env)
   apply (auto)
  apply (cut_tac r_s="rx" and r_c="r_s1" and r_x="r_ex" in cancel_diff_use_env)
   apply (simp)
  apply (cut_tac r_s="rx" and r_x="r_s1" and r_ex="r_ex" in comm_diff_use_env)
  apply (auto)
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and tau="tau" and e="e" and ?r_s2.0="diff_use_env r_s1 r_s1" and
        rx="diff_use_env rx r_s1" and r_x="r_ex" in well_typed_diff_perms)
    apply (auto)
    (* - lemma that proves x \<notin> e, since if it was subtracted out in r_ex, thus not in r_s2a *)
  apply (cut_tac ?r_s1.0="r_s1" and r_s2a="r_s2a" and r_ex="r_ex" and x="x" in wtepl_diff_remove_lemma)
     apply (auto)
   apply (simp add: own_env_vars_def)
  apply (cut_tac env="env" and ?r_s1.0="r_s2a" and x="x" and e="e" in well_typed_no_npv_use)
    apply (auto)
  done
    
    (*
        in our inferencing completeness proof, we need to show that \<rho>( P* ) \<le> P1 for all P1.
        in order to achieve this, our selection of P* must be as small as possible. in the pair + app cases,
        we have to construct it relative to Q. our problem is that Q does not generally have a lower bound,
        since we can always subtract things out.

        we know that \<rho>( Q* - R* ) represents the so-called "real" requirements, which is to say, requirements
        barring things being subtracted out. one possibility here is that we can say given P1 |- P1 - EX, Q - EX,
        (where EX \<le> P1) we know that \<rho>( Q* - R* ) - EX \<le> Q - EX.

        in the induction for pair, it should be possible to prove lift(\<rho>( Q1* - R1* ), p) \<le> P1 since
        lift(\<rho>( Q1* - R1* ), p) \<le> lift(\<rho>( Q1* - R1* ), p) - EX + EX \<le> lift(\<rho>( Q1* - R1* ) - EX, p) + EX \<le>
          lift(Q1, p) + EX \<le> P1

        proving \<rho>( Q* - R* ) - EX \<le> Q - EX is usually simple since by the selection of EX.

        Q* and R* are generally simple. it's mostly the construction of P* that proves to be complex. for
        example, the construction for pairs is now P* = (P1* + lift(Q* - R*, p)) + (P2* + lift(Q* - R*, p)).
        most noticable is that presence of the subtraction operator now.
    *)
    
    (*
        Infer(Gamma*, X, e) = (tau*, P*, Q*, S*, K, X') \<and> \<sigma> |= K
          \<Longrightarrow> \<sigma>( Gamma* ), P1: \<sigma>( P* ) |- e: \<sigma>( tau* ), P2: \<sigma>( P* - S* ), Q: \<sigma>( Q* - S* )

        Gamma, P1 |- e1: tau1, P1 - R1, Q1 - R1
        Gamma, P2 |- e2: tau2, P2 - R2, Q2 - R2

        Gamma, P1 + P2 |- (e1, e2): (tau1, tau2)_p, (P1 + P2) - (R1 + R2), (Q1 + Q2) - (R1 + R2) 

        (P1 + P2) - (R1 + R2) \<noteq> (P1 - R1) + (P2 - R2)

        [ P* \<le> Q* ] \<Longrightarrow> P* - S* \<le> Q* - S*

        Gamma, P1 |- e: tau, P2, Q
        \<sigma>( P* ) \<le> P1

        \<sigma>( P* ) == the "minimal" P1.
        \<sigma>( P* - S* ) == the "maximal" P2 given the minimal P1.
        \<sigma>( Q* - S* ) == the "minimal" Q given the maximal P2.        
    *)

lemma well_typed_end_perm_lbound: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx \<rbrakk> \<Longrightarrow> well_typed env delta r_s1 e tau (diff_use_env r_s1 r_s1) (diff_use_env rx r_s1)"    
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)  
        apply (auto)
    (* const + op cases *)
          apply (rule_tac self_diff_leq_use_env)
         apply (rule_tac dist_diff_leq_use_env)
         apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
          apply (auto)
        apply (rule_tac self_diff_leq_use_env)
       apply (rule_tac dist_diff_leq_use_env)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (auto)
    (* var case *)
      apply (rule_tac x="r_s1" in exI)
      apply (auto)
         apply (rule_tac dist_diff_leq_use_env_gen)
          apply (rule_tac id_leq_use_env)
         apply (rule_tac dist_comp_leq_use_env)
          apply (simp)
         apply (rule_tac id_leq_use_env)
        apply (rule_tac dist_diff_leq_use_env)
        apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env (owner_name delta x) tau_x) r_ex)" in trans_leq_use_env)
         apply (rule_tac self_diff_leq_use_env)
        apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
         apply (auto)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac r_sb="diff_use_env (ereq_use_env (owner_name delta x) tau_x) (comp_use_env (comp_use_env (ereq_use_env (owner_name delta x) tau_x) r_ex) r_s1)" in trans_leq_use_env)
       apply (rule_tac lhs_unroll_dcl_use_env)
       apply (rule_tac dist_diff_leq_use_env)
       apply (simp)
      apply (rule_tac dist_diff_leq_use_env_gen)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac self_comp_leq_use_env1)
       apply (rule_tac comp_leq_use_env2)
       apply (simp)
      apply (rule_tac self_comp_leq_use_env2)
    (* pair case *)
     apply (rule_tac x="super_norm_use_env r_s1 r_s2a" in exI)
     apply (rule_tac x="super_norm_use_env (super_norm_use_env r_s1 r_s2a) r_s3" in exI)
     apply (rule_tac x="rx1" in exI)
     apply (auto)
      apply (rule_tac well_typed_sstr_end_perm)
      apply (auto)
     apply (rule_tac x="rx2" in exI)
     apply (auto)
        apply (rule_tac well_typed_sstr_end_perm)
        apply (rule_tac ?r_s1.0="r_s2a" in well_typed_incr_start_perm)
         apply (auto)
        apply (rule_tac rhs_snorm_leq_use_env)
         apply (rule_tac well_typed_perm_leq)
         apply (auto)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac rhs_snorm_leq_use_env2)
        apply (simp)
       apply (rule_tac rhs_snorm_leq_use_env2)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (rule_tac rhs_snorm_leq_use_env2)
       apply (simp)
      apply (rule_tac rhs_snorm_leq_use_env2)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (cut_tac r_s="r_s1" and r_xa="r_s2a" and r_xb="r_s3" in cancel_snorm_use_env)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (cut_tac r_s="r_s1" and r_x="r_s3" in snorm_diff_use_env)
     apply (auto)
     apply (cut_tac r_sc="r_s2" and r_sb="diff_use_env r_s3 r_ex" and r_sa="r_s1" in trans_leq_use_env)
       apply (rule_tac diff_leq_use_env)
       apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (rule_tac x="r_s1" in exI)
     apply (auto)
        apply (rule_tac rhs_diff_leq_use_env)
        apply (rule_tac dist_diff_leq_use_env_gen)
         apply (rule_tac id_leq_use_env)
        apply (simp)
       apply (rule_tac dist_diff_leq_use_env)
       apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
        apply (auto)
      apply (rule_tac id_leq_use_env)
     apply (case_tac "req_type (PairTy t1 t2 r) = Prim")
      apply (simp add: pair_req_def)
      apply (rule_tac leq_empty_use_env)
     apply (simp add: pair_req_def)
     apply (rule_tac rhs_diff_leq_use_env)
     apply (rule_tac r_sb="diff_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex" in trans_leq_use_env)
      apply (simp)
     apply (rule_tac dist_diff_leq_use_env_gen)
      apply (rule_tac id_leq_use_env)
     apply (simp)
    (* if case *)
    apply (rule_tac x="rx'" in exI)
    apply (rule_tac x="super_norm_use_env r_s1 r_s2a" in exI)
    apply (auto)
     apply (rule_tac well_typed_sstr_end_perm)
     apply (auto)
    apply (rule_tac x="diff_use_env rx1 r_s1" in exI)
    apply (auto)
     apply (rule_tac ?r_s3.0="r_s2" in wtepl_conversion)
       apply (auto)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (cut_tac env="env" and ?r_s1.0="r_s2a" and r_c="r_s1" and e="e2" and tau="tau" and ?r_s2.0="r_s2" and rx="rx1" in well_typed_incr_start_perm)
       apply (auto)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    (* - we have to do the same thing for e3 *)
    apply (rule_tac x="diff_use_env rx2 r_s1" in exI)
    apply (auto)
     apply (rule_tac ?r_s3.0="r_s2" in wtepl_conversion)
       apply (auto)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (cut_tac env="env" and ?r_s1.0="r_s2a" and r_c="r_s1" and e="e3" and tau="tau" and ?r_s2.0="r_s2" and rx="rx2" in well_typed_incr_start_perm)
       apply (auto)
     apply (rule_tac well_typed_perm_leq)
      apply (auto)
    (* - last equality *)
  apply (rule_tac s="comp_use_env (diff_use_env rx1 r_s1) (diff_use_env rx2 r_s1)" and t="diff_use_env (comp_use_env rx1 rx2) r_s1" in subst)
     apply (rule_tac dist_diff_comp_use_env)
    apply (auto)
    (* lam case *)
   apply (rule_tac x="rxa" in exI)
   apply (auto)
   apply (rule_tac x="r_s1" in exI)
   apply (auto)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac dist_diff_leq_use_env)
     apply (rule_tac r_sb="diff_use_env r_s1 r_ex" in trans_leq_use_env)
      apply (rule_tac self_diff_leq_use_env)
     apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
      apply (auto)
    apply (rule_tac id_leq_use_env)
   apply (cut_tac r_s="rxa" and r_c="r_s1" and r_x="r_ex" in cancel_diff_use_env)
    apply (auto)
   apply (rule_tac dist_diff_leq_use_env)
   apply (auto)
    (* app case *)
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="r" in exI)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="super_norm_use_env r_s1 r_s2a" in exI)
  apply (rule_tac x="rx1" in exI)
  apply (auto)
   apply (rule_tac well_typed_sstr_end_perm)
   apply (auto)
  apply (rule_tac x="rx2" in exI)
  apply (rule_tac x="super_norm_use_env r_s1 r_s3" in exI)
  apply (auto)
   apply (rule_tac r_c="super_norm_use_env (super_norm_use_env r_s1 r_s2a) r_s3" in well_typed_decr_end_perm)
     apply (rule_tac well_typed_sstr_end_perm)
     apply (rule_tac ?r_s1.0="r_s2a" in well_typed_incr_start_perm)
      apply (simp)
     apply (rule_tac rhs_snorm_leq_use_env2)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (rule_tac dist_snorm_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
    apply (rule_tac rhs_snorm_leq_use_env2)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac well_typed_perm_leqx)
   apply (auto)
    (* - prelim: useful inequality r_s3 \<le> r_s1 *)
  apply (cut_tac r_sc="r_s3" and r_sb="r_s2a" and r_sa="r_s1" in trans_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
    (* - prelim: r_s2 \<le> r_s1 *)
  apply (cut_tac r_sc="r_s2" and r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" and r_sa="r_s1" in trans_leq_use_env)
    apply (rule_tac diff_leq_use_env)
    apply (auto)
    (* - existential *)
  apply (rule_tac x="r_s1" in exI)
  apply (auto)
    (* - end perm bound *)
      apply (cut_tac r_s="r_s1" and r_x="r_s3" in snorm_diff_use_env)
      apply (auto)
      apply (rule_tac rhs_fold_dcl_use_env)
      apply (rule_tac dist_diff_leq_use_env_gen)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (simp)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
        apply (auto)
      apply (rule_tac id_leq_use_env)
    (* - containment bound *)
     apply (rule_tac rhs_snorm_leq_use_env2)
      apply (simp_all)
    (* - in-between bound *)
    apply (rule_tac dist_diff_leq_use_env)
    apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
     apply (auto)
    (* - subtractibility bound *)
   apply (rule_tac id_leq_use_env)
    (* - requirement bound *)
  apply (simp add: app_req_def)
  apply (auto)
   apply (rule_tac leq_empty_use_env)
  apply (rule_tac lhs_unroll_dcl_use_env)
  apply (rule_tac t="diff_use_env (diff_use_env (comp_use_env rx1 rx2) (comp_use_env rx1 (lift_use_env rx2 r))) r_s1" and
      s="diff_use_env (diff_use_env (diff_use_env (comp_use_env rx1 rx2) (comp_use_env rx1 (lift_use_env rx2 r))) r_s1) r_s1" in subst)
   apply (cut_tac r_s="diff_use_env (comp_use_env rx1 rx2) (comp_use_env rx1 (lift_use_env rx2 r))" and r_x="r_s1" in double_diff_use_env)
   apply (auto)
  apply (rule_tac dist_diff_leq_use_env)
  apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac rhs_unroll_dcl_use_env)
  apply (rule_tac dist_diff_leq_use_env_gen)
   apply (rule_tac id_leq_use_env)
  apply (simp)
  done
    
end