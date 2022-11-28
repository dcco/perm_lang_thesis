theory ReduceWTS
  imports ReduceExp ResMapValid
begin
  
  (*
      a value is a "resource" if it cannot be copied across threads (always has a distinct owner).
      - all arrays are resources, because they cannot be copied. the question is whether they can contain
        other resources (multi-dimensional arrays, etc). the issue with this would be that there is no
        easy way to read resources from an array. however the idea is that the expression 'read a 0'
        should still hold 'a' in its requirements. so it should be safe to simply allow arrays to contain
        anything.
      - pairs are similar, although they can be copied assuming that they have copyable elements.
        however to be valid in our system, they would actually have to be copied, which is problematic.
        it would be nice to have both a copyable pair + reference pair.
        i think the easier thing would be to change the notion of validity, namely to only care about
        "mutable" values.
  *)
  
  (* so the idea here is that arrays et al CAN contain unlimited resources.
      - this means that some arrays require permissions to be typed. allowing for this is already within our preparations.
      - except that because arrays are unlimited, they dont require ownership, even when you write to them. the question is,
          does that make sense?
      - fundamentally, an array being "unlimited" means that it can have multiple aliases, because we aren't worried about destructive
        operations being performed with it. technically a pair is the same way iirc?
      - but what happens when we perform an array write? the issue is, we still require ownership because in theory it "belongs" to it in
        a sense. so then an array can contain any datatype, so long as it always contains unique copies of said datatype.
      - what happens when you read such a value? when you read one out, you should only gain use permission for the data value. and this is where
        leaking can happen.
  *)  
  
  (* ###### well-typed state definitions  *)
  
    (* defines well-typedness for an array's contents. since we allow arrays to contain other (unlimited)
      arrays, we may need permissions to type the contents. which means it may exist in multiple places.
      so the idea is that every resource is tied to a specific thread. *)
    (*
fun well_typed_list where
  "well_typed_list env rs_list Nil n tau = True"
| "well_typed_list env rs_list (e # t) n tau = (\<exists> delta r_x. rs_list n = Some r_x \<and>
  well_typed env delta r_x e tau r_x r_x \<and> is_value e \<and> well_typed_list env rs_list t (n + 1) tau)"
  *)

fun well_typed_list where
  "well_typed_list env delta r_s Nil tau = True"
| "well_typed_list env delta r_s (e # t) tau = (well_typed env delta r_s e tau r_s r_s \<and>
    is_value e \<and> well_typed_list env delta r_s t tau)"

definition disj_res_list where
  "disj_res_list r_x i rs_list = (\<forall> j r_y. i \<noteq> j \<and> rs_list j = Some r_y \<longrightarrow> strong_disj_use_env r_x r_y)"  
  
definition valid_res_list :: "perm_use_env \<Rightarrow> (int \<Rightarrow> perm_use_env option) \<Rightarrow> bool" where
  "valid_res_list r_s rs_list = (\<forall> i r_x. rs_list i = Some r_x \<longrightarrow> leq_use_env r_x r_s \<and> disj_res_list r_x i rs_list)"    
  
    (* for pairs, the idea is that if there are extra permissions necessary to type e1 + e2 (which may not be
      affine), we expect them to be completely separate from any pre-extant permissions. *)
  
  (*
fun well_typed_mem_value where
  "well_typed_mem_value env r_s tau (ArrValue el) = (\<exists> rs_list t. tau = ArrayTy t \<and> unlim t \<and>
    valid_res_list r_s rs_list \<and> well_typed_list env rs_list el 0 t)"
| "well_typed_mem_value env r_s tau ChanSValue = (\<exists> t. tau = ChanTy t SEnd)"
| "well_typed_mem_value env r_s tau (ChanRValue c_s) = (\<exists> t. tau = ChanTy t REnd \<and>
    env (Loc c_s) = Some (ChanTy t SEnd))"*)

fun well_typed_mem_value where
  "well_typed_mem_value env delta r_s tau (ArrValue el) = (\<exists> t. tau = ArrayTy t \<and> unlim t \<and>
    well_typed_list env delta r_s el t)"
| "well_typed_mem_value env delta r_s tau ChanSValue = (\<exists> t. tau = ChanTy t SEnd)"
| "well_typed_mem_value env delta r_s tau (ChanRValue c_s) = (\<exists> t. tau = ChanTy t REnd \<and>
    env (Loc c_s) = Some (ChanTy t SEnd))"
  (*
fun proper_list where
  "proper_list rs_map Nil = True"
| "proper_list rs_map (e # t) = (proper_exp rs_map e \<and> proper_list rs_map t)"  
  
fun proper_mem_value where
  "proper_mem_value rs_map (ArrValue el) = proper_list rs_map el"
| "proper_mem_value rs_map other = True"

  *)
    (* all pairs must be typable  *)(*
| "well_typed_mem_value s env r_s tau (PairValue e1 e2) = (\<exists> t1 t2 r rx1 rx2. tau = PairTy t1 t2 r \<and> is_value e1 \<and> is_value e2 \<and>
  leq_use_env (lift_use_env rx1 r) r_s \<and> leq_use_env (lift_use_env rx2 r) r_s \<and> disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r) \<and>
  safe_use_lift rx1 r \<and> safe_use_lift rx2 r \<and> safe_type t1 r \<and> safe_type t2 r \<and>
  well_typed env r_s e1 t1 r_s rx1 \<and> well_typed env r_s e2 t2 r_s rx2)"   *) 
  
lemma well_typed_list_add_vars: "\<lbrakk> well_typed_list env delta r_s l tau; env x = None \<rbrakk> \<Longrightarrow> well_typed_list (add_env env x t) delta r_s l tau"  
  apply (induct l)
   apply (auto)
  apply (rule_tac well_typed_add_varsx)
   apply (auto)
  done
  
lemma well_typed_mem_non_prim_type: "\<lbrakk> well_typed_mem_value env delta r_s tau v \<rbrakk> \<Longrightarrow> req_type tau \<noteq> Prim"    
  apply (case_tac v)
    apply (auto)
  done      
    
lemma well_typed_mem_ref_type: "\<lbrakk> well_typed_mem_value env delta r_s tau v \<rbrakk> \<Longrightarrow> req_type tau = Ref"        
  apply (case_tac v)
    apply (auto)
  done
  
lemma well_typed_mv_add_vars: "\<lbrakk> well_typed_mem_value env delta r_s tau v; env x = None \<rbrakk> \<Longrightarrow>
  well_typed_mem_value (add_env env x t) delta r_s tau v"    
  apply (case_tac v)
  apply (auto)
   apply (rule_tac well_typed_list_add_vars)
    apply (auto)
  apply (simp add: add_env_def)
  apply (auto)
  done 
    
definition add_delta :: "owner_env \<Rightarrow> string \<Rightarrow> string \<Rightarrow> owner_env" where  
  "add_delta delta x y = (\<lambda> z. if z = x then y else delta z)"    

lemma well_typed_add_delta: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; env (Loc x) = None \<rbrakk> \<Longrightarrow> well_typed env (add_delta delta x x) r_s1 e tau r_s2 rx"  
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
    (* var case *)
      apply (case_tac "owner_name delta xa \<noteq> owner_name (add_delta delta x x) xa")
       apply (case_tac xa)
        apply (auto)
      apply (simp add: add_delta_def)
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
   apply (case_tac "add_env env (Var x1a) t1 (Loc x) \<noteq> None")
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
    
lemma well_typed_list_add_delta: "\<lbrakk> well_typed_list env delta r_s l tau; env (Loc x) = None \<rbrakk> \<Longrightarrow> well_typed_list env (add_delta delta x x) r_s l tau"  
  apply (induct l)
   apply (auto)
  apply (rule_tac well_typed_add_delta)
   apply (auto)
  done  
  
lemma well_typed_mv_add_delta: "\<lbrakk> well_typed_mem_value env delta r_s tau v; env (Loc x) = None \<rbrakk> \<Longrightarrow>
  well_typed_mem_value env (add_delta delta x x) r_s tau v"
  apply (case_tac v)
    apply (auto)
  apply (rule_tac well_typed_list_add_delta)
   apply (auto)
  done
    
    (*
      reducing an expression may change the external state. we expect the type environment +
      permissions environment to change accordingly. so we need to be able to construct a
      type env / perm env that "matches" the state. so what does it mean for them to match it?

      obviously every value in the external state has to be typable by its assigned type. i
      think it's okay for it to have the same environment. the key is that the permissions
      environments between all of them must be completely disjoint, including from the expression
      being reduced.
    *) 
  
    (* given a state, we say a type env "matches" (types) it if every value from the state can be typed by it.
      the biggest question concerning this is how to deal with well_typed_state.

      all resource values, regardless of whether they are affine or not, cannot be included in more
      than one reference, the reason being that it removes their "distinct"-ness.
    *)
  
    (*
definition well_typed_state where
  "well_typed_state s env rs_map = (sub_env s env \<and> valid_res_map s rs_map \<and> (\<forall> x. case s x of
    None \<Rightarrow> True
    | Some v \<Rightarrow> (case env x of
      None \<Rightarrow> False 
      | Some tau \<Rightarrow> well_typed_mem_value s env (lookup_res rs_map x) tau v
    )
  ))" *)    
    (*
definition proper_delta where
  "proper_delta s delta = (\<forall> x. case s x of
    None \<Rightarrow> True
    | Some v \<Rightarrow> (\<exists> l. path_lookup s (delta x) l x)
  )"*)
    
definition proper_delta where
  "proper_delta s delta = (\<forall> x. case s x of
    None \<Rightarrow> True
    | Some v \<Rightarrow> s (delta x) \<noteq> None
  )"  
  
  (* the paper has a requirement that dom(s) = dom(env), while this definition only states that dom(env) \<subseteq> dom(s).
    the reverse direction that dom(s) \<subseteq> dom(env) is implicit in this definition by the case analysis *)
definition well_typed_state :: "p_state \<Rightarrow> pt_env \<Rightarrow> owner_env \<Rightarrow> bool" where
  "well_typed_state s env delta = (sub_env s env \<and> proper_delta s delta \<and> (\<forall> x. case s x of
    None \<Rightarrow> True
    | Some v \<Rightarrow> (case env (Loc x) of
      None \<Rightarrow> False 
      | Some tau \<Rightarrow> well_typed_mem_value env delta (one_use_env (Loc (delta x)) UsePerm) tau v
    )
  ))"    
    
definition non_prim_env :: "pt_env \<Rightarrow> bool" where
  "non_prim_env env = (\<forall> x. case env x of
    None \<Rightarrow> True
    | Some tau \<Rightarrow> req_type tau \<noteq> Prim
  )"
  
definition ref_env :: "pt_env \<Rightarrow> bool" where
  "ref_env env = (\<forall> x. case env x of
    None \<Rightarrow> True
    | Some tau \<Rightarrow> req_type tau = Ref
  )"  
  
    (* env is primitive because every element of env is a well-typed memory value *)
lemma well_typed_state_non_prim_env: "\<lbrakk> well_typed_state s env delta \<rbrakk> \<Longrightarrow> non_prim_env env"    
  apply (simp add: well_typed_state_def)
  apply (simp add: non_prim_env_def)
  apply (auto)
  apply (case_tac "env x")
   apply (auto)
  apply (simp add: sub_env_def)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (erule_tac x="y" in allE)
  apply (auto)
  apply (cut_tac tau="a" in well_typed_mem_non_prim_type)
   apply (auto)
  done     

lemma well_typed_state_ref_env: "\<lbrakk> well_typed_state s env delta \<rbrakk> \<Longrightarrow> ref_env env"       
  apply (simp add: well_typed_state_def)
  apply (simp add: ref_env_def)
  apply (auto)
  apply (case_tac "env x")
   apply (auto)
  apply (simp add: sub_env_def)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (erule_tac x="y" in allE)
  apply (auto)
  apply (cut_tac tau="a" in well_typed_mem_ref_type)
   apply (auto)
  done   
    
lemma prim_type_no_req: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; req_type tau = Prim; non_prim_env env \<rbrakk> \<Longrightarrow> well_typed env delta r_s1 e tau r_s2 empty_use_env"  
  apply (induct e arbitrary: env r_s1 tau r_s2 rx)
        apply (auto)
        apply (rule_tac leq_empty_use_env)
       apply (rule_tac leq_empty_use_env)
      apply (simp add: non_prim_env_def)
      apply (erule_tac x="res_name x" in allE)
      apply (case_tac x)
       apply (auto)
     apply (rule_tac x="r_s2a" in exI)
     apply (rule_tac x="r_s3" in exI)
     apply (rule_tac x="rx1" in exI)
     apply (auto)
     apply (rule_tac x="rx2" in exI)
     apply (auto)
     apply (rule_tac x="r_ex" in exI)
     apply (auto)
      apply (rule_tac leq_empty_use_env)
     apply (simp add: pair_req_def)
     apply (rule_tac leq_empty_use_env)
    apply (rule_tac x="rx'" in exI)
    apply (rule_tac x="r_s2a" in exI)
    apply (auto)
    apply (rule_tac x="empty_use_env" in exI)
    apply (auto)
    apply (rule_tac x="empty_use_env" in exI)
    apply (auto)
    apply (rule_tac comp_empty_use_env)
   apply (rule_tac x="rxa" in exI)
   apply (auto)
   apply (rule_tac x="r_ex" in exI)
   apply (auto)
    apply (rule_tac leq_empty_use_env)
   apply (rule_tac diff_leq_use_env)
   apply (simp add: aff_use_env_def)
   apply (simp add: leq_use_env_def)
   apply (simp add: null_use_env_def)
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="r" in exI)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="r_s2a" in exI)
  apply (rule_tac x="rx1" in exI)
  apply (auto)
  apply (rule_tac x="rx2" in exI)
  apply (rule_tac x="r_s3" in exI)
  apply (auto)
  apply (rule_tac x="r_ex" in exI)
  apply (auto)
   apply (rule_tac leq_empty_use_env)
  apply (simp add: app_req_def)
  apply (rule_tac leq_empty_use_env)
  done
    
    
lemma add_vars_path_lookup: "\<lbrakk> path_lookup rs_map x l y; leq_use_env (nres_lookup rs_map z) r_s \<rbrakk> \<Longrightarrow>
  (\<exists> l. path_lookup (add_env rs_map z r_s) x l y)"    
  apply (induct l arbitrary: x)
   apply (auto)
   apply (rule_tac x="Nil" in exI)
   apply (auto)
  apply (case_tac "rs_map x")
   apply (auto)
  apply (case_tac "\<exists>l. path_lookup (add_env rs_map z r_s) a l y")
   apply (erule_tac exE)
   apply (auto)
  apply (rule_tac x="a # la" in exI)
  apply (auto)
  apply (simp add: add_env_def)
  apply (auto)
  apply (simp add: nres_lookup_def)
  apply (cut_tac r_x="aa" and r_s="r_s" and x="Loc a" in leq_use_none)
    apply (auto)
  done


lemma wts_mem_val_env: "\<lbrakk> well_typed_state s env delta \<rbrakk> \<Longrightarrow> mem_val_env env"
  apply (simp add: mem_val_env_def)
  apply (auto)
  apply (case_tac "x")
   apply (auto)
  apply (case_tac "env (Loc x2)")
   apply (auto)
  apply (simp add: well_typed_state_def)
  apply (auto)
  apply (simp add: sub_env_def)
  apply (erule_tac x="Loc x2" in allE)
  apply (auto)
  apply (erule_tac x="x2" in allE)
  apply (auto)
  apply (case_tac y)
    apply (auto)
  done           
  
lemma wts_well_formed_delta: "well_typed_state s env delta \<Longrightarrow> well_formed_delta env delta"
  apply (simp add: well_formed_delta_def)
  apply (auto)
    (* we want to show that if a location is in the env, its ancestor is as well, and they have appropriate types. *)
  apply (case_tac "env (Loc x)")
   apply (auto)
    (* first we show that the ancestor is in the state. *)
  apply (case_tac "s (delta x) = None")
   apply (simp add: well_typed_state_def)
    apply (case_tac "s x = None")
    apply (simp add: sub_env_def)
    apply (auto)
   apply (simp add: proper_delta_def)
   apply (erule_tac x="x" in allE)
   apply (auto)
    (* this can be used to show that the ancestor is in the env. *)
  apply (case_tac "env (Loc (delta x)) = None")
   apply (simp add: well_typed_state_def)
   apply (auto)
   apply (erule_tac x="delta x" in allE)
    apply (auto)
    (* lastly, we prove the types are as expected *)
   apply (cut_tac env="env" in well_typed_state_ref_env)
    apply (auto)
   apply (simp add: ref_env_def)
   apply (erule_tac x="Loc (delta x)" in allE)
   apply (auto)
  apply (cut_tac env="env" in well_typed_state_ref_env)
   apply (auto)
  apply (simp add: ref_env_def)
  apply (erule_tac x="Loc x" in allE)
  apply (auto)
  done   

    (*
lemma wts_ref_memory: "\<lbrakk> well_typed_state s env delta rs_map \<rbrakk> \<Longrightarrow> ref_memory env"  
  apply (simp add: well_typed_state_def)
  apply (simp add: ref_memory_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (simp add: sub_env_def)
  apply (erule_tac x="Loc x" in allE)
  apply (auto)
  apply (case_tac "env (Loc x)")
   apply (auto)
  apply (case_tac y)
    apply (auto)
  done*)  
    
end