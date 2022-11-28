theory WellTypedExp
  imports WTMiscEnv
begin

    (* 
      ####################################
        P1. expression syntax
      ####################################
    *)

    (* expressions *)
  
datatype p_const =
  UnitConst
  | IConst int
  | BConst bool
  | FixConst
    (* arrays *)
  (*| EmptyArrayConst
  | ExtArrayConst*)
  | NullConst
  | NewArrayConst
  | ReadConst
  | WriteConst
    (* pairs *)
  | UnpackConst
    (* channels *)
  | NewChanConst
  | SendConst
  | RecvConst
  | ForkConst

datatype p_op =
  I2Op "int \<Rightarrow> int \<Rightarrow> int"
  | I1Op "int \<Rightarrow> int"
  | C2Op "int \<Rightarrow> int \<Rightarrow> bool"
  | C1Op "int \<Rightarrow> bool"
  | R2Op "bool \<Rightarrow> bool \<Rightarrow> bool"
  | R1Op "bool \<Rightarrow> bool"

datatype var_type =
  VarType string
  | LocType string
    
datatype p_exp =
  ConstExp p_const
  | OpExp p_op
  | VarExp var_type
  | PairExp p_exp p_exp
  | IfExp p_exp p_exp p_exp
  | LamExp string p_exp
  | AppExp p_exp p_exp  
    
fun bin_const where
  "bin_const ReadConst = True"
| "bin_const WriteConst = True"
| "bin_const SendConst = True"
| "bin_const c = False"
  
fun is_value :: "p_exp \<Rightarrow> bool" where    
  "is_value (ConstExp c) = True"
| "is_value (OpExp xop) = True"
| "is_value (VarExp (LocType x)) = True"
| "is_value (PairExp v1 v2) = (is_value v1 \<and> is_value v2)"
| "is_value (LamExp x e) = True"
| "is_value (AppExp (ConstExp c) v) = (bin_const c \<and> is_value v)"
| "is_value other = False"

fun is_sexp :: "p_exp \<Rightarrow> bool" where
  "is_sexp (ConstExp c) = True"
| "is_sexp (OpExp xop) = True"
| "is_sexp (VarExp (VarType x)) = False"
| "is_sexp (VarExp (LocType x)) = True"
| "is_sexp (PairExp v1 v2) = (is_value v1 \<and> is_value v2)"
| "is_sexp (LamExp x e) = True"
| "is_sexp (AppExp (ConstExp FixConst) (LamExp x e)) = True"
| "is_sexp (AppExp (ConstExp c) v) = (bin_const c \<and> is_value v)"
| "is_sexp other = False"        
    
fun free_vars :: "p_exp \<Rightarrow> string set" where
  "free_vars (ConstExp c) = {}"
| "free_vars (OpExp xop) = {}"
| "free_vars (VarExp v) = (case v of
  VarType x \<Rightarrow> {x}
  | other \<Rightarrow> {}
)"
| "free_vars (PairExp e1 e2) = free_vars e1 \<union> free_vars e2"
| "free_vars (IfExp e1 e2 e3) = free_vars e1 \<union> free_vars e2 \<union> free_vars e3"
| "free_vars (LamExp x e) = free_vars e - {x}"
| "free_vars (AppExp e1 e2) = free_vars e1 \<union> free_vars e2"
  
fun ref_vars :: "p_exp \<Rightarrow> string set" where
  "ref_vars (ConstExp c) = {}"
| "ref_vars (OpExp xop) = {}"
| "ref_vars (VarExp v) = (case v of
    VarType x \<Rightarrow> {}
    | LocType x \<Rightarrow> {x}
  )"
| "ref_vars (PairExp e1 e2) = ref_vars e1 \<union> ref_vars e2"
| "ref_vars (IfExp e1 e2 e3) = ref_vars e1 \<union> ref_vars e2 \<union> ref_vars e3"
| "ref_vars (LamExp x e) = ref_vars e"
| "ref_vars (AppExp e1 e2) = ref_vars e1 \<union> ref_vars e2"    
  
type_synonym owner_env = "string \<Rightarrow> string"  
  
fun res_name where
  "res_name (VarType x) = Var x"  
| "res_name (LocType x) = Loc x"

fun owner_name where
  "owner_name delta (VarType x) = Var x"
| "owner_name delta (LocType x) = Loc (delta x)"  
  
fun res_vars :: "owner_env \<Rightarrow> p_exp \<Rightarrow> res_id set" where
  "res_vars delta (ConstExp c) = {}"
| "res_vars delta (OpExp xop) = {}"
| "res_vars delta (VarExp v) = {owner_name delta v}"
| "res_vars delta (PairExp e1 e2) = res_vars delta e1 \<union> res_vars delta e2"
| "res_vars delta (IfExp e1 e2 e3) = res_vars delta e1 \<union> res_vars delta e2 \<union> res_vars delta e3"
| "res_vars delta (LamExp x e) = res_vars delta e - {Var x}"
| "res_vars delta (AppExp e1 e2) = res_vars delta e1 \<union> res_vars delta e2" 
  
definition non_prim_vars where
  "non_prim_vars env delta e = { x | x. non_prim_entry env x \<and> x \<in> res_vars delta e }"
  
definition env_vars :: "(string \<Rightarrow> 'a option) \<Rightarrow> string set" where
  "env_vars env = { x | x. env x \<noteq> None }"

definition use_env_vars where
  "use_env_vars r_s = { x | x. r_s x \<noteq> NoPerm }"
  
definition own_env_vars where
  "own_env_vars r_s = { x | x. r_s x = OwnPerm }"    
  
    (* 
      ####################################
        P4. type system for expressions
      ####################################
    *)
  
definition pure_fun where
  "pure_fun t1 t2 r = FunTy t1 t2 UsePerm r"  

fun aff_leq where
  "aff_leq Prim r = True"  
| "aff_leq Ref NoPerm = False"  
| "aff_leq Ref r = True"
| "aff_leq Aff OwnPerm = True"  
| "aff_leq Aff r = False"    
  
fun is_nullable where
  "is_nullable (FunTy t1 t2 p a) = True"  
| "is_nullable (ChanTy tau c_end) = True"  
| "is_nullable (ArrayTy tau) = True"  
| "is_nullable tau = False"  
  
fun const_type :: "p_const \<Rightarrow> p_type set" where
  "const_type UnitConst = {UnitTy}"
| "const_type (IConst i) = {IntTy}"
| "const_type (BConst b) = {BoolTy}"
| "const_type FixConst = {pure_fun (pure_fun t t (req_type t)) t Prim | t. fun_ty t \<and> unlim t}"
  (* arrays: since t is unlim and arrays are unlim, no functions require ownership.
      pairs are affine because they are only needed once. *)
(*| "const_type EmptyArrayConst = {pure_fun UnitTy (ArrayTy t) Prim | t. unlim t}"
| "const_type ExtArrayConst = {pure_fun (ArrayTy t) (FunTy t (ArrayTy t) OwnPerm Ref) Prim | t. unlim t}"*)
| "const_type NewArrayConst = {pure_fun IntTy (ArrayTy tau) Prim | tau. unlim tau}"
| "const_type NullConst = { tau | tau. True }"
| "const_type ReadConst = {pure_fun (ArrayTy t) (pure_fun IntTy t Ref) Prim | t. unlim t}"
| "const_type WriteConst = {pure_fun (ArrayTy t) (FunTy (PairTy IntTy t OwnPerm) UnitTy OwnPerm Ref) Prim | t. unlim t}"
  (* pairs: a reusable pair must be constructed from unlimited values + requires ownership of both its elements,
    however permissions-wise it is treated like a var.
      - an affine pair can be constructed from anything, and also requires ownership of both its elements
       - for unpacking, the pair is assumed to be owned, whatever is put in *)
| "const_type UnpackConst = {FunTy (PairTy t1 t2 r) (FunTy (FunTy t1 (FunTy t2 tx r (as_aff r')) r (as_aff r')) tx r' (as_aff r)) r Prim | t1 t2 tx r r'. leq_perm r r'}"
  (* channels: all uses of a channel use up ownership *)
| "const_type NewChanConst = {pure_fun UnitTy (PairTy (ChanTy tau SEnd) (ChanTy tau REnd) OwnPerm) Prim | tau. True}"
| "const_type SendConst = {pure_fun (ChanTy t SEnd) (FunTy t UnitTy r Ref) Prim | t r. is_own r}"
| "const_type RecvConst = {pure_fun (ChanTy t REnd) t Prim | t. True }"
| "const_type ForkConst = {FunTy (FunTy UnitTy UnitTy UsePerm a) UnitTy r Prim | a r. is_own r}"
  
fun op_type :: "p_op \<Rightarrow> p_type" where
  "op_type (I2Op xop) = pure_fun IntTy (pure_fun IntTy IntTy Prim) Prim"
| "op_type (I1Op xop) = pure_fun IntTy IntTy Prim"
| "op_type (C2Op xop) = pure_fun IntTy (pure_fun IntTy BoolTy Prim) Prim"
| "op_type (C1Op xop) = pure_fun IntTy BoolTy Prim"
| "op_type (R2Op xop) = pure_fun BoolTy (pure_fun BoolTy BoolTy Prim) Prim"
| "op_type (R1Op xop) = pure_fun BoolTy BoolTy Prim"

definition app_req where
  "app_req rx1 rx2 r tau r_ex = (if req_type tau = Prim then empty_use_env else
    diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex))"  
  
definition pair_req where
  "pair_req rx r_ex tau = (if req_type tau = Prim then empty_use_env else diff_use_env rx r_ex)"  
  
fun safe_type where
  "safe_type tau OwnPerm = True"
| "safe_type tau UsePerm = unlim tau"
| "safe_type tau NoPerm = False"  

fun safe_type_x where
  "safe_type_x tau OwnPerm = True"
| "safe_type_x tau UsePerm = unlim tau"
| "safe_type_x tau NoPerm = (req_type tau = Prim)"

  
fun safe_pair_aff where
  "safe_pair_aff a NoPerm = False"  
| "safe_pair_aff a UsePerm = (a \<noteq> Aff)"
| "safe_pair_aff a OwnPerm = True"
  


  (*
fun value_req where
  "value_req (VarType x) tau tau_x = True"  
| "value_req (LocType x) tau tau_x = (req_type tau = Ref \<and> req_type tau_x = Ref)"  
  *)
  
fun well_typed :: "pt_env \<Rightarrow> owner_env \<Rightarrow> perm_use_env \<Rightarrow> p_exp \<Rightarrow> p_type \<Rightarrow> perm_use_env \<Rightarrow> perm_use_env \<Rightarrow> bool" where
  "well_typed env delta r_s1 (ConstExp c) tau r_s2 rx = (tau \<in> const_type c \<and> leq_use_env r_s2 r_s1 \<and> leq_use_env rx r_s2)"
| "well_typed env delta r_s1 (OpExp xop) tau r_s2 rx = (tau = op_type xop \<and> leq_use_env r_s2 r_s1 \<and> leq_use_env rx r_s2)"
| "well_typed env delta r_s1 (VarExp v) tau r_s2 rx = (\<exists> r_ex tau_x. env (res_name v) = Some tau \<and> env (owner_name delta v) = Some tau_x \<and> (*value_req v tau tau_x \<and>*)
    leq_use_env (ereq_use_env (owner_name delta v) tau_x) r_s1 \<and> leq_use_env r_s2 (diff_use_env r_s1 (comp_use_env (ereq_use_env (owner_name delta v) tau_x) r_ex)) \<and>
    leq_use_env rx r_s2 \<and> leq_use_env r_ex r_s1 \<and> leq_use_env (diff_use_env (ereq_use_env (owner_name delta v) tau_x) (comp_use_env (ereq_use_env (owner_name delta v) tau_x) r_ex)) rx)" 
| "well_typed env delta r_s1 (PairExp e1 e2) tau r_sf rf = (\<exists> t1 t2 r r_s2 r_s3 rx1 rx2 r_ex. tau = PairTy t1 t2 r \<and>
    well_typed env delta r_s1 e1 t1 r_s2 rx1 \<and> well_typed env delta r_s2 e2 t2 r_s3 rx2 \<and>
    leq_use_env (lift_use_env rx1 r) r_s3 \<and> leq_use_env (lift_use_env rx2 r) r_s3 \<and> aff_leq (max_aff (req_type t1) (req_type t2)) r \<and>
    disj_use_env (lift_use_env rx1 r) (lift_use_env rx2 r) \<and>
    leq_use_env r_sf (diff_use_env r_s3 r_ex) \<and> leq_use_env rf r_sf \<and> leq_use_env r_ex r_s1 \<and>
    leq_use_env (pair_req (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex tau) rf
  )"
| "well_typed env delta r_s1 (IfExp e1 e2 e3) tau r_s3 rx = (\<exists> rx' r_s2 rx1 rx2.
    well_typed env delta r_s1 e1 BoolTy r_s2 rx' \<and> well_typed env delta r_s2 e2 tau r_s3 rx1 \<and> well_typed env delta r_s2 e3 tau r_s3 rx2 \<and>
    rx = comp_use_env rx1 rx2)"
| "well_typed env delta r_s1 (LamExp x e) tau r_s2 rf = (\<exists> t1 t2 r a rx r_end r_s' r_ex. tau = FunTy t1 t2 r a \<and>
    well_typed (add_env env (Var x) t1) delta (add_use_env rx (Var x) r) e t2 r_s' r_end \<and> aff_use_env rx a \<and>
    leq_use_env rx r_s1 \<and> leq_use_env r_s2 (diff_use_env r_s1 r_ex) \<and> leq_use_env rf r_s2 \<and>
    leq_use_env r_ex r_s1 \<and> leq_use_env (diff_use_env rx r_ex) rf)"
| "well_typed env delta r_s1 (AppExp e1 e2) tau r_sf rx = (\<exists> t1 r a r_s2 rx1 rx2 r_s3 r_ex.
    well_typed env delta r_s1 e1 (FunTy t1 tau r a) r_s2 rx1 \<and> well_typed env delta r_s2 e2 t1 r_s3 rx2 \<and>
    leq_use_env r_sf (diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)) \<and>
    leq_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_s3 \<and>
    disj_use_env rx1 (lift_use_env rx2 r) \<and> leq_use_env rx r_sf \<and> 
    leq_use_env r_ex r_s1 \<and> leq_use_env (app_req rx1 rx2 r tau r_ex) rx
  )" 
  
    (* - expression lemmas *)

lemma value_is_sexp: "is_value e \<Longrightarrow> is_sexp e"    
  apply (case_tac e)
        apply (auto)
   apply (case_tac x3)
    apply (auto)
  apply (case_tac x71)
        apply (auto)
  apply (case_tac x1)
              apply (auto)
  done
    
lemma e2_sexp: "\<lbrakk> is_sexp (AppExp e1 e2) \<rbrakk> \<Longrightarrow> is_sexp e2" 
  apply (case_tac e1)
       apply (auto)
  apply (case_tac e2)
        apply (auto)
   apply (case_tac x3)
    apply (auto)
  apply (case_tac x71)
        apply (auto)
  apply (case_tac x1a)
              apply (auto)
  done    
    
end