module TieredSystemFNoBidi where

open import Relation.Binary.PropositionalEquality




data TypeContext : Set where
  [] : TypeContext
  _,type : TypeContext -> TypeContext





data RawTypeVar : Set where
  here : RawTypeVar
  there : RawTypeVar -> RawTypeVar

data TypeVar : TypeContext -> Set where
  here : forall {H} -> TypeVar (H ,type)
  there : forall {H} -> TypeVar H -> TypeVar (H ,type)

data IsTypeVar : TypeContext -> RawTypeVar -> Set where
  here : forall {H} -> IsTypeVar (H ,type) here
  there : forall {H a} -> IsTypeVar H a -> IsTypeVar (H ,type) (there a)

data IsNotTypeVar : TypeContext -> RawTypeVar -> Set where
  not-var : forall {a} -> IsNotTypeVar [] a
  not-there : forall {H a} -> IsNotTypeVar H a -> IsNotTypeVar (H ,type) (there a)

data CheckedTypeVar (H : TypeContext) (a : RawTypeVar) : Set where
  isTypeVar : IsTypeVar H a -> CheckedTypeVar H a
  isNotTypeVar : IsNotTypeVar H a -> CheckedTypeVar H a

checkTypeVar : (H : TypeContext) -> (a : RawTypeVar) -> CheckedTypeVar H a
checkTypeVar [] a = isNotTypeVar not-var
checkTypeVar (H ,type) here = isTypeVar here
checkTypeVar (H ,type) (there a) with checkTypeVar H a
checkTypeVar (H ,type) (there a) | isTypeVar p = isTypeVar (there p)
checkTypeVar (H ,type) (there a) | isNotTypeVar np = isNotTypeVar (not-there np)

extractRawTypeVar : forall {H} -> TypeVar H -> RawTypeVar
extractRawTypeVar here = here
extractRawTypeVar (there a) = there (extractRawTypeVar a)

extractTypeVar : forall {H a} -> (P : IsTypeVar H a) -> TypeVar H
extractTypeVar here = here
extractTypeVar (there a) = there (extractTypeVar a)

coherenceTypeVar : forall {H a} -> (P : IsTypeVar H a) -> extractRawTypeVar (extractTypeVar P) ≡ a
coherenceTypeVar here = refl
coherenceTypeVar (there P) rewrite coherenceTypeVar P = refl

checkTypeVarCorrect : forall {H a} -> (P : IsTypeVar H a) -> checkTypeVar H a ≡ isTypeVar P
checkTypeVarCorrect here = refl
checkTypeVarCorrect (there P) rewrite checkTypeVarCorrect P = refl

data EqTypeVar : forall H -> TypeVar H -> TypeVar H -> Set where
  here : forall {H} -> EqTypeVar (H ,type) here here
  there : forall {H a a'} -> EqTypeVar H a a' -> EqTypeVar (H ,type) (there a) (there a')

data NotEqTypeVar : forall H -> TypeVar H -> TypeVar H -> Set where
  here-there : forall {H a'} -> NotEqTypeVar (H ,type) here (there a')
  there-here : forall {H a} -> NotEqTypeVar (H ,type) (there a) here
  there-there : forall {H a a'} -> NotEqTypeVar H a a' -> NotEqTypeVar (H ,type) (there a) (there a')

data CheckEqTypeVar {H} (a a' : TypeVar H) : Set where
  eqTypeVar : EqTypeVar H a a' -> CheckEqTypeVar a a'
  notEqTypeVar : NotEqTypeVar H a a' -> CheckEqTypeVar a a'

checkEqTypeVar : forall {H} -> (a a' : TypeVar H) -> CheckEqTypeVar a a'
checkEqTypeVar here here = eqTypeVar here
checkEqTypeVar here (there a') = notEqTypeVar here-there
checkEqTypeVar (there a) here = notEqTypeVar there-here
checkEqTypeVar (there a) (there a') with checkEqTypeVar a a'
checkEqTypeVar (there a) (there a') | eqTypeVar p = eqTypeVar (there p)
checkEqTypeVar (there a) (there a') | notEqTypeVar np = notEqTypeVar (there-there np)

checkEqTypeVarCorrect : forall {H a a'} -> (P : EqTypeVar H a a') -> checkEqTypeVar a a' ≡ eqTypeVar P
checkEqTypeVarCorrect here = refl
checkEqTypeVarCorrect (there a) rewrite checkEqTypeVarCorrect a = refl

reflEqTypeVar : forall {H} {a : TypeVar H} -> EqTypeVar H a a
reflEqTypeVar {a = here} = here
reflEqTypeVar {a = there a} = there reflEqTypeVar





data RawType : Set where
  var : RawTypeVar -> RawType
  _=>_ : RawType -> RawType -> RawType
  all : RawType -> RawType

data Type (H : TypeContext) : Set where
  var : TypeVar H -> Type H
  _=>_ : Type H -> Type H -> Type H
  all : Type (H ,type) -> Type H

data IsType (H : TypeContext) : RawType -> Set where
  var : forall {a} -> IsTypeVar H a -> IsType H (var a)
  _=>_ : forall {A B} -> IsType H A -> IsType H B -> IsType H (A => B)
  all : forall {A} -> IsType (H ,type) A -> IsType H (all A)

data IsNotType (H : TypeContext) : RawType -> Set where
  not-var : forall {a} -> IsNotTypeVar H a -> IsNotType H (var a)
  not-=>-L : forall {A B} -> IsNotType H A -> IsNotType H (A => B)
  not-=>-R : forall {A B} -> IsType H A -> IsNotType H B -> IsNotType H (A => B)
  not-all : forall {A} -> IsNotType (H ,type) A -> IsNotType H (all A)

data CheckedType (H : TypeContext) (A : RawType) : Set where
  isType : IsType H A -> CheckedType H A
  isNotType : IsNotType H A -> CheckedType H A

checkType : (H : TypeContext) -> (A : RawType) -> CheckedType H A
checkType H (var a) with checkTypeVar H a
checkType H (var a) | isTypeVar x = isType (var x)
checkType H (var a) | isNotTypeVar x = isNotType (not-var x)
checkType H (A => B) with checkType H A
checkType H (A => B) | isType pA with checkType H B
checkType H (A => B) | isType pA | isType pB = isType (pA => pB)
checkType H (A => B) | isType pA | isNotType npB = isNotType (not-=>-R pA npB)
checkType H (A => B) | isNotType npA = isNotType (not-=>-L npA)
checkType H (all A) with checkType (H ,type) A
checkType H (all A) | isType pA = isType (all pA)
checkType H (all A) | isNotType npA = isNotType (not-all npA)

extractRawType : forall {H} -> Type H -> RawType
extractRawType (var a) = var (extractRawTypeVar a)
extractRawType (A => B) = extractRawType A => extractRawType B
extractRawType (all A) = all (extractRawType A)

extractType : forall {H A} -> IsType H A -> Type H
extractType (var a) = var (extractTypeVar a)
extractType (A => B) = extractType A => extractType B
extractType (all A) = all (extractType A)

coherenceType : forall {H A} -> (P : IsType H A) -> extractRawType (extractType P) ≡ A
coherenceType (var a) rewrite coherenceTypeVar a = refl
coherenceType (A => B) rewrite coherenceType A | coherenceType B = refl
coherenceType (all A) rewrite coherenceType A = refl

checkTypeCorrect : forall {H A} -> (P : IsType H A) -> checkType H A ≡ isType P
checkTypeCorrect (var x) rewrite checkTypeVarCorrect x = refl
checkTypeCorrect (A => B) rewrite checkTypeCorrect A | checkTypeCorrect B = refl
checkTypeCorrect (all A) rewrite checkTypeCorrect A = refl

wkTypeRenaming : forall {H H'} -> (TypeVar H -> TypeVar H') -> TypeVar (H ,type) -> TypeVar (H' ,type)
wkTypeRenaming r here = here
wkTypeRenaming r (there v) = there (r v)

renType : forall {H H'} -> (TypeVar H -> TypeVar H') -> Type H -> Type H'
renType r (var x) = var (r x)
renType r (A => B) = renType r A => renType r B
renType r (all A) = all (renType (wkTypeRenaming r) A)

wkTypeEnv : forall {H H'} -> (TypeVar H -> Type H') -> TypeVar (H ,type) -> Type (H' ,type)
wkTypeEnv env here = var here
wkTypeEnv env (there v) = renType there (env v)

wkType : forall {H} -> Type H -> Type (H ,type)
wkType A = renType there A

subType : forall {H H'} -> (TypeVar H -> Type H') -> Type H -> Type H'
subType env (var x) = env x
subType env (A => B) = subType env A => subType env B
subType env (all A) = all (subType (wkTypeEnv env) A)

typeSubstitution : forall {H} -> Type H -> TypeVar (H ,type) -> Type H
typeSubstitution A here = A
typeSubstitution A (there v) = var v

substType : forall {H} -> Type H -> Type (H ,type) -> Type H
substType A B = subType (typeSubstitution A) B

data EqType {H} : Type H -> Type H -> Set where
  var : forall {a a'} -> EqTypeVar H a a' -> EqType (var a) (var a')
  _=>_ : forall {A A' B B'} -> EqType A A' -> EqType B B' -> EqType (A => B) (A' => B')
  all : forall {A A'} -> EqType A A' -> EqType (all A) (all A')

data NotEqType {H} : Type H -> Type H -> Set where
  var-var : forall {a a'} -> NotEqTypeVar H a a' -> NotEqType (var a) (var a')
  var-=> : forall {a A' B'} -> NotEqType (var a) (A' => B')
  var-all : forall {a A'} -> NotEqType (var a) (all A')
  =>-var : forall {A B a'} -> NotEqType (A => B) (var a')
  =>-=>-L : forall {A B A' B'} -> NotEqType A A' -> NotEqType (A => B) (A' => B')
  =>-=>-R : forall {A B A' B'} -> EqType A A' -> NotEqType B B' -> NotEqType (A => B) (A' => B')
  =>-all : forall {A B A'} -> NotEqType (A => B) (all A')
  all-var : forall {A a'} -> NotEqType (all A) (var a')
  all-=> : forall {A A' B'} -> NotEqType (all A) (A' => B')
  all-all : forall {A A'} -> NotEqType A A' -> NotEqType (all A) (all A')

data CheckEqType {H} (A B : Type H) : Set where
  eqType : EqType A B -> CheckEqType A B
  notEqType : NotEqType A B -> CheckEqType A B

checkEqType : forall {H} -> (A B : Type H) -> CheckEqType A B
checkEqType (var a) (var a') with checkEqTypeVar a a'
checkEqType (var a) (var a') | eqTypeVar p = eqType (var p)
checkEqType (var a) (var a') | notEqTypeVar np = notEqType (var-var np)
checkEqType (var a) (B => B') = notEqType var-=>
checkEqType (var a) (all B) = notEqType var-all
checkEqType (A => B) (var a') = notEqType =>-var
checkEqType (A => B) (A' => B') with checkEqType A A'
checkEqType (A => B) (A' => B') | eqType p with checkEqType B B'
checkEqType (A => B) (A' => B') | eqType p | eqType p' = eqType (p => p')
checkEqType (A => B) (A' => B') | eqType p | notEqType np' = notEqType (=>-=>-R p np')
checkEqType (A => B) (A' => B') | notEqType np = notEqType (=>-=>-L np)
checkEqType (A => B) (all B') = notEqType =>-all
checkEqType (all A) (var x) = notEqType all-var
checkEqType (all A) (A' => B') = notEqType all-=>
checkEqType (all A) (all A') with checkEqType A A'
checkEqType (all A) (all A') | eqType p = eqType (all p)
checkEqType (all A) (all A') | notEqType np = notEqType (all-all np)

checkEqTypeCorrect : forall {H} {A B : Type H} -> (P : EqType A B) -> checkEqType A B ≡ eqType P
checkEqTypeCorrect (var a) rewrite checkEqTypeVarCorrect a = refl
checkEqTypeCorrect (A => B) rewrite checkEqTypeCorrect A | checkEqTypeCorrect B = refl
checkEqTypeCorrect (all A) rewrite checkEqTypeCorrect A = refl

reflEqType : forall {H} {A : Type H} -> EqType A A
reflEqType {A = var x} = var reflEqTypeVar
reflEqType {A = A => B} = reflEqType => reflEqType
reflEqType {A = all A} = all reflEqType

data IsFunType {H} : Type H -> Type H -> Type H -> Set where
  _=>_ : (A B : Type H) -> IsFunType (A => B) A B

data IsNotFunType {H} : Type H -> Set where
  var : (a : TypeVar H) -> IsNotFunType (var a)
  all : (A : Type (H ,type)) -> IsNotFunType (all A)

data CheckFunType {H} (A : Type H) : Set where
  isFunType : forall {B C} -> IsFunType A B C -> CheckFunType A
  isNotFunType : IsNotFunType A -> CheckFunType A

checkFunType : forall {H} -> (A : Type H) -> CheckFunType A
checkFunType (var a) = isNotFunType (var a)
checkFunType (A => B) = isFunType (A => B)
checkFunType (all A) = isNotFunType (all A)

checkFunTypeCorrect : forall {H} {A B C : Type H} -> (P : IsFunType A B C) -> checkFunType A ≡ isFunType P
checkFunTypeCorrect (A => B) = refl

data IsAllType {H} : Type H -> Type (H ,type) -> Set where
  all : (A : Type (H ,type)) -> IsAllType (all A) A

data IsNotAllType {H} : Type H -> Set where
  var : (a : TypeVar H) -> IsNotAllType (var a)
  _=>_ : (A B : Type H) -> IsNotAllType (A => B)

data CheckAllType {H} (A : Type H) : Set where
  isAllType : forall {B} -> IsAllType A B -> CheckAllType A
  isNotAllType : IsNotAllType A -> CheckAllType A

checkAllType : forall {H} -> (A : Type H) -> CheckAllType A
checkAllType (var a) = isNotAllType (var a)
checkAllType (A => B) = isNotAllType (A => B)
checkAllType (all A) = isAllType (all A)

checkAllTypeCorrect : forall {H} {A : Type H} {B} -> (P : IsAllType A B) -> checkAllType A ≡ isAllType P
checkAllTypeCorrect (all A) = refl
  





mutual
  
  data TermContext : Set where
    [] : TermContext
    _,term_ : (G : TermContext) -> Type (stripTermContext G) -> TermContext
    _,type : TermContext -> TermContext
  
  stripTermContext : TermContext -> TypeContext
  stripTermContext [] = []
  stripTermContext (G ,term A) = stripTermContext G
  stripTermContext (G ,type) = stripTermContext G ,type





data RawTermVar : Set where
  here : RawTermVar
  there : RawTermVar -> RawTermVar

data TermVar : (G : TermContext) -> Type (stripTermContext G) -> Set where
  here : forall {G A} -> TermVar (G ,term A) A
  there : forall {G A B} -> TermVar G A -> TermVar (G ,term B) A
  skip-type : forall {G A} -> TermVar G A -> TermVar (G ,type) (wkType A)

data IsTermVar : (G : TermContext) -> RawTermVar -> Type (stripTermContext G) -> Set where
  here : forall {G A} -> IsTermVar (G ,term A) here A
  there : forall {G A B x} -> IsTermVar G x A -> IsTermVar (G ,term B) (there x) A
  skip-type : forall {G A x} -> IsTermVar G x A -> IsTermVar (G ,type) x (wkType A)

data IsNotTermVar : (G : TermContext) -> RawTermVar -> Set where
  not-var : forall {x} -> IsNotTermVar [] x
  not-there : forall {G B x} -> IsNotTermVar G x -> IsNotTermVar (G ,term B) (there x)
  not-skip-type : forall {G x} -> IsNotTermVar G x -> IsNotTermVar (G ,type) x

data SynthedTermVar (G : TermContext) (x : RawTermVar) : Set where
  isTermVar : forall {A} -> IsTermVar G x A -> SynthedTermVar G x
  isNotTermVar : IsNotTermVar G x -> SynthedTermVar G x

synthTermVar : (G : TermContext) -> (x : RawTermVar) -> SynthedTermVar G x
synthTermVar [] x = isNotTermVar not-var
synthTermVar (G ,term A) here = isTermVar here
synthTermVar (G ,term A) (there x) with synthTermVar G x
synthTermVar (G ,term A) (there x) | isTermVar px = isTermVar (there px)
synthTermVar (G ,term A) (there x) | isNotTermVar npx = isNotTermVar (not-there npx)
synthTermVar (G ,type) x with synthTermVar G x
synthTermVar (G ,type) x | isTermVar px = isTermVar (skip-type px)
synthTermVar (G ,type) x | isNotTermVar npx = isNotTermVar (not-skip-type npx)

extractRawTermVar : forall {G A} -> TermVar G A -> RawTermVar
extractRawTermVar here = here
extractRawTermVar (there x) = there (extractRawTermVar x)
extractRawTermVar (skip-type x) = extractRawTermVar x

extractTermVar : forall {G x A} -> IsTermVar G x A -> TermVar G A
extractTermVar here = here
extractTermVar (there x) = there (extractTermVar x)
extractTermVar (skip-type x) = skip-type (extractTermVar x)

coherenceTermVar : forall {G x A} -> (P : IsTermVar G x A) -> extractRawTermVar (extractTermVar P) ≡ x
coherenceTermVar here = refl
coherenceTermVar (there P) rewrite coherenceTermVar P = refl
coherenceTermVar (skip-type P) rewrite coherenceTermVar P = refl

synthTermVarCorrect : forall {G x A} -> (P : IsTermVar G x A) -> synthTermVar G x ≡ isTermVar P
synthTermVarCorrect here = refl
synthTermVarCorrect (there P) rewrite synthTermVarCorrect P = refl
synthTermVarCorrect (skip-type P) rewrite synthTermVarCorrect P = refl

extractTypeFromTermVar : forall {G A} -> TermVar G A -> Type (stripTermContext G)
extractTypeFromTermVar {G ,term A} here = A
extractTypeFromTermVar (there x) = extractTypeFromTermVar x
extractTypeFromTermVar (skip-type x) = wkType (extractTypeFromTermVar x)

extractTypeFromIsTermVar : forall {G x A} -> IsTermVar G x A -> Type (stripTermContext G)
extractTypeFromIsTermVar {G ,term A} here = A
extractTypeFromIsTermVar (there M) = extractTypeFromIsTermVar M
extractTypeFromIsTermVar (skip-type M) = wkType (extractTypeFromIsTermVar M)





data RawTerm : Set where
  var : RawTermVar -> RawTerm
  lam : RawType -> RawTerm -> RawTerm
  app : RawTerm -> RawTerm -> RawTerm
  abs : RawTerm -> RawTerm
  inst : RawTerm -> RawType -> RawTerm

data Term (G : TermContext) : Type (stripTermContext G) -> Set where
  var : forall {A} -> TermVar G A -> Term G A
  lam : forall {B} -> (A : Type (stripTermContext G)) -> (M : Term (G ,term A) B) -> Term G (A => B)
  app : {A B : Type (stripTermContext G)} -> (M : Term G) -> (N : Term G) -> Term G
  abs : (P : Term (G ,type)) -> Term G
  inst : forall {A} -> (P : Term G) -> (B : Type (stripTermContext G)) -> IsAllType (extractTypeFromTerm P) A -> Term G

{-
mutual
  data IsTerm (G : TermContext) : RawTerm -> Set where
    var : forall {x} -> IsTermVar G x -> IsTerm G (var x)
    lam : forall {A M} -> (P : IsType (stripTermContext G) A) -> IsTerm (G ,term (extractType P)) M -> IsTerm G (lam A M)
    app : forall {A B M N} -> (PM : IsTerm G M) -> (PN : IsTerm G N) -> (PFun : IsFunType (extractTypeFromIsTerm PM) A B) -> EqType (extractTypeFromIsTerm PN) A -> IsTerm G (app M N)
    abs : forall {M} -> IsTerm (G ,type) M -> IsTerm G (abs M)
    inst : forall {A M B} -> (PM : IsTerm G M) -> (PB : IsType (stripTermContext G) B) -> IsAllType (extractTypeFromIsTerm PM) A -> IsTerm G (inst M B)

  extractTypeFromIsTerm : forall {G M} -> IsTerm G M -> Type (stripTermContext G)
  extractTypeFromIsTerm (var x) = extractTypeFromIsTermVar x
  extractTypeFromIsTerm (lam A M) = extractType A => extractTypeFromIsTerm M
  extractTypeFromIsTerm (app {B = B} M N pFun pn) = B
  extractTypeFromIsTerm (abs M) = all (extractTypeFromIsTerm M)
  extractTypeFromIsTerm (inst {A = A} M B pAll) = substType (extractType B) A

data IsNotTerm (G : TermContext) : RawTerm -> Set where
  not-var : forall {x} -> IsNotTermVar G x -> IsNotTerm G (var x)
  not-lam-L : forall {A M} -> IsNotType (stripTermContext G) A -> IsNotTerm G (lam A M)
  not-lam-R : forall {A M} -> (P : IsType (stripTermContext G) A) -> IsNotTerm (G ,term extractType P) M -> IsNotTerm G (lam A M)
  not-app-L : forall {M N} -> IsNotTerm G M -> IsNotTerm G (app M N)
  not-app-R : forall {M N} -> IsTerm G M -> IsNotTerm G N -> IsNotTerm G (app M N)
  not-app-funtype : forall {M N} -> (P : IsTerm G M) -> IsTerm G N -> IsNotFunType (extractTypeFromIsTerm P) -> IsNotTerm G (app M N)
  not-app-argtype : forall {A B M N} -> (P : IsTerm G M) -> (P' : IsTerm G N) -> (PFun : IsFunType (extractTypeFromIsTerm P) A B) -> NotEqType (extractTypeFromIsTerm P') A -> IsNotTerm G (app M N)
  not-abs : forall {M} -> IsNotTerm (G ,type) M -> IsNotTerm G (abs M)
  not-inst-L : forall {M B} -> IsNotTerm G M -> IsNotTerm G (inst M B)
  not-inst-R : forall {M B} -> IsTerm G M -> IsNotType (stripTermContext G) B -> IsNotTerm G (inst M B)
  not-inst-alltype : forall {M B} -> (P : IsTerm G M) -> IsType (stripTermContext G) B -> IsNotAllType (extractTypeFromIsTerm P) -> IsNotTerm G (inst M B)
  
data TypeSynthesis (G : TermContext) (M : RawTerm) : Set where
  isTerm : IsTerm G M -> TypeSynthesis G M
  isNotTerm : IsNotTerm G M -> TypeSynthesis G M

synthTerm : (G : TermContext) -> (M : RawTerm) -> TypeSynthesis G M
synthTerm G (var x) with synthTermVar G x
synthTerm G (var x) | isTermVar p = isTerm (var p)
synthTerm G (var x) | isNotTermVar np = isNotTerm (not-var np)
synthTerm G (lam A M) with checkType (stripTermContext G) A
synthTerm G (lam A M) | isType pA with synthTerm (G ,term extractType pA) M
synthTerm G (lam A M) | isType pA | isTerm pM = isTerm (lam pA pM)
synthTerm G (lam A M) | isType pA | isNotTerm npM = isNotTerm (not-lam-R pA npM)
synthTerm G (lam A M) | isNotType npA = isNotTerm (not-lam-L npA)
synthTerm G (app M N) with synthTerm G M
synthTerm G (app M N) | isTerm pM with synthTerm G N
synthTerm G (app M N) | isTerm pM | isTerm pN with checkFunType (extractTypeFromIsTerm pM)
synthTerm G (app M N) | isTerm pM | isTerm pN | isFunType pFun with checkEqType (extractTypeFromIsTerm pN) _
synthTerm G (app M N) | isTerm pM | isTerm pN | isFunType pFun | eqType eq = isTerm (app pM pN pFun eq)
synthTerm G (app M N) | isTerm pM | isTerm pN | isFunType pFun | notEqType neq = isNotTerm (not-app-argtype pM pN pFun neq)
synthTerm G (app M N) | isTerm pM | isTerm pN | isNotFunType npFun = isNotTerm (not-app-funtype pM pN npFun)
synthTerm G (app M N) | isTerm pM | isNotTerm npN = isNotTerm (not-app-R pM npN)
synthTerm G (app M N) | isNotTerm npM = isNotTerm (not-app-L npM)
synthTerm G (abs M) with synthTerm (G ,type) M
synthTerm G (abs M) | isTerm p = isTerm (abs p)
synthTerm G (abs M) | isNotTerm np = isNotTerm (not-abs np)
synthTerm G (inst M B) with synthTerm G M
synthTerm G (inst M B) | isTerm p with checkType (stripTermContext G) B
synthTerm G (inst M B) | isTerm p | isType p' with checkAllType (extractTypeFromIsTerm p)
synthTerm G (inst M B) | isTerm p | isType p' | isAllType pAll = isTerm (inst p p' pAll)
synthTerm G (inst M B) | isTerm p | isType p' | isNotAllType npAll = isNotTerm (not-inst-alltype p p' npAll)
synthTerm G (inst M B) | isTerm p | isNotType np' = isNotTerm (not-inst-R p np')
synthTerm G (inst M B) | isNotTerm np = isNotTerm (not-inst-L np)

extractRawTerm : forall {G} -> Term G -> RawTerm
extractRawTerm (var x) = var (extractRawTermVar x)
extractRawTerm (lam A M) = lam (extractRawType A) (extractRawTerm M)
extractRawTerm (app M N _ _) = app (extractRawTerm M) (extractRawTerm N)
extractRawTerm (abs M) = abs (extractRawTerm M)
extractRawTerm (inst M B _) = inst (extractRawTerm M) (extractRawType B)

mutual
  
  extractTerm : forall {G M} -> IsTerm G M -> Term G
  extractTerm (var x) = var (extractTermVar x)
  extractTerm (lam A M) = lam (extractType A) (extractTerm M)
  extractTerm (app {A = A} {B = B} M N pFun pN) = app {A = A} {B = B}
                                                      (extractTerm M)
                                                      (extractTerm N)
                                                      (subst (\ T -> IsFunType T A B) (extractTermLemma M) pFun)
                                                      (subst (\ T -> EqType T A) (extractTermLemma N) pN)
  extractTerm (abs M) = abs (extractTerm M)
  extractTerm (inst {A = A} M B pM) = inst {A = A} (extractTerm M) (extractType B) (subst (\ T -> IsAllType T A) (extractTermLemma M) pM )

  extractVarLemma : forall {G x} -> (P : IsTermVar G x) -> extractTypeFromIsTermVar P ≡ extractTypeFromTermVar (extractTermVar P)
  extractVarLemma here = refl
  extractVarLemma (there x) rewrite extractVarLemma x = refl
  extractVarLemma (skip-type x) rewrite extractVarLemma x = refl
  
  extractTermLemma : forall {G M} -> (P : IsTerm G M) -> extractTypeFromIsTerm P ≡ extractTypeFromTerm (extractTerm P)
  extractTermLemma (var x) = extractVarLemma x
  extractTermLemma (lam A M) rewrite extractTermLemma M = refl
  extractTermLemma (app M N pFun pN) = refl
  extractTermLemma (abs M) rewrite extractTermLemma M = refl
  extractTermLemma (inst M B pAll) = refl

coherenceTerm : forall {G M} -> (P : IsTerm G M) -> extractRawTerm (extractTerm P) ≡ M
coherenceTerm (var x) rewrite coherenceTermVar x = refl
coherenceTerm (lam A M) rewrite coherenceType A | coherenceTerm M = refl
coherenceTerm (app M N _ _) rewrite coherenceTerm M | coherenceTerm N = refl
coherenceTerm (abs M) rewrite coherenceTerm M = refl
coherenceTerm (inst M B _) rewrite coherenceTerm M | coherenceType B = refl

synthTermCorrect : forall {G M} -> (P : IsTerm G M) -> synthTerm G M ≡ isTerm P
synthTermCorrect (var x) rewrite synthTermVarCorrect x = refl
synthTermCorrect (lam A M) rewrite checkTypeCorrect A | synthTermCorrect M = refl
synthTermCorrect {G} {app M N} (app P P' pM pN) with synthTerm G M | synthTermCorrect P
synthTermCorrect {G} {app M N} (app P P' pM pN) | isTerm .P | refl with synthTerm G N | synthTermCorrect P'
synthTermCorrect {G} {app M N} (app P P' pM pN) | isTerm .P | refl | isTerm .P' | refl with checkFunType (extractTypeFromIsTerm P) | checkFunTypeCorrect pM
synthTermCorrect {G} {app M N} (app {A = A} P P' pM pN) | isTerm .P | refl | isTerm .P' | refl | isFunType .pM | refl with checkEqType (extractTypeFromIsTerm P') A | checkEqTypeCorrect pN
synthTermCorrect {G} {app M N} (app P P' pM pN) | isTerm .P | refl | isTerm .P' | refl | isFunType .pM | refl | eqType .pN | refl = refl
synthTermCorrect {G} {app M N} (app P P' pM pN) | isTerm .P | refl | isTerm .P' | refl | isFunType .pM | refl | notEqType _ | ()
synthTermCorrect {G} {app M N} (app P P' pM pN) | isTerm .P | refl | isTerm .P' | refl | isNotFunType _ | ()
synthTermCorrect {G} {app M N} (app P P' pM pN) | isTerm .P | refl | isNotTerm x | ()
synthTermCorrect {G} {app M N} (app P P' pM pN) | isNotTerm _ | ()
synthTermCorrect (abs M) rewrite synthTermCorrect M = refl
synthTermCorrect {G} {inst M B} (inst P P' pM) with synthTerm G M | synthTermCorrect P
synthTermCorrect {G} {inst M B} (inst P P' pM) | isTerm .P | refl with checkType (stripTermContext G) B | checkTypeCorrect P'
synthTermCorrect {G} {inst M B} (inst P P' pM) | isTerm .P | refl | isType .P' | refl with checkAllType (extractTypeFromIsTerm P) | checkAllTypeCorrect pM
synthTermCorrect {G} {inst M B₁} (inst P P' pM) | isTerm .P | refl | isType .P' | refl | isAllType .pM | refl = refl
synthTermCorrect {G} {inst M B} (inst P P' pM) | isTerm .P | refl | isType .P' | refl | isNotAllType _ | ()
synthTermCorrect {G} {inst M B} (inst P P' pM) | isTerm .P | refl | isNotType _ | ()
synthTermCorrect {G} {inst M B} (inst P P' pM) | isNotTerm _ | ()
-}
