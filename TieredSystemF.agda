module TieredSystemF where

open import Relation.Binary.PropositionalEquality




data RawTypeContext : Set where
  [] : RawTypeContext
  _,type : RawTypeContext -> RawTypeContext

data TypeContext : Set where
  [] : TypeContext
  _,type : TypeContext -> TypeContext

data IsTypeContext : RawTypeContext -> Set where
  [] : IsTypeContext []
  _,type : forall {H} -> IsTypeContext H -> IsTypeContext (H ,type)

checkTypeContext : (H : RawTypeContext) -> IsTypeContext H
checkTypeContext [] = []
checkTypeContext (H ,type) = checkTypeContext H ,type

extractRawTypeContext : TypeContext -> RawTypeContext
extractRawTypeContext [] = []
extractRawTypeContext (H ,type) = extractRawTypeContext H ,type

extractTypeContext : forall {H} -> IsTypeContext H -> TypeContext
extractTypeContext [] = []
extractTypeContext (H ,type) = extractTypeContext H ,type

coherenceTypeContext : forall {H} -> (P : IsTypeContext H) -> extractRawTypeContext (extractTypeContext P) ≡ H
coherenceTypeContext [] = refl
coherenceTypeContext (P ,type) rewrite coherenceTypeContext P = refl

checkTypeContextCorrect : forall {H} -> (P : IsTypeContext H) -> checkTypeContext H ≡ P
checkTypeContextCorrect [] = refl
checkTypeContextCorrect (P ,type) rewrite checkTypeContextCorrect P = refl





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
  _=>_ : forall {A A' B B'} -> EqType A A' -> EqType B B' -> EqType (A => B) (A' => B)
  all : forall {A A'} -> EqType A A' -> EqType (all A) (all A')

data NotEqType {H} : Type H -> Type H -> Set where
  var-var : forall {a a'} -> NotEqTypeVar H a a' -> NotEqType (var a) (var a')
  var-=> : forall {a A' B'} -> NotEqType (var a) (A' => B')
  var-all : forall {a A'} -> NotEqType (var a) (all A')
  =>-var : forall {A B a'} -> NotEqType (A => B) (var a')
  =>-=>-L : forall {A B A' B'} -> NotEqType A A' -> NotEqType (A => B) (A' => B')
  =>-=>-R : forall {A B A' B'} -> EqType A A' -> NotEqType B B' -> NotEqType (A => B) (A' => B)
  all-var : forall {A a'} -> NotEqType (all A) (var a')
  all-=> : forall {A A' B'} -> NotEqType (all A) (A' => B')
  all-all : forall {A A'} -> NotEqType A A' -> NotEqType (all A) (all A')





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

data TermVar : (G : TermContext) -> Set where
  here : forall {G A} -> TermVar (G ,term A)
  there : forall {G B} -> TermVar G -> TermVar (G ,term B)
  skip-type : forall {G} -> TermVar G -> TermVar (G ,type)
  
data IsTermVar : (G : TermContext) -> RawTermVar -> Set where
  here : forall {G A} -> IsTermVar (G ,term A) here
  there : forall {G B x} -> IsTermVar G x -> IsTermVar (G ,term B) (there x)
  skip-type : forall {G x} -> IsTermVar G x -> IsTermVar (G ,type) x

data IsNotTermVar : (G : TermContext) -> RawTermVar -> Set where
  not-var : forall {x} -> IsNotTermVar [] x
  not-there : forall {G B x} -> IsNotTermVar G x -> IsNotTermVar (G ,term B) (there x)
  not-skip-type : forall {G x} -> IsNotTermVar G x -> IsNotTermVar (G ,type) x

data SynthedTermVar (G : TermContext) (x : RawTermVar) : Set where
  isTermVar : IsTermVar G x -> SynthedTermVar G x
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

extractRawTermVar : forall {G} -> TermVar G -> RawTermVar
extractRawTermVar here = here
extractRawTermVar (there x) = there (extractRawTermVar x)
extractRawTermVar (skip-type x) = extractRawTermVar x

extractTermVar : forall {G x} -> IsTermVar G x -> TermVar G
extractTermVar here = here
extractTermVar (there x) = there (extractTermVar x)
extractTermVar (skip-type x) = skip-type (extractTermVar x)

coherenceTermVar : forall {G x} -> (P : IsTermVar G x) -> extractRawTermVar (extractTermVar P) ≡ x
coherenceTermVar here = refl
coherenceTermVar (there P) rewrite coherenceTermVar P = refl
coherenceTermVar (skip-type P) rewrite coherenceTermVar P = refl

synthTermVarCorrect : forall {G x} -> (P : IsTermVar G x) -> synthTermVar G x ≡ isTermVar P
synthTermVarCorrect here = refl
synthTermVarCorrect (there P) rewrite synthTermVarCorrect P = refl
synthTermVarCorrect (skip-type P) rewrite synthTermVarCorrect P = refl

extractTypeFromTermVar : forall {G} -> TermVar G -> Type (stripTermContext G)
extractTypeFromTermVar {G ,term A} here = A
extractTypeFromTermVar (there x) = extractTypeFromTermVar x
extractTypeFromTermVar (skip-type x) = wkType (extractTypeFromTermVar x)

extractTypeFromIsTermVar : forall {G x} -> IsTermVar G x -> Type (stripTermContext G)
extractTypeFromIsTermVar {G ,term A} here = A
extractTypeFromIsTermVar (there M) = extractTypeFromIsTermVar M
extractTypeFromIsTermVar (skip-type M) = wkType (extractTypeFromIsTermVar M)





data RawTerm : Set where
  var : RawTermVar -> RawTerm
  lam : RawType -> RawTerm -> RawTerm
  app : RawTerm -> RawTerm -> RawTerm
  abs : RawTerm -> RawTerm
  inst : RawTerm -> RawType -> RawTerm

mutual

  data Term (G : TermContext) : Set where
    var : TermVar G -> Term G
    lam : (A : Type (stripTermContext G)) -> (M : Term (G ,term A)) -> Term G
    app : {A B : Type (stripTermContext G)} -> (M : Term G) -> (N : Term G) -> EqType (extractTypeFromTerm M) (A => B) -> EqType (extractTypeFromTerm N) A -> Term G
    abs : (P : Term (G ,type)) -> Term G
    inst : forall {A} -> (P : Term G) -> (B : Type (stripTermContext G)) -> EqType (extractTypeFromTerm P) (all A) -> Term G

  extractTypeFromTerm : forall {G} -> Term G -> Type (stripTermContext G)
  extractTypeFromTerm (var x) = extractTypeFromTermVar x
  extractTypeFromTerm (lam A M) = A => extractTypeFromTerm M
  extractTypeFromTerm (app M N pM pN) with extractTypeFromTerm M
  extractTypeFromTerm (app M N (pA => pB) pN) | A => B = B
  extractTypeFromTerm (abs M) = all (extractTypeFromTerm M)
  extractTypeFromTerm (inst M B pM) with extractTypeFromTerm M
  extractTypeFromTerm (inst M B (all pA)) | all A = substType B A

mutual
  data IsTerm (G : TermContext) : RawTerm -> Set where
    var : forall {x} -> IsTermVar G x -> IsTerm G (var x)
    lam : forall {A M } -> (P : IsType (stripTermContext G) A) -> IsTerm (G ,term (extractType P)) M -> IsTerm G (lam A M)
    app : forall {M N A B} -> (PM : IsTerm G M) -> (PN : IsTerm G N) -> EqType (extractTypeFromIsTerm PM) (A => B) -> EqType (extractTypeFromIsTerm PN) A -> IsTerm G (app M N)
    abs : forall {M} -> IsTerm (G ,type) M -> IsTerm G (abs M)
    inst : forall {M A B} -> (PM : IsTerm G M) -> (PB : IsType (stripTermContext G) B) -> EqType (extractTypeFromIsTerm PM) (all A) -> IsTerm G (inst M B)

  extractTypeFromIsTerm : forall {G M} -> IsTerm G M -> Type (stripTermContext G)
  extractTypeFromIsTerm (var x) = extractTypeFromIsTermVar x
  extractTypeFromIsTerm (lam A M) = extractType A => extractTypeFromIsTerm M
  extractTypeFromIsTerm (app M N pM Pn) with extractTypeFromIsTerm M
  extractTypeFromIsTerm (app M N (pA => pB) Pn) | A => B = B
  extractTypeFromIsTerm (abs M) = all (extractTypeFromIsTerm M)
  extractTypeFromIsTerm (inst M B pM) with extractTypeFromIsTerm M
  extractTypeFromIsTerm (inst M B (all pA)) | all A = substType (extractType B) A



{-
data IsNotTerm (G : TermContext) : RawTerm -> Set where
--  app-L : forall {M N} -> 
-}
{-
data TypeSynthesis (G : TermContext) (M : RawTerm) : Set where
  isTerm : (A : Type (stripTermContext G)) -> IsTerm G M A -> TypeSynthesis G M
  isNotTerm : IsNotTerm G M -> TypeSynthesis G M

eqType : forall {H} -> (A B : Type H) -> Dec (A ≡ B)
eqType A B = {!!}

synthTerm : (G : TermContext) -> (M : RawTerm) -> TypeSynthesis G M
synthTerm G (var x) = {!!}
synthTerm G (lam A M) with checkType (stripTermContext G) A
... | d = {!!}
synthTerm G (app M N) with synthTerm G M
synthTerm G (app M N) | isTerm A p = {!!}
synthTerm G (app M N) | isNotTerm np = {!!}
synthTerm G (abs M) = {!!}
synthTerm G (inst M B) = {!!}

extractRawTerm : forall {G A} -> Term G A -> RawTerm
extractRawTerm (var x) = var (extractRawTermVar x)
extractRawTerm (lam A M) = lam (extractRawType A) (extractRawTerm M)
extractRawTerm (app M N) = app (extractRawTerm M) (extractRawTerm N)
extractRawTerm (abs M) = abs (extractRawTerm M)
extractRawTerm (inst M B) = inst (extractRawTerm M) (extractRawType B)

extractTerm : forall {G M A} -> IsTerm G M A -> Term G A
extractTerm (var x) = var (extractTermVar x)
extractTerm (lam A M) = lam (extractType A) (extractTerm M)
extractTerm (app M N) = app (extractTerm M) (extractTerm N)
extractTerm (abs M) = abs (extractTerm M)
extractTerm (inst M B) = inst (extractTerm M) (extractType B)

coherenceTerm : forall {G M A} -> (P : IsTerm G M A) -> extractRawTerm (extractTerm P) ≡ M
coherenceTerm (var x) rewrite coherenceTermVar x = refl
coherenceTerm (lam A M) rewrite coherenceType A | coherenceTerm M = refl
coherenceTerm (app M N) rewrite coherenceTerm M | coherenceTerm N = refl
coherenceTerm (abs M) rewrite coherenceTerm M = refl
coherenceTerm (inst M B) rewrite coherenceTerm M | coherenceType B = refl

checkCorrect : forall {G M A} -> (P : IsTerm G M A) -> synthTerm G M ≡ isTerm A P
checkCorrect P = {!!}
-}