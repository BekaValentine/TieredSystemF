module TieredHigherKindedSystemF where

open import Relation.Binary.PropositionalEquality




data Kind : Set where
  * : Kind
  _=>_ : Kind -> Kind -> Kind

data EqKind : Kind -> Kind -> Set where
  * : EqKind * *
  _=>_ : forall {K J K' J'} -> EqKind K K' -> EqKind J J' -> EqKind (K => J) (K' => J')

data NotEqKind : Kind -> Kind -> Set where
  *-=> : forall {K' J'} -> NotEqKind * (K' => J')
  =>-* : forall {K J} -> NotEqKind (K => J) *
  =>-=>-L : forall {K J K' J'} -> NotEqKind K K' -> NotEqKind (K => J) (K' => J')
  =>-=>-R : forall {K J K' J'} -> EqKind K K' -> NotEqKind J J' -> NotEqKind (K => J) (K' => J')

data CheckEqKind (K K' : Kind) : Set where
  eqKind : EqKind K K' -> CheckEqKind K K'
  notEqKind : NotEqKind K K' -> CheckEqKind K K'

checkEqKind : (K K' : Kind) -> CheckEqKind K K'
checkEqKind * * = eqKind *
checkEqKind * (K' => J') = notEqKind *-=>
checkEqKind (K => J) * = notEqKind =>-*
checkEqKind (K => J) (K' => J') with checkEqKind K K'
checkEqKind (K => J) (K' => J') | eqKind p with checkEqKind J J'
checkEqKind (K => J) (K' => J') | eqKind p | eqKind p' = eqKind (p => p')
checkEqKind (K => J) (K' => J') | eqKind p | notEqKind np' = notEqKind (=>-=>-R p np')
checkEqKind (K => J) (K' => J') | notEqKind np = notEqKind (=>-=>-L np)

checkEqKindCorrect : forall {K K'} -> (P : EqKind K K') -> checkEqKind K K' ≡ eqKind P
checkEqKindCorrect * = refl
checkEqKindCorrect (K => J) rewrite checkEqKindCorrect K | checkEqKindCorrect J = refl

eqKindReflection : forall {K K'} -> EqKind K K' -> K ≡ K'
eqKindReflection * = refl
eqKindReflection (K => J) rewrite eqKindReflection K | eqKindReflection J = refl

reflEqKind : forall {K} -> EqKind K K
reflEqKind {*} = *
reflEqKind {K => J} = reflEqKind => reflEqKind

eqKindElim : forall {K K'} {P : Set} -> EqKind K K' -> NotEqKind K K' -> P
eqKindElim * ()
eqKindElim (p => p') (=>-=>-L np) = eqKindElim p np
eqKindElim (p => p') (=>-=>-R x np) = eqKindElim p' np

data IsFunKind : Kind -> Kind -> Kind -> Set where
  _=>_ : (K J : Kind) -> IsFunKind (K => J) K J

data IsNotFunKind : Kind -> Set where
  * : IsNotFunKind *

data CheckFunKind (K : Kind) : Set where
  isFunKind : forall {J L} -> IsFunKind K J L -> CheckFunKind K
  isNotFunKind : IsNotFunKind K -> CheckFunKind K

checkFunKind : (K : Kind) -> CheckFunKind K
checkFunKind * = isNotFunKind *
checkFunKind (K => J) = isFunKind (K => J)

checkFunKindCorrect : forall {K J L} -> (P : IsFunKind K J L) -> checkFunKind K ≡ isFunKind P
checkFunKindCorrect (K => J) = refl



data TypeContext : Set where
  [] : TypeContext
  _,type_ : TypeContext -> Kind -> TypeContext





data RawTypeVar : Set where
  here : RawTypeVar
  there : RawTypeVar -> RawTypeVar

data TypeVar : TypeContext -> Set where
  here : forall {H K} -> TypeVar (H ,type K)
  there : forall {H K} -> TypeVar H -> TypeVar (H ,type K)

data IsTypeVar : TypeContext -> RawTypeVar -> Set where
  here : forall {H K} -> IsTypeVar (H ,type K) here
  there : forall {H K a} -> IsTypeVar H a -> IsTypeVar (H ,type K) (there a)

data IsNotTypeVar : TypeContext -> RawTypeVar -> Set where
  not-var : forall {a} -> IsNotTypeVar [] a
  not-there : forall {H K a} -> IsNotTypeVar H a -> IsNotTypeVar (H ,type K) (there a)

data CheckedTypeVar (H : TypeContext) (a : RawTypeVar) : Set where
  isTypeVar : IsTypeVar H a -> CheckedTypeVar H a
  isNotTypeVar : IsNotTypeVar H a -> CheckedTypeVar H a

checkTypeVar : (H : TypeContext) -> (a : RawTypeVar) -> CheckedTypeVar H a
checkTypeVar [] a = isNotTypeVar not-var
checkTypeVar (H ,type K) here = isTypeVar here
checkTypeVar (H ,type K) (there a) with checkTypeVar H a
checkTypeVar (H ,type K) (there a) | isTypeVar p = isTypeVar (there p)
checkTypeVar (H ,type K) (there a) | isNotTypeVar np = isNotTypeVar (not-there np)

extractRawTypeVar : forall {H} -> TypeVar H -> RawTypeVar
extractRawTypeVar here = here
extractRawTypeVar (there a) = there (extractRawTypeVar a)

extractTypeVar : forall {H a} -> (P : IsTypeVar H a) -> TypeVar H
extractTypeVar here = here
extractTypeVar (there a) = there (extractTypeVar a)

extractKindFromTypeVar : forall {H} -> TypeVar H -> Kind
extractKindFromTypeVar (here {K = K}) = K
extractKindFromTypeVar (there a) = extractKindFromTypeVar a

extractKindFromIsTypeVar : forall {H a} -> IsTypeVar H a -> Kind
extractKindFromIsTypeVar (here {K = K}) = K
extractKindFromIsTypeVar (there a) = extractKindFromIsTypeVar a

extractKindTypeVarLemma : forall {H a} -> (P : IsTypeVar H a) -> extractKindFromIsTypeVar P ≡ extractKindFromTypeVar (extractTypeVar P)
extractKindTypeVarLemma here = refl
extractKindTypeVarLemma (there P) rewrite extractKindTypeVarLemma P = refl

coherenceTypeVar : forall {H a} -> (P : IsTypeVar H a) -> extractRawTypeVar (extractTypeVar P) ≡ a
coherenceTypeVar here = refl
coherenceTypeVar (there P) rewrite coherenceTypeVar P = refl

checkTypeVarCorrect : forall {H a} -> (P : IsTypeVar H a) -> checkTypeVar H a ≡ isTypeVar P
checkTypeVarCorrect here = refl
checkTypeVarCorrect (there P) rewrite checkTypeVarCorrect P = refl

data EqTypeVar : forall H -> TypeVar H -> TypeVar H -> Set where
  here : forall {H K} -> EqTypeVar (H ,type K) here here
  there : forall {H K a a'} -> EqTypeVar H a a' -> EqTypeVar (H ,type K) (there a) (there a')

data NotEqTypeVar : forall H -> TypeVar H -> TypeVar H -> Set where
  here-there : forall {H K a'} -> NotEqTypeVar (H ,type K) here (there a')
  there-here : forall {H K a} -> NotEqTypeVar (H ,type K) (there a) here
  there-there : forall {H K a a'} -> NotEqTypeVar H a a' -> NotEqTypeVar (H ,type K) (there a) (there a')

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
  all : Kind -> RawType -> RawType
  lam : Kind -> RawType -> RawType
  app : RawType -> RawType -> RawType

mutual
  
  data Type (H : TypeContext) : Set where
    var : TypeVar H -> Type H
    _=>_ : Type H -> Type H -> Type H
    all : (K : Kind) -> Type (H ,type K) -> Type H
    lam : (K : Kind) -> Type (H ,type K) -> Type H
    app : forall {K J} -> (A B : Type H) -> IsFunKind (extractKindFromType A) K J -> EqKind (extractKindFromType B) K -> Type H

  extractKindFromType : forall {H} -> Type H -> Kind
  extractKindFromType (var a) = extractKindFromTypeVar a
  extractKindFromType (A => B) = *
  extractKindFromType (all K A) = *
  extractKindFromType (lam K A) = K => extractKindFromType A
  extractKindFromType (app {J = J} A B pFun pB) = J

mutual

  data IsType (H : TypeContext) : RawType -> Set where
    var : forall {a} -> IsTypeVar H a -> IsType H (var a)
    _=>_ : forall {A B} -> IsType H A -> IsType H B -> IsType H (A => B)
    all : forall {A} -> (K : Kind) -> IsType (H ,type K) A -> IsType H (all K A)
    lam : forall {A} -> (K : Kind) -> IsType (H ,type K) A -> IsType H (lam K A)
    app : forall {A B K J} -> (P : IsType H A) -> (P' : IsType H B) -> IsFunKind (extractKindFromIsType P) K J -> EqKind (extractKindFromIsType P') K -> IsType H (app A B)

  extractKindFromIsType : forall {H A} -> IsType H A -> Kind
  extractKindFromIsType (var a) = extractKindFromIsTypeVar a
  extractKindFromIsType (A => B) = *
  extractKindFromIsType (all K A) = *
  extractKindFromIsType (lam K A) = K => extractKindFromIsType A
  extractKindFromIsType (app {J = J} A B _ _) = J

data IsNotType (H : TypeContext) : RawType -> Set where
  not-var : forall {a} -> IsNotTypeVar H a -> IsNotType H (var a)
  not-=>-L : forall {A B} -> IsNotType H A -> IsNotType H (A => B)
  not-=>-R : forall {A B} -> IsType H A -> IsNotType H B -> IsNotType H (A => B)
  not-all : forall {A} -> (K : Kind) -> IsNotType (H ,type K) A -> IsNotType H (all K A)
  not-lam : forall {A} -> (K : Kind) -> IsNotType (H ,type K) A -> IsNotType H (lam K A)
  not-app-L : forall {A B} -> IsNotType H A -> IsNotType H (app A B)
  not-app-R : forall {A B} -> IsType H A -> IsNotType H B -> IsNotType H (app A B)
  not-app-funkind : forall {A B} -> (P : IsType H A) -> IsType H B -> IsNotFunKind (extractKindFromIsType P) -> IsNotType H (app A B)
  not-app-eq : forall {A B K J} -> (P : IsType H A) -> (P' : IsType H B) -> IsFunKind (extractKindFromIsType P) K J -> NotEqKind (extractKindFromIsType P') K -> IsNotType H (app A B)

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
checkType H (all K A) with checkType (H ,type K) A
checkType H (all K A) | isType pA = isType (all K pA)
checkType H (all K A) | isNotType npA = isNotType (not-all K npA)
checkType H (lam K A) with checkType (H ,type K) A
checkType H (lam K A) | isType p = isType (lam K p)
checkType H (lam K A) | isNotType np = isNotType (not-lam K np)
checkType H (app A B) with checkType H A
checkType H (app A B) | isType p with checkType H B
checkType H (app A B) | isType p | isType p' with checkFunKind (extractKindFromIsType p)
checkType H (app A B) | isType p | isType p' | isFunKind fun with checkEqKind (extractKindFromIsType p') _
checkType H (app A B) | isType p | isType p' | isFunKind fun | eqKind eq = isType (app p p' fun eq)
checkType H (app A B) | isType p | isType p' | isFunKind fun | notEqKind neq = isNotType (not-app-eq p p' fun neq)
checkType H (app A B) | isType p | isType p' | isNotFunKind nfun = isNotType (not-app-funkind p p' nfun)
checkType H (app A B) | isType p | isNotType np' = isNotType (not-app-R p np')
checkType H (app A B) | isNotType np = isNotType (not-app-L np)

extractRawType : forall {H} -> Type H -> RawType
extractRawType (var a) = var (extractRawTypeVar a)
extractRawType (A => B) = extractRawType A => extractRawType B
extractRawType (all K A) = all K (extractRawType A)
extractRawType (lam K A) = lam K (extractRawType A)
extractRawType (app A B _ _) = app (extractRawType A) (extractRawType B)

mutual

  extractType : forall {H A} -> IsType H A -> Type H
  extractType (var a) = var (extractTypeVar a)
  extractType (A => B) = extractType A => extractType B
  extractType (all K A) = all K (extractType A)
  extractType (lam K A) = lam K (extractType A)
  extractType (app A B pFun pB) rewrite extractKindLemma A | extractKindLemma B = app (extractType A) (extractType B) pFun pB

  extractKindLemma : forall {H A} -> (P : IsType H A) -> extractKindFromIsType P ≡ extractKindFromType (extractType P)
  extractKindLemma (var a) = extractKindTypeVarLemma a
  extractKindLemma (A => B) rewrite extractKindLemma A | extractKindLemma B = refl
  extractKindLemma (all K A) rewrite extractKindLemma A = refl
  extractKindLemma (lam K A) rewrite extractKindLemma A = refl
  extractKindLemma (app A B pFun pB) rewrite extractKindLemma A | extractKindLemma B = refl

coherenceType : forall {H A} -> (P : IsType H A) -> extractRawType (extractType P) ≡ A
coherenceType (var a) rewrite coherenceTypeVar a = refl
coherenceType (A => B) rewrite coherenceType A | coherenceType B = refl
coherenceType (all K A) rewrite coherenceType A = refl
coherenceType (lam K A) rewrite coherenceType A = refl
coherenceType (app A B pFun pB) rewrite extractKindLemma A | extractKindLemma B | coherenceType A | coherenceType B = refl

checkTypeCorrect : forall {H A} -> (P : IsType H A) -> checkType H A ≡ isType P
checkTypeCorrect (var x) rewrite checkTypeVarCorrect x = refl
checkTypeCorrect (A => B) rewrite checkTypeCorrect A | checkTypeCorrect B = refl
checkTypeCorrect (all K A) rewrite checkTypeCorrect A = refl
checkTypeCorrect (lam K A) rewrite checkTypeCorrect A = refl
checkTypeCorrect (app A B pFun pB) rewrite checkTypeCorrect A | checkTypeCorrect B | checkFunKindCorrect pFun | checkEqKindCorrect pB = refl

record TypeVarRenaming (H H' : TypeContext) : Set where
  field
    rename : TypeVar H -> TypeVar H'
    kind-preserving : forall a -> extractKindFromTypeVar (rename a) ≡ extractKindFromTypeVar a

there-typevar-renaming : forall {H K} -> TypeVarRenaming H (H ,type K)
there-typevar-renaming {H} {K} = record { rename = there ; kind-preserving = \ _ -> refl }

wkTypeRenaming : forall {H H' K} -> TypeVarRenaming H H' -> TypeVarRenaming (H ,type K) (H' ,type K)
wkTypeRenaming {H} {H'} {K} r = record { rename = rename2 ; kind-preserving = kind-preserving2 }
  where
    rename2 : TypeVar (H ,type K) -> TypeVar (H' ,type K)
    rename2 here = here
    rename2 (there a) = there (TypeVarRenaming.rename r a)

    kind-preserving2 : forall a -> extractKindFromTypeVar (rename2 a) ≡ extractKindFromTypeVar a
    kind-preserving2 here = refl
    kind-preserving2 (there a) rewrite TypeVarRenaming.kind-preserving r a = refl

mutual
  renType : forall {H H'} -> (r : TypeVarRenaming H H') -> Type H -> Type H'
  renType r (var x) = var (TypeVarRenaming.rename r x)
  renType r (A => B) = renType r A => renType r B
  renType r (all K A) = all K (renType (wkTypeRenaming r) A)
  renType r (lam K A) = lam K (renType (wkTypeRenaming r) A)
  renType r (app {K = K} {J = J} A B pFun pB) rewrite sym (renTypePreserving r A) | sym (renTypePreserving r B) = app {K = K} {J = J} (renType r A) (renType r B) pFun pB

  renTypePreserving : forall {H H'} -> (r : TypeVarRenaming H H') -> (A : Type H) -> extractKindFromType (renType r A) ≡ extractKindFromType A
  renTypePreserving r (var a) = TypeVarRenaming.kind-preserving r a
  renTypePreserving r (A => B) = refl
  renTypePreserving r (all K A) = refl
  renTypePreserving r (lam K A) rewrite renTypePreserving (wkTypeRenaming r) A = refl
  renTypePreserving r (app A B pFun pB) rewrite sym (renTypePreserving r A) | sym (renTypePreserving r B) = refl

record TypeEnvironment (H H' : TypeContext) : Set where
  field
    substitute : TypeVar H -> Type H'
    kind-preserving : forall a -> extractKindFromType (substitute a) ≡ extractKindFromTypeVar a

wkTypeEnv : forall {H H' K} -> TypeEnvironment H H' -> TypeEnvironment (H ,type K) (H' ,type K)
wkTypeEnv {H} {H'} {K} env = record { substitute = substitute2 ; kind-preserving = kind-preserving2 }
  where
    substitute2 : TypeVar (H ,type K) -> Type (H' ,type K)
    substitute2 here = var here
    substitute2 (there v) = renType there-typevar-renaming (TypeEnvironment.substitute env v)

    kind-preserving2 : (a : TypeVar (H ,type K)) -> extractKindFromType (substitute2 a) ≡ extractKindFromTypeVar a
    kind-preserving2 here = refl
    kind-preserving2 (there a) = trans (renTypePreserving there-typevar-renaming (TypeEnvironment.substitute env a)) (TypeEnvironment.kind-preserving env a)

wkType : forall {H K} -> Type H -> Type (H ,type K)
wkType A = renType there-typevar-renaming A

mutual
  subType : forall {H H'} -> TypeEnvironment H H' -> Type H -> Type H'
  subType env (var x) = TypeEnvironment.substitute env x
  subType env (A => B) = subType env A => subType env B
  subType env (all K A) = all K (subType (wkTypeEnv env) A)
  subType env (lam K A) = lam K (subType (wkTypeEnv env) A)
  subType env (app {K = K} {J = J} A B pFun pB) rewrite sym (subTypePreserving env A) | sym (subTypePreserving env B) = app {K = K} {J = J} (subType env A) (subType env B) pFun pB

  subTypePreserving : forall {H H'} -> (env : TypeEnvironment H H') -> (A : Type H) -> extractKindFromType (subType env A) ≡ extractKindFromType A
  subTypePreserving env (var a) = TypeEnvironment.kind-preserving env a
  subTypePreserving env (A => B) = refl
  subTypePreserving env (all K A) = refl
  subTypePreserving env (lam K A) rewrite subTypePreserving (wkTypeEnv env) A = refl
  subTypePreserving env (app A B pFun pB) rewrite sym (subTypePreserving env A) | sym (subTypePreserving env B) = refl

typeSubstitution : forall {H K} -> (A : Type H) -> extractKindFromType A ≡ K -> TypeEnvironment (H ,type K) H
typeSubstitution {H} {K} A P = record { substitute = substitute2 ; kind-preserving = kind-preserving2 }
  where
    substitute2 : TypeVar (H ,type K) -> Type H
    substitute2 here = A
    substitute2 (there v) = var v

    kind-preserving2 : (a : TypeVar (H ,type K)) -> extractKindFromType (substitute2 a) ≡ extractKindFromTypeVar a
    kind-preserving2 here = P
    kind-preserving2 (there a) = refl

substType : forall {H K} -> (A : Type H) -> extractKindFromType A ≡ K -> Type (H ,type K) -> Type H
substType A P B = subType (typeSubstitution A P) B

data EqType {H} : Type H -> Type H -> Set where
  var : forall {a a'} -> EqTypeVar H a a' -> EqType (var a) (var a')
  _=>_ : forall {A A' B B'} -> EqType A A' -> EqType B B' -> EqType (A => B) (A' => B')
  all : (K : Kind) -> {A A' : Type (H ,type K)} -> EqType A A' -> EqType (all K A) (all K A')
  lam : (K : Kind) -> {A A' : Type (H ,type K)} -> EqType A A' -> EqType (lam K A) (lam K A')
  app : forall {K J A A' B B' pFun pFun' pB pB'} -> EqType A A' -> EqType B B' -> EqType (app {K = K} {J = J} A B pFun pB) (app {K = K} {J = J} A' B' pFun' pB')

eqTypeReflection : forall {H} {A A' : Type H} -> EqType A A' -> A ≡ A'
eqTypeReflection (var x) = {!!}
eqTypeReflection (A => B) rewrite eqTypeReflection A | eqTypeReflection B = refl
eqTypeReflection (all K A) rewrite eqTypeReflection A = refl
eqTypeReflection (lam K A) rewrite eqTypeReflection A = refl
eqTypeReflection {A = app _ _ pFun pB} {A' = app _ _ pFun' pB'} (app A B) rewrite eqTypeReflection A | eqTypeReflection B = {!!}

data NotEqType {H} : Type H -> Type H -> Set where
  var-var : forall {a a'} -> NotEqTypeVar H a a' -> NotEqType (var a) (var a')
  var-=> : forall {a A' B'} -> NotEqType (var a) (A' => B')
  var-all : forall {a K A'} -> NotEqType (var a) (all K A')
  var-lam : forall {a K' A'} -> NotEqType (var a) (lam K' A')
  var-app : forall {a K' J' A' B' pFun' pB'} -> NotEqType (var a) (app {K = K'} {J = J'} A' B' pFun' pB')
  =>-var : forall {A B a'} -> NotEqType (A => B) (var a')
  =>-=>-L : forall {A B A' B'} -> NotEqType A A' -> NotEqType (A => B) (A' => B')
  =>-=>-R : forall {A B A' B'} -> EqType A A' -> NotEqType B B' -> NotEqType (A => B) (A' => B')
  =>-all : forall {A B K A'} -> NotEqType (A => B) (all K A')
  =>-lam : forall {A B K' A'} -> NotEqType (A => B) (lam K' A')
  =>-app : forall {A B K' J' A' B' pFun' pB'} -> NotEqType (A => B) (app {K = K'} {J = J'} A' B' pFun' pB')
  all-var : forall {K A a'} -> NotEqType (all K A) (var a')
  all-=> : forall {K A A' B'} -> NotEqType (all K A) (A' => B')
  all-all-kind : forall {K K' A A'} -> NotEqKind K K' -> NotEqType (all K A) (all K' A')
  all-all-body : forall {K A A'} -> NotEqType A A' -> NotEqType (all K A) (all K A')
  all-lam : forall {K K' A A'} -> NotEqType (all K A) (lam K' A')
  all-app : forall {K A K' J' A' B' pFun' pB'} -> NotEqType (all K A) (app {K = K'} {J = J'} A' B' pFun' pB')
  lam-var : forall {K A a'} -> NotEqType (lam K A) (var a')
  lam-=> : forall {K A A' B'} -> NotEqType (lam K A) (A' => B')
  lam-all : forall {K A K' A'} -> NotEqType (lam K A) (all K' A')
  lam-lam-kind : forall {K A K' A'} -> NotEqKind K K' -> NotEqType (lam K A) (lam K' A')
  lam-lam-body : forall {K A A'} -> NotEqType A A' -> NotEqType (lam K A) (lam K A')
  lam-app :  forall {K A K' J' A' B' pFun' pB'} -> NotEqType (lam K A) (app {K = K'} {J = J'} A' B' pFun' pB')
  app-var : forall {K J A B pFun pB a'} -> NotEqType (app {K = K} {J = J} A B pFun pB) (var a')
  app-=> : forall {K J A B pFun pB A' B'} -> NotEqType (app {K = K} {J = J} A B pFun pB) (A' => B')
  app-all : forall {K J A B pFun pB K' A'} -> NotEqType (app {K = K} {J = J} A B pFun pB) (all K' A')
  app-lam : forall {K J A B pFun pB K' A'} -> NotEqType (app {K = K} {J = J} A B pFun pB) (lam K' A')
  app-app-L : forall {K J A B pFun pB K' J' A' B' pFun' pB'} -> NotEqType A A' -> NotEqType (app {K = K} {J = J} A B pFun pB) (app {K = K'} {J = J'} A' B' pFun' pB')
  app-app-R : forall {K J A B pFun pB K' J' A' B' pFun' pB'} -> EqType A A' -> NotEqType B B' -> NotEqType (app {K = K} {J = J} A B pFun pB) (app {K = K'} {J = J'} A' B' pFun' pB')
  
data CheckEqType {H} (A B : Type H) : Set where
  eqType : EqType A B -> CheckEqType A B
  notEqType : NotEqType A B -> CheckEqType A B

checkEqType : forall {H} -> (A B : Type H) -> CheckEqType A B
checkEqType (var a) (var a') with checkEqTypeVar a a'
checkEqType (var a) (var a') | eqTypeVar p = eqType (var p)
checkEqType (var a) (var a') | notEqTypeVar np = notEqType (var-var np)
checkEqType (var a) (B => B') = notEqType var-=>
checkEqType (var a) (all K' B) = notEqType var-all
checkEqType (var a) (lam K' B) = notEqType var-lam
checkEqType (var a) (app A' B' pFun' pB') = notEqType var-app
checkEqType (A => B) (var a') = notEqType =>-var
checkEqType (A => B) (A' => B') with checkEqType A A'
checkEqType (A => B) (A' => B') | eqType p with checkEqType B B'
checkEqType (A => B) (A' => B') | eqType p | eqType p' = eqType (p => p')
checkEqType (A => B) (A' => B') | eqType p | notEqType np' = notEqType (=>-=>-R p np')
checkEqType (A => B) (A' => B') | notEqType np = notEqType (=>-=>-L np)
checkEqType (A => B) (all K B') = notEqType =>-all
checkEqType (A => B) (lam K B') = notEqType =>-lam
checkEqType (A => B) (app A' B' pFun' pB') = notEqType =>-app
checkEqType (all K A) (var x) = notEqType all-var
checkEqType (all K A) (A' => B') = notEqType all-=>
checkEqType (all K A) (all K' A') with checkEqKind K K'
checkEqType (all K A) (all K' A') | eqKind p with eqKindReflection p
checkEqType (all K A) (all .K A') | eqKind p | refl with checkEqType A A'
checkEqType (all K A) (all .K A') | eqKind p | refl | eqType p' = eqType (all K p')
checkEqType (all K A) (all .K A') | eqKind p | refl | notEqType np' = notEqType (all-all-body np')
checkEqType (all K A) (all K' A') | notEqKind np = notEqType (all-all-kind np)
checkEqType (all K A) (lam K' A') = notEqType all-lam
checkEqType (all K A) (app A' B' pFun' pB') = notEqType all-app
checkEqType (lam K A) (var x) = notEqType lam-var
checkEqType (lam K A) (A' => B') = notEqType lam-=>
checkEqType (lam K A) (all K' A') = notEqType lam-all
checkEqType (lam K A) (lam K' A') with checkEqKind K K'
checkEqType (lam K A) (lam K' A') | eqKind p with eqKindReflection p
checkEqType (lam K A) (lam .K A') | eqKind p | refl with checkEqType A A'
checkEqType (lam K A) (lam .K A') | eqKind p | refl | eqType p' = eqType (lam K p')
checkEqType (lam K A) (lam .K A') | eqKind p | refl | notEqType np' = notEqType (lam-lam-body np')
checkEqType (lam K A) (lam K' A') | notEqKind np = notEqType (lam-lam-kind np)
checkEqType (lam K A) (app A' B' pFun' pB') = notEqType lam-app
checkEqType (app A B pFun pB) (var a') = notEqType app-var
checkEqType (app A B pFun pB) (A' => B') = notEqType app-=>
checkEqType (app A B pFun pB) (all K' A') = notEqType app-all
checkEqType (app A B pFun pB) (lam K' A') = notEqType app-lam
checkEqType (app A B pFun pB) (app A' B' pFun' pB') with checkEqType A A'
checkEqType (app A B pFun pB) (app A' B' pFun' pB') | eqType p with checkEqType B B'
checkEqType (app {K = K} A B pFun pB) (app {K = K'} A' B' pFun' pB') | eqType p | eqType p' = {!!}
checkEqType (app A B pFun pB) (app A' B' pFun' pB') | eqType p | notEqType np' = notEqType (app-app-R p np')
checkEqType (app A B pFun pB) (app A' B' pFun' pB') | notEqType np = notEqType (app-app-L np)
{-
checkEqTypeCorrect : forall {H} {A B : Type H} -> (P : EqType A B) -> checkEqType A B ≡ eqType P
checkEqTypeCorrect (var a) rewrite checkEqTypeVarCorrect a = refl
checkEqTypeCorrect (A => B) rewrite checkEqTypeCorrect A | checkEqTypeCorrect B = refl
checkEqTypeCorrect (all K A) rewrite checkEqKindCorrect (reflEqKind {K}) | eqKindReflection (reflEqKind {K}) | checkEqTypeCorrect A = refl
checkEqTypeCorrect (lam K A) rewrite checkEqKindCorrect (reflEqKind {K}) | eqKindReflection (reflEqKind {K}) | checkEqTypeCorrect A = refl

reflEqType : forall {H} {A : Type H} -> EqType A A
reflEqType {A = var x} = var reflEqTypeVar
reflEqType {A = A => B} = reflEqType => reflEqType
reflEqType {A = all K A} = all K reflEqType
reflEqType {A = lam K A} = lam K reflEqType

data IsFunType {H} : Type H -> Type H -> Type H -> Set where
  _=>_ : (A B : Type H) -> IsFunType (A => B) A B

data IsNotFunType {H} : Type H -> Set where
  var : (a : TypeVar H) -> IsNotFunType (var a)
  all : (K : Kind) -> (A : Type (H ,type K)) -> IsNotFunType (all K A)
  lam : (K : Kind) -> (A : Type (H ,type K)) -> IsNotFunType (lam K A)

data CheckFunType {H} (A : Type H) : Set where
  isFunType : forall {B C} -> IsFunType A B C -> CheckFunType A
  isNotFunType : IsNotFunType A -> CheckFunType A

checkFunType : forall {H} -> (A : Type H) -> CheckFunType A
checkFunType (var a) = isNotFunType (var a)
checkFunType (A => B) = isFunType (A => B)
checkFunType (all K A) = isNotFunType (all K A)
checkFunType (lam K A) = isNotFunType (lam K A)

checkFunTypeCorrect : forall {H} {A B C : Type H} -> (P : IsFunType A B C) -> checkFunType A ≡ isFunType P
checkFunTypeCorrect (A => B) = refl

data IsAllType {H} : Type H -> (K : Kind) -> Type (H ,type K) -> Set where
  all : (K : Kind) -> (A : Type (H ,type K)) -> IsAllType (all K A) K A

data IsNotAllType {H} : Type H -> Set where
  var : (a : TypeVar H) -> IsNotAllType (var a)
  _=>_ : (A B : Type H) -> IsNotAllType (A => B)
  lam : (K : Kind) -> (A : Type (H ,type K)) -> IsNotAllType (lam K A)

data CheckAllType {H} (A : Type H) : Set where
  isAllType : forall {K B} -> IsAllType A K B -> CheckAllType A
  isNotAllType : IsNotAllType A -> CheckAllType A

checkAllType : forall {H} -> (A : Type H) -> CheckAllType A
checkAllType (var a) = isNotAllType (var a)
checkAllType (A => B) = isNotAllType (A => B)
checkAllType (all K A) = isAllType (all K A)
checkAllType (lam K A) = isNotAllType (lam K A)

checkAllTypeCorrect : forall {H} {A : Type H} {K B} -> (P : IsAllType A K B) -> checkAllType A ≡ isAllType P
checkAllTypeCorrect (all K A) = refl

normalizeType : forall {H} -> (A : Type H) -> Type H
normalizeType (var a) = var a
normalizeType (A => B) = normalizeType A => normalizeType B
normalizeType (all K A) = all K (normalizeType A)
normalizeType (lam K A) = lam K (normalizeType A)






mutual
  
  data TermContext : Set where
    [] : TermContext
    _,term_ : (G : TermContext) -> Type (stripTermContext G) -> TermContext
    _,type_ : TermContext -> Kind -> TermContext
  
  stripTermContext : TermContext -> TypeContext
  stripTermContext [] = []
  stripTermContext (G ,term A) = stripTermContext G
  stripTermContext (G ,type K) = stripTermContext G ,type K





data RawTermVar : Set where
  here : RawTermVar
  there : RawTermVar -> RawTermVar

data TermVar : (G : TermContext) -> Set where
  here : forall {G A} -> TermVar (G ,term A)
  there : forall {G B} -> TermVar G -> TermVar (G ,term B)
  skip-type : forall {G K} -> TermVar G -> TermVar (G ,type K)
  
data IsTermVar : (G : TermContext) -> RawTermVar -> Set where
  here : forall {G A} -> IsTermVar (G ,term A) here
  there : forall {G B x} -> IsTermVar G x -> IsTermVar (G ,term B) (there x)
  skip-type : forall {G K x} -> IsTermVar G x -> IsTermVar (G ,type K) x

data IsNotTermVar : (G : TermContext) -> RawTermVar -> Set where
  not-var : forall {x} -> IsNotTermVar [] x
  not-there : forall {G B x} -> IsNotTermVar G x -> IsNotTermVar (G ,term B) (there x)
  not-skip-type : forall {G K x} -> IsNotTermVar G x -> IsNotTermVar (G ,type K) x

data SynthedTermVar (G : TermContext) (x : RawTermVar) : Set where
  isTermVar : IsTermVar G x -> SynthedTermVar G x
  isNotTermVar : IsNotTermVar G x -> SynthedTermVar G x

synthTermVar : (G : TermContext) -> (x : RawTermVar) -> SynthedTermVar G x
synthTermVar [] x = isNotTermVar not-var
synthTermVar (G ,term A) here = isTermVar here
synthTermVar (G ,term A) (there x) with synthTermVar G x
synthTermVar (G ,term A) (there x) | isTermVar px = isTermVar (there px)
synthTermVar (G ,term A) (there x) | isNotTermVar npx = isNotTermVar (not-there npx)
synthTermVar (G ,type K) x with synthTermVar G x
synthTermVar (G ,type K) x | isTermVar px = isTermVar (skip-type px)
synthTermVar (G ,type K) x | isNotTermVar npx = isNotTermVar (not-skip-type npx)

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
  abs : Kind -> RawTerm -> RawTerm
  inst : RawTerm -> RawType -> RawTerm

mutual

  data Term (G : TermContext) : Set where
    var : TermVar G -> Term G
    lam : (A : Type (stripTermContext G)) -> (M : Term (G ,term A)) -> Term G
    app : {A B : Type (stripTermContext G)} -> (M : Term G) -> (N : Term G) -> (PFun : IsFunType (extractTypeFromTerm M) A B) -> EqType (extractTypeFromTerm N) A -> Term G
    abs : (K : Kind) -> (P : Term (G ,type K)) -> Term G
    inst : forall {K A} -> (P : Term G) -> (B : Type (stripTermContext G)) -> IsAllType (extractTypeFromTerm P) K A -> EqKind (extractKindFromType B) K -> Term G

  extractTypeFromTerm : forall {G} -> Term G -> Type (stripTermContext G)
  extractTypeFromTerm (var x) = extractTypeFromTermVar x
  extractTypeFromTerm (lam A M) = A => extractTypeFromTerm M
  extractTypeFromTerm (app {B = B} M N pFun pN) = B
  extractTypeFromTerm (abs K M) = all K (extractTypeFromTerm M)
  extractTypeFromTerm (inst {A = A} M B pAll pB) = substType B A

mutual
  data IsTerm (G : TermContext) : RawTerm -> Set where
    var : forall {x} -> IsTermVar G x -> IsTerm G (var x)
    lam : forall {A M} -> (P : IsType (stripTermContext G) A) -> IsTerm (G ,term (extractType P)) M -> IsTerm G (lam A M)
    app : forall {A B M N} -> (PM : IsTerm G M) -> (PN : IsTerm G N) -> (PFun : IsFunType (extractTypeFromIsTerm PM) A B) -> EqType (extractTypeFromIsTerm PN) A -> IsTerm G (app M N)
    abs : forall {M} -> (K : Kind) -> IsTerm (G ,type K) M -> IsTerm G (abs K M)
    inst : forall {K A M B} -> (PM : IsTerm G M) -> (PB : IsType (stripTermContext G) B) -> IsAllType (extractTypeFromIsTerm PM) K A -> EqKind (extractKindFromIsType PB) K -> IsTerm G (inst M B)

  extractTypeFromIsTerm : forall {G M} -> IsTerm G M -> Type (stripTermContext G)
  extractTypeFromIsTerm (var x) = extractTypeFromIsTermVar x
  extractTypeFromIsTerm (lam A M) = extractType A => extractTypeFromIsTerm M
  extractTypeFromIsTerm (app {B = B} M N pFun pn) = B
  extractTypeFromIsTerm (abs K M) = all K (extractTypeFromIsTerm M)
  extractTypeFromIsTerm (inst {A = A} M B pAll pB) = substType (extractType B) A

data IsNotTerm (G : TermContext) : RawTerm -> Set where
  not-var : forall {x} -> IsNotTermVar G x -> IsNotTerm G (var x)
  not-lam-L : forall {A M} -> IsNotType (stripTermContext G) A -> IsNotTerm G (lam A M)
  not-lam-R : forall {A M} -> (P : IsType (stripTermContext G) A) -> IsNotTerm (G ,term extractType P) M -> IsNotTerm G (lam A M)
  not-app-L : forall {M N} -> IsNotTerm G M -> IsNotTerm G (app M N)
  not-app-R : forall {M N} -> IsTerm G M -> IsNotTerm G N -> IsNotTerm G (app M N)
  not-app-funtype : forall {M N} -> (P : IsTerm G M) -> IsTerm G N -> IsNotFunType (extractTypeFromIsTerm P) -> IsNotTerm G (app M N)
  not-app-argtype : forall {A B M N} -> (P : IsTerm G M) -> (P' : IsTerm G N) -> (PFun : IsFunType (extractTypeFromIsTerm P) A B) -> NotEqType (extractTypeFromIsTerm P') A -> IsNotTerm G (app M N)
  not-abs : forall {K M} -> IsNotTerm (G ,type K) M -> IsNotTerm G (abs K M)
  not-inst-L : forall {M B} -> IsNotTerm G M -> IsNotTerm G (inst M B)
  not-inst-R : forall {M B} -> IsTerm G M -> IsNotType (stripTermContext G) B -> IsNotTerm G (inst M B)
  not-inst-alltype : forall {M B} -> (P : IsTerm G M) -> IsType (stripTermContext G) B -> IsNotAllType (extractTypeFromIsTerm P) -> IsNotTerm G (inst M B)
  not-inst-eq : forall {M B K A} -> (P : IsTerm G M) -> (PB : IsType (stripTermContext G) B) -> IsAllType (extractTypeFromIsTerm P) K A -> NotEqKind (extractKindFromIsType PB) K -> IsNotTerm G (inst M B)

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
synthTerm G (abs K M) with synthTerm (G ,type K) M
synthTerm G (abs K M) | isTerm p = isTerm (abs K p)
synthTerm G (abs K M) | isNotTerm np = isNotTerm (not-abs np)
synthTerm G (inst M B) with synthTerm G M
synthTerm G (inst M B) | isTerm p with checkType (stripTermContext G) B
synthTerm G (inst M B) | isTerm p | isType p' with checkAllType (extractTypeFromIsTerm p)
synthTerm G (inst M B) | isTerm p | isType p' | isAllType {K = K} pAll with checkEqKind (extractKindFromIsType p') K
synthTerm G (inst M B) | isTerm p | isType p' | isAllType pAll | eqKind pB = isTerm (inst p p' pAll pB)
synthTerm G (inst M B) | isTerm p | isType p' | isAllType pAll | notEqKind npB = isNotTerm (not-inst-eq p p' pAll npB)
synthTerm G (inst M B) | isTerm p | isType p' | isNotAllType npAll = isNotTerm (not-inst-alltype p p' npAll)
synthTerm G (inst M B) | isTerm p | isNotType np' = isNotTerm (not-inst-R p np')
synthTerm G (inst M B) | isNotTerm np = isNotTerm (not-inst-L np)

extractRawTerm : forall {G} -> Term G -> RawTerm
extractRawTerm (var x) = var (extractRawTermVar x)
extractRawTerm (lam A M) = lam (extractRawType A) (extractRawTerm M)
extractRawTerm (app M N _ _) = app (extractRawTerm M) (extractRawTerm N)
extractRawTerm (abs K M) = abs K (extractRawTerm M)
extractRawTerm (inst M B _ _) = inst (extractRawTerm M) (extractRawType B)

mutual
  
  extractTerm : forall {G M} -> IsTerm G M -> Term G
  extractTerm (var x) = var (extractTermVar x)
  extractTerm (lam A M) = lam (extractType A) (extractTerm M)
  extractTerm (app {A = A} {B = B} M N pFun pN) = app {A = A} {B = B}
                                                      (extractTerm M)
                                                      (extractTerm N)
                                                      (subst (\ T -> IsFunType T A B) (extractTermLemma M) pFun)
                                                      (subst (\ T -> EqType T A) (extractTermLemma N) pN)
  extractTerm (abs K M) = abs K (extractTerm M)
  extractTerm (inst {K = K} {A = A} M B pM pB) = inst {A = A}
                                                      (extractTerm M)
                                                      (extractType B)
                                                      (subst (\ T -> IsAllType T K A) (extractTermLemma M) pM)
                                                      (subst (\ K' -> EqKind K' K) (extractKindLemma B) pB)

  extractVarLemma : forall {G x} -> (P : IsTermVar G x) -> extractTypeFromIsTermVar P ≡ extractTypeFromTermVar (extractTermVar P)
  extractVarLemma here = refl
  extractVarLemma (there x) rewrite extractVarLemma x = refl
  extractVarLemma (skip-type x) rewrite extractVarLemma x = refl
  
  extractTermLemma : forall {G M} -> (P : IsTerm G M) -> extractTypeFromIsTerm P ≡ extractTypeFromTerm (extractTerm P)
  extractTermLemma (var x) = extractVarLemma x
  extractTermLemma (lam A M) rewrite extractTermLemma M = refl
  extractTermLemma (app M N pFun pN) = refl
  extractTermLemma (abs K M) rewrite extractTermLemma M = refl
  extractTermLemma (inst M B pAll pB) = refl

coherenceTerm : forall {G M} -> (P : IsTerm G M) -> extractRawTerm (extractTerm P) ≡ M
coherenceTerm (var x) rewrite coherenceTermVar x = refl
coherenceTerm (lam A M) rewrite coherenceType A | coherenceTerm M = refl
coherenceTerm (app M N _ _) rewrite coherenceTerm M | coherenceTerm N = refl
coherenceTerm (abs K M) rewrite coherenceTerm M = refl
coherenceTerm (inst M B _ _) rewrite coherenceTerm M | coherenceType B = refl

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
synthTermCorrect (abs K M) rewrite synthTermCorrect M = refl
synthTermCorrect {G} {inst M B} (inst P P' pM pB) with synthTerm G M | synthTermCorrect P
synthTermCorrect {G} {inst M B} (inst P P' pM pB) | isTerm .P | refl with checkType (stripTermContext G) B | checkTypeCorrect P'
synthTermCorrect {G} {inst M B} (inst P P' pM pB) | isTerm .P | refl | isType .P' | refl with checkAllType (extractTypeFromIsTerm P) | checkAllTypeCorrect pM
synthTermCorrect {G} {inst M B} (inst {K = K} P P' pM pB) | isTerm .P | refl | isType .P' | refl | isAllType .pM | refl with checkEqKind (extractKindFromIsType P') K | checkEqKindCorrect pB
synthTermCorrect {G} {inst M B} (inst P P' pM pB) | isTerm .P | refl | isType .P' | refl | isAllType .pM | refl | eqKind .pB | refl = refl
synthTermCorrect {G} {inst M B} (inst P P' pM pB) | isTerm .P | refl | isType .P' | refl | isAllType .pM | refl | notEqKind _ | ()
synthTermCorrect {G} {inst M B} (inst P P' pM pB) | isTerm .P | refl | isType .P' | refl | isNotAllType _ | ()
synthTermCorrect {G} {inst M B} (inst P P' pM pB) | isTerm .P | refl | isNotType _ | ()
synthTermCorrect {G} {inst M B} (inst P P' pM pB) | isNotTerm _ | ()

-- -}
