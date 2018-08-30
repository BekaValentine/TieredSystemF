module TieredSTLC where




data Type : Set where
  Bool : Type
  _*_ _+_ _=>_ : Type -> Type -> Type

data EqType : Type -> Type -> Set where
  Bool : EqType Bool Bool
  _*_ : forall {A A' B B'} -> EqType A A' -> EqType B B' -> EqType (A * B) (A' * B')
  _+_ : forall {A A' B B'} -> EqType A A' -> EqType B B' -> EqType (A + B) (A' + B')
  _=>_ : forall {A A' B B'} -> EqType A A' -> EqType B B' -> EqType (A => B) (A' => B')


  


data TermContext : Set where
  [] : TermContext
  _,_ : TermContext -> Type -> TermContext





data RawTermVar : Set where
  here : RawTermVar
  there : RawTermVar -> RawTermVar

data TermVar : TermContext -> Type -> Set where
  here : forall {G A} -> TermVar (G , A) A
  there : forall {G A B} -> TermVar G A -> TermVar (G , B) A

data IsTermVar : TermContext -> RawTermVar -> Type -> Set where
  here : forall {G A} -> IsTermVar (G , A) here A
  there : forall {G x A B} -> IsTermVar G x A -> IsTermVar (G , B) (there x) A





data RawTerm : Set where
  var : RawTermVar -> RawTerm
  true false : RawTerm
  if_then_else_ : RawTerm -> RawTerm -> RawTerm -> RawTerm
  <_,_> : RawTerm -> RawTerm -> RawTerm
  fst snd : RawTerm -> RawTerm
  inl inr : RawTerm -> RawTerm
  case_inl->_inr->_ : RawTerm -> RawTerm -> RawTerm -> RawTerm
  lam : RawTerm -> RawTerm
  _$_ : RawTerm -> RawTerm -> RawTerm

data Term (G : TermContext) : Type -> Set where
  var : forall {A} -> TermVar G A -> Term G A
  true false : Term G Bool
  if_then_else_ : forall {A} -> Term G Bool -> Term G A -> Term G A -> Term G A
  <_,_> : forall {A B} -> Term G A -> Term G B -> Term G (A * B)
  fst : forall {A B} -> Term G (A * B) -> Term G A
  snd : forall {A B} -> Term G (A * B) -> Term G B
  inl : forall {A B} -> Term G A -> Term G (A + B)
  inr : forall {A B} -> Term G B -> Term G (A + B)
  case_inl->_inr->_ : forall {A B C} -> Term G (A + B) -> Term (G , A) C -> Term (G , B) C -> Term G C
  lam : forall {A B} -> Term (G , A) B -> Term G (A => B)
  _$_ : forall {A B} -> Term G (A => B) -> Term G A -> Term G B

data IsTerm (G : TermContext) : RawTerm -> Type -> Set where
  var : forall {x A} -> IsTermVar G x A -> IsTerm G (var x) A
  true : IsTerm G true Bool
  false : IsTerm G false Bool
  if_then_else_ : forall {M N P A} -> IsTerm G M Bool -> IsTerm G N A -> IsTerm G P A -> IsTerm G (if M then N else P) A
  <_,_> : forall {M N A B} -> IsTerm G M A -> IsTerm G N B -> IsTerm G < M , N > (A * B)
  fst : forall {P A B} -> IsTerm G P (A * B) -> IsTerm G (fst P) A
  snd : forall {P A B} -> IsTerm G P (A * B) -> IsTerm G (snd P) B
  inl : forall {M A B} -> IsTerm G M A -> IsTerm G (inl M) (A + B)
  inr : forall {N A B} -> IsTerm G N B -> IsTerm G (inr N) (A + B)
  case_inl->_inr->_ : forall {M N P A B C} -> IsTerm G M (A + B) -> IsTerm (G , A) N C -> IsTerm (G , B) P C -> IsTerm G (case M inl-> N inr-> P) C
  lam : forall {M A B} -> IsTerm (G , A) M B -> IsTerm G (lam M) (A => B)
  _$_ : forall {M N A B} -> IsTerm G M (A => B) -> IsTerm G N A -> IsTerm G (M $ N) B
