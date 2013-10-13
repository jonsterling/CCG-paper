module CCG where

Type = Set

data ⊥ : Type where
record ⊤ : Type where constructor tt
¬_ : Type → Type
¬ P = P → ⊥
data Decision (P : Type) : Type where
  yes  : P → Decision P
  no   : ¬ P → Decision P
record Σ (A : Type) (B : A → Type) : Type where
  constructor _,_
  field
    fst : A
    snd : B fst
  

Decidable : {C : Type} (R : C → C → Type) → Type
Decidable R = ∀ x y → Decision (R x y)

data _≅_ {A : Type} (x : A) : A → Type where
  refl : x ≅ x

record is-lattice (L : Set) : Set₁ where
  field
    _∨_ : L → L → L
    _∧_ : L → L → L
    ∨-comm : ∀ a b → (a ∨ b) ≅ (b ∨ a)
    ∧-comm : ∀ a b → (a ∧ b) ≅ (b ∧ a)
    ∨-assoc : ∀ a b c → (a ∨ (b ∨ c)) ≅ ((a ∨ b) ∨ c)
    ∧-assoc : ∀ a b c → (a ∧ (b ∧ c)) ≅ ((a ∧ b) ∧ c)
    ∨-absrb : ∀ a b → (a ∨ (a ∧ b)) ≅ a
    ∧-absrb : ∀ a b → (a ∧ (a ∨ b)) ≅ a
    ∨-idem : ∀ a → (a ∨ a) ≅ a
    ∧-idem : ∀ a → (a ∧ a) ≅ a

record is-bounded-lattice (L : Set) : Set₁ where
  private open is-lattice {{...}}
  field
    lat : is-lattice L
    top : L
    bottom : L
    ∨-identity : ∀ a → (a ∨ bottom) ≅ a
    ∧-identity : ∀ a → (a ∧ top) ≅ a

data Direction : Type where
  ▹ ◃ : Direction

!_ : Direction → Direction
! ▹ = ◃
! ◃ = ▹

data Modality : Type where
  ∙ ◇ × ⋆ : Modality

-- _/\_ is the meet of Modality: the greatest lower bound
_∨_ : (a b : Modality) → Modality
∙ ∨ b = b
◇ ∨ ∙ = ◇
◇ ∨ ◇ = ◇
◇ ∨ × = ⋆
◇ ∨ ⋆ = ⋆
× ∨ ∙ = ×
× ∨ ◇ = ⋆
× ∨ × = ×
× ∨ ⋆ = ⋆
⋆ ∨ b = ⋆

_∧_ : (a b : Modality) → Modality
∙ ∧ b = ∙
◇ ∧ ∙ = ∙
◇ ∧ ◇ = ◇
◇ ∧ × = ∙
◇ ∧ ⋆ = ◇
× ∧ ∙ = ∙
× ∧ ◇ = ∙
× ∧ × = ×
× ∧ ⋆ = ×
⋆ ∧ b = b

Modality-Lattice : is-lattice Modality
Modality-Lattice = record {
                     _∨_ = _∨_;
                     _∧_ = _∧_;
                     ∨-comm = λ { ∙ ∙ → refl ; ∙ ◇ → refl ; ∙ × → refl ; ∙ ⋆ → refl ; ◇ ∙ → refl ; ◇ ◇ → refl ; ◇ × → refl ; ◇ ⋆ → refl ; × ∙ → refl ; × ◇ → refl ; × × → refl ; × ⋆ → refl ; ⋆ ∙ → refl ; ⋆ ◇ → refl ; ⋆ × → refl ; ⋆ ⋆ → refl };
                     ∧-comm = λ { ∙ ∙ → refl ; ∙ ◇ → refl ; ∙ × → refl ; ∙ ⋆ → refl ; ◇ ∙ → refl ; ◇ ◇ → refl ; ◇ × → refl ; ◇ ⋆ → refl ; × ∙ → refl ; × ◇ → refl ; × × → refl ; × ⋆ → refl ; ⋆ ∙ → refl ; ⋆ ◇ → refl ; ⋆ × → refl ; ⋆ ⋆ → refl };
                     ∨-assoc = λ { ∙ b c → refl ; ◇ ∙ c → refl ; ◇ ◇ ∙ → refl ; ◇ ◇ ◇ → refl ; ◇ ◇ × → refl ; ◇ ◇ ⋆ → refl ; ◇ × ∙ → refl ; ◇ × ◇ → refl ; ◇ × × → refl ; ◇ × ⋆ → refl ; ◇ ⋆ c → refl ; × ∙ c → refl ; × ◇ ∙ → refl ; × ◇ ◇ → refl ; × ◇ × → refl ; × ◇ ⋆ → refl ; × × ∙ → refl ; × × ◇ → refl ; × × × → refl ; × × ⋆ → refl ; × ⋆ c → refl ; ⋆ b c → refl };
                     ∧-assoc = λ { ∙ b c → refl ; ◇ ∙ c → refl ; ◇ ◇ ∙ → refl ; ◇ ◇ ◇ → refl ; ◇ ◇ × → refl ; ◇ ◇ ⋆ → refl ; ◇ × ∙ → refl ; ◇ × ◇ → refl ; ◇ × × → refl ; ◇ × ⋆ → refl ; ◇ ⋆ c → refl ; × ∙ c → refl ; × ◇ ∙ → refl ; × ◇ ◇ → refl ; × ◇ × → refl ; × ◇ ⋆ → refl ; × × ∙ → refl ; × × ◇ → refl ; × × × → refl ; × × ⋆ → refl ; × ⋆ c → refl ; ⋆ b c → refl };
                     ∨-absrb = λ { ∙ b → refl ; ◇ ∙ → refl ; ◇ ◇ → refl ; ◇ × → refl ; ◇ ⋆ → refl ; × ∙ → refl ; × ◇ → refl ; × × → refl ; × ⋆ → refl ; ⋆ b → refl };
                     ∧-absrb = λ { ∙ b → refl ; ◇ ∙ → refl ; ◇ ◇ → refl ; ◇ × → refl ; ◇ ⋆ → refl ; × ∙ → refl ; × ◇ → refl ; × × → refl ; × ⋆ → refl ; ⋆ b → refl };
                     ∨-idem = λ { ∙ → refl ; ◇ → refl ; × → refl ; ⋆ → refl };
                     ∧-idem = λ { ∙ → refl ; ◇ → refl ; × → refl ; ⋆ → refl } }

Modality-Bounded-Lattice : is-bounded-lattice Modality
Modality-Bounded-Lattice = record {
                             lat = Modality-Lattice;
                             top = ⋆;
                             bottom = ∙;
                             ∨-identity = λ { ∙ → refl ; ◇ → refl ; × → refl ; ⋆ → refl };
                             ∧-identity = λ { ∙ → refl ; ◇ → refl ; × → refl ; ⋆ → refl }}

_≟m_ : Decidable (_≅_ {A = Modality})
∙ ≟m ∙ = yes refl
∙ ≟m ◇ = no (λ ())
∙ ≟m × = no (λ ())
∙ ≟m ⋆ = no (λ ())
◇ ≟m ∙ = no (λ ())
◇ ≟m ◇ = yes refl
◇ ≟m × = no (λ ())
◇ ≟m ⋆ = no (λ ())
× ≟m ∙ = no (λ ())
× ≟m ◇ = no (λ ())
× ≟m × = yes refl
× ≟m ⋆ = no (λ ())
⋆ ≟m ∙ = no (λ ())
⋆ ≟m ◇ = no (λ ())
⋆ ≟m × = no (λ ())
⋆ ≟m ⋆ = yes refl

_≤_ : (a b : Modality) → Set
a ≤ b with (a ∧ b) ≟m a
a ≤ b | yes x = ⊤
a ≤ b | no x = ⊥

_≤?_ : Decidable _≤_
a ≤? b with (a ∧ b) ≟m a
a ≤? b | yes x = yes tt
a ≤? b | no x = no (λ z → z)

data SynType : Type where
  N D V  : SynType
  _|[_,_]_ : (X : SynType) (θ : Direction) (μ : Modality) (Y : SynType) → SynType

data Lex : SynType → Type where
  dog  : Lex N
  the  : Lex (D |[ ▹ , ◇ ] N)
  happy  : Lex (N |[ ▹ , ◇ ] N)


data Either (A B : Type) : Type where
  left : A → Either A B
  right : B → Either A B

data Turn (θ : Direction) (μ ν : Modality) : Direction → Type where
  ∥ : ⦃ _ : ◇ ≤ μ ⦄ ⦃ _ : ◇ ≤ ν ⦄ → Turn θ μ ν θ
  ⋏ : ⦃ _ : × ≤ μ ⦄ ⦃ _ : × ≤ ν ⦄ → Turn θ μ ν (! θ)

data Tm : SynType → Type where
  [_] : ∀ {X} → Lex X → Tm X
  App : ∀ {X Y θ μ} ⦃ _ : ∙ ≤ μ ⦄ (f : Tm (X |[ θ , μ ] Y)) (x : Tm Y) → Tm X
  B⟨_⟩ : ∀ {X Y Z θ θ′ μ ν} (_ : Turn θ μ ν θ′) (f : Tm (X |[ θ , μ ] Y)) (g : Tm (Y |[ θ′ , ν ] Z)) → Tm (X |[ θ′ , μ ∧ ν ] Z)

infixr 9 _,_
data String : Set where
  [] : String
  _,_ : {A : SynType} → Lex A → String → String

_++_ : String → String → String
[] ++ ys = ys
(x , xs) ++ ys = x , xs ++ ys

_++[_]_ : String → Direction → String → String
xs ++[ ▹ ] ys = xs ++ ys
xs ++[ ◃ ] ys = ys ++ xs

print : ∀ {A} → Tm A → String
print [ x ] = x , []
print (App {θ = θ} f x) = print f ++[ θ ] print x
print (B⟨_⟩ {θ = θ} t f g) = print f ++[ θ ] print g
  
happy-dog : Tm N
happy-dog = App [ happy ] [ dog ]

the-happy : Tm (D |[ ▹ , ◇ ] N)
the-happy = B⟨ ∥ ⟩ [ the ] [ happy ]

the-happy-dog : Tm D
the-happy-dog = App the-happy [ dog ]
