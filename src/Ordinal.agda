{-# OPTIONS --safe #-}
module Ordinal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Relation.Binary.Base

open import Cubical.Induction.WellFounded

open Iso
open BinaryRelation


private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

record IsOrdinal {A : Type ℓ} (_<_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isordinal

  field
    is-set : isSet A
    is-prop-valued : isPropValued _<_

    is-trans : isTrans _<_
    well-founded : WellFounded _<_
    extensional : ∀ a b → (∀ c → (c < a → c < b) × (c < b → c < a)) → a ≡ b

  open WFI well-founded public

  trans : ∀ {a b c} → a < b → b < c → a < c
  trans = is-trans _ _ _

unquoteDecl IsOrdinalIsoΣ = declareRecordIsoΣ IsOrdinalIsoΣ (quote IsOrdinal)


record OrdinalStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor ordinalstr

  field
    _<_         : A → A → Type ℓ'
    isOrdinal : IsOrdinal _<_

  infixl 7 _<_

  open IsOrdinal isOrdinal public

Ordinal : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Ordinal ℓ ℓ' = TypeWithStr ℓ (OrdinalStr ℓ')

ordinal : (A : Type ℓ) (_<_ : A → A → Type ℓ') (h : IsOrdinal _<_) → Ordinal ℓ ℓ'
ordinal A _<_ h = A , ordinalstr _<_ h

record IsOrdinalEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : OrdinalStr ℓ₀' A) (e : A ≃ B) (N : OrdinalStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor
   isordinalequiv
  -- Shorter qualified names
  private
    module M = OrdinalStr M
    module N = OrdinalStr N

  field
    pres< : (x y : A) → x M.< y ≃ equivFun e x N.< equivFun e y

  pres⁻¹< : (x y : B) → x N.< y ≃ invEq e x M.< invEq  e y
  pres⁻¹< x y = subst2 (λ x' y' → x' N.< y' ≃ invEq e x M.< invEq e y)
                       (secEq e x) (secEq e y)
                       (invEquiv (pres< (invEq e x) (invEq e y)))

isPropIsOrdinalEquiv : ∀ {A : Type ℓ₀} {B : Type ℓ₁} (M : OrdinalStr ℓ₀' A) (e : A ≃ B) (N : OrdinalStr ℓ₁' B) →
                        isProp (IsOrdinalEquiv M e N)
isPropIsOrdinalEquiv M e N p q i =
  let module M = OrdinalStr M
      module N = OrdinalStr N
      module p = IsOrdinalEquiv p
      module q = IsOrdinalEquiv q
  in
  isordinalequiv λ x y → equivEq {e = p.pres< x y} {f = q.pres< x y}
    (funExt (λ h → N.is-prop-valued _ _ (equivFun (p.pres< _ _) h) (equivFun (q.pres< _ _) h))) i

OrdinalEquiv : (M : Ordinal ℓ₀ ℓ₀') (M : Ordinal ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
OrdinalEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsOrdinalEquiv (M .snd) e (N .snd)

isPropIsOrdinal : {A : Type ℓ} (_<_ : A → A → Type ℓ') → isProp (IsOrdinal _<_)
isPropIsOrdinal _<_ = isOfHLevelRetractFromIso 1 IsOrdinalIsoΣ
  (isPropΣ isPropIsSet λ isSetA →
    isPropΣ (isPropΠ2 λ _ _ → isPropIsProp) λ isPropValued< →
    isProp×2 (isPropΠ5 λ _ _ _ _ _ → isPropValued< _ _)
             (isPropΠ isPropAcc)
             (isPropΠ3 λ _ _ _ → isSetA _ _))

𝒮ᴰ-Ordinal : DUARel (𝒮-Univ ℓ) (OrdinalStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-Ordinal =
  𝒮ᴰ-Record (𝒮-Univ _) IsOrdinalEquiv
    (fields:
      data[ _<_ ∣ autoDUARel _ _ ∣ pres< ]
      prop[ isOrdinal ∣ (λ _ _ → isPropIsOrdinal _) ])
    where
    open OrdinalStr
    open IsOrdinal
    open IsOrdinalEquiv

OrdinalPath : (M N : Ordinal ℓ ℓ') → OrdinalEquiv M N ≃ (M ≡ N)
OrdinalPath = ∫ 𝒮ᴰ-Ordinal .UARel.ua

-- an easier way of establishing an equivalence of ordinals
module _ {P : Ordinal ℓ₀ ℓ₀'} {S : Ordinal ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = OrdinalStr (P .snd)
    module S = OrdinalStr (S .snd)

  module _ (isMon : ∀ x y → x P.< y → equivFun e x S.< equivFun e y)
           (isMonInv : ∀ x y → x S.< y → invEq e x P.< invEq e y) where
    open IsOrdinalEquiv
    open IsOrdinal

    makeIsOrdinalEquiv : IsOrdinalEquiv (P .snd) e (S .snd)
    pres< makeIsOrdinalEquiv x y = propBiimpl→Equiv (P.isOrdinal .is-prop-valued _ _)
                                                    (S.isOrdinal .is-prop-valued _ _)
                                                    (isMon _ _) (isMonInv' _ _)
      where
      isMonInv' : ∀ x y → equivFun e x S.< equivFun e y → x P.< y
      isMonInv' x y ex≤ey = transport (λ i → retEq e x i P.< retEq e y i) (isMonInv _ _ ex≤ey)

module _ {M : Ordinal ℓ₀ ℓ₀'} {N : Ordinal ℓ₁ ℓ₁'} where
  private
    module M = OrdinalStr (snd M)
    module N = OrdinalStr (snd N)

  ordinalEquivEq : {e f : OrdinalEquiv M N} (h : equivFun (fst e) ≡ equivFun (fst f)) → e ≡ f
  ordinalEquivEq {e = e} {f = f} h =
    Σ≡Prop (λ _ → isPropIsOrdinalEquiv _ _ _) (equivEq h)

  OrdinalEquiv-unique-value : ∀ (f g : OrdinalEquiv M N)  (x : ⟨ M ⟩) → equivFun (fst f) x ≡ equivFun (fst g) x
  OrdinalEquiv-unique-value f g =
    let module f = IsOrdinalEquiv (snd f)
        module g = IsOrdinalEquiv (snd g)
    in
    M.induction λ x rec →
    N.extensional _ _ λ c →
      (λ c<fx → let ff⁻¹c≡c = secEq (fst f) c
                    ff⁻¹c<fx = subst⁻ (λ a → a N.< equivFun (fst f) x) ff⁻¹c≡c c<fx
                    f⁻¹c<x = invEq (f.pres< (invEq (fst f) c) x) ff⁻¹c<fx
                    c≡gf⁻¹c = sym ff⁻¹c≡c ∙ rec (invEq (fst f) c) f⁻¹c<x
                in subst⁻ (λ a → a N.< _) c≡gf⁻¹c (equivFun (g.pres< _ _) f⁻¹c<x)) ,
      λ c<gx → let gg⁻¹c≡c = secEq (fst g) c
                   gg⁻¹c<gx = subst⁻ (λ a → a N.< _) gg⁻¹c≡c c<gx
                   g⁻¹c<x = invEq (g.pres< (invEq (fst g) c) x) gg⁻¹c<gx
                   fg⁻¹c≡c = rec (invEq (fst g) c) g⁻¹c<x ∙ gg⁻¹c≡c
               in subst (λ a → a N.< _) fg⁻¹c≡c (equivFun (f.pres< _ _) g⁻¹c<x)

  isPropOrdinalEquiv : isProp (OrdinalEquiv M N) 
  isPropOrdinalEquiv f g = 
    ordinalEquivEq (funExt (OrdinalEquiv-unique-value f g))

isSetOrdinal : isSet (Ordinal ℓ ℓ')
isSetOrdinal M N = isOfHLevelRespectEquiv 1 (OrdinalPath M N) isPropOrdinalEquiv

record IsSimulation {A : Type ℓ₀} {B : Type ℓ₁}
  (M : OrdinalStr ℓ₀' A) (f : A → B) (N : OrdinalStr ℓ₁' B) : Type (ℓ-max (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁) ℓ₁') where
  constructor issimulation

  private
    module M = OrdinalStr M
    module N = OrdinalStr N

  field
    pres< : ∀ x y → x M.< y → f x N.< f y
    simulated : ∀ x y → y N.< f x → Σ[ x' ∈ A ] (x' M.< x) × (f x' ≡ y)
  
  injective : ∀ x y → f x ≡ f y → x ≡ y
  injective =
    M.induction λ x rec y fx≡fy →
    M.extensional x y λ c →
    (λ c<x → let fc<fx = pres< c x c<x
                 fc<fy = subst (λ a → f c N.< a) fx≡fy fc<fx
                 c' , c'<y , fc'≡fc = simulated y (f c) fc<fy
                 c≡c' = rec c c<x c' (sym fc'≡fc)
             in subst⁻ (λ a → a M.< y) c≡c' c'<y) ,
    λ c<y → let fc<fy = pres< c y c<y
                fc<fx = subst⁻ (λ a → f c N.< a) fx≡fy fc<fy
                c' , c'<x , fc'≡fc = simulated x (f c) fc<fx
                c'≡c = rec c' c'<x c fc'≡fc
            in subst (λ a → a M.< x) c'≡c c'<x 
  
isPropIsSimulation : ∀ {A : Type ℓ₀} {B : Type ℓ₁}
  (M : OrdinalStr ℓ₀' A) (f : A → B) (N : OrdinalStr ℓ₁' B) →
  isProp (IsSimulation M f N)
isPropIsSimulation M f N p q =
  let module M = OrdinalStr M
      module N = OrdinalStr N
      module p = IsSimulation p
      module q = IsSimulation q
  in
  cong₂ issimulation (funExt λ x → funExt λ y → funExt λ h → N.is-prop-valued (f x) (f y) (p.pres< x y h) (q.pres< x y h))
                     (funExt λ x → funExt λ y → funExt λ h →
                      Σ≡Prop (λ x' → isProp× (M.is-prop-valued x' x) (N.is-set (f x') y)) 
                        (let px , px<x , fpx≡y = p.simulated x y h
                             qx , qx<x , fqx≡y = q.simulated x y h
                             fpx≡fqx = fpx≡y ∙ sym fqx≡y
                         in
                         p.injective px qx fpx≡fqx))

Simulation : (M : Ordinal ℓ₀ ℓ₀') (M : Ordinal ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
Simulation M N = Σ[ f ∈ (⟨ M ⟩ → ⟨ N ⟩) ] IsSimulation (M .snd) f (N .snd)

_/_ : (A : Ordinal ℓ ℓ') → ⟨ A ⟩ → Ordinal (ℓ-max ℓ ℓ') ℓ'
A / a = A/a , ordinalstr _<'_ A/a-IsOrdinal
  where
    open OrdinalStr (snd A)

    A/a = Σ[ a' ∈ ⟨ A ⟩ ] (a' < a)

    _<'_ : A/a → A/a → Type _
    x <' y = fst x < fst y

    A/a-IsOrdinal : IsOrdinal _<'_
    IsOrdinal.is-set A/a-IsOrdinal = isSetΣ is-set λ a' → isProp→isSet (is-prop-valued a' a)
    IsOrdinal.is-prop-valued A/a-IsOrdinal x y = is-prop-valued (fst x) (fst y)
    IsOrdinal.is-trans A/a-IsOrdinal x y z = is-trans (fst x) (fst y) (fst z)
    IsOrdinal.well-founded A/a-IsOrdinal α =
      induction {P = λ x → (p : x < a) → Acc _<'_ (x , p)}
                (λ x rec x<a → acc λ y y<x → rec (fst y) y<x (snd y)) (fst α) (snd α)
    IsOrdinal.extensional A/a-IsOrdinal x y hyp =
      Σ≡Prop (λ a' → is-prop-valued a' a)
            (extensional (fst x) (fst y) λ c →
              (λ c<x → fst (hyp (c , is-trans c (fst x) a c<x (snd x))) c<x) ,
              λ c<y → snd (hyp (c , is-trans c (fst y) a c<y (snd y))) c<y)

module _ {M : Ordinal ℓ₀ ℓ₀'} {N : Ordinal ℓ₁ ℓ₁'} where
  private
    module M = OrdinalStr (snd M)
    module N = OrdinalStr (snd N)

  SimulationEq : ∀ (f g : Simulation M N) → (f .fst ≡ g .fst) → f ≡ g
  SimulationEq f g = Σ≡Prop (λ e → isPropIsSimulation (snd M) e (snd N))

  Simulation-unique : (f g : Simulation M N) → ∀ x → fst f x ≡ fst g x
  Simulation-unique f g =
    let module f = IsSimulation (snd f)
        module g = IsSimulation (snd g)
    in
    M.induction λ x rec →
    N.extensional (fst f x) (fst g x) λ c →
    (λ c<fx → let c' , c'<x , fc'≡c = f.simulated x c c<fx
                  fc'≡gc' = rec c' c'<x
                  gc'≡c = sym fc'≡gc' ∙ fc'≡c
                  gc'<gx = g.pres< _ _ c'<x
              in subst (λ a → a N.< fst g x) gc'≡c gc'<gx) ,
    λ c<gx → let c' , c'<x , gc'≡c = g.simulated x c c<gx
                 fc'≡gc' = rec c' c'<x
                 fc'≡c = fc'≡gc' ∙ gc'≡c
                 fc'<fx = f.pres< _ _ c'<x
              in subst (λ a → a N.< fst f x) fc'≡c fc'<fx

  isPropSimulation : isProp (Simulation M N)
  isPropSimulation f g = SimulationEq f g (funExt (Simulation-unique f g))

_/_-include : ∀ (A : Ordinal ℓ ℓ') (a : ⟨ A ⟩) → Simulation (A / a) A
A / a -include = fst , issimulation (λ x y x<y → x<y) λ x y y<x → (y , trans y<x (snd x)) , y<x , refl
  where
    open OrdinalStr (snd A)

_/_-include-unique : ∀ (A : Ordinal ℓ ℓ') (a : ⟨ A ⟩)  (f : Simulation (A / a) A) → f ≡ A / a -include
_/_-include-unique A a f = isPropSimulation f (A / a -include)

idsim : ∀ (O : Ordinal ℓ ℓ') → Simulation O O
fst (idsim O) x = x
IsSimulation.pres< (snd (idsim O)) x y H = H
IsSimulation.simulated (snd (idsim O)) x y H = y , H , refl

_/-injective : (A : Ordinal ℓ ℓ') (a b : ⟨ A ⟩) → (A / a) ≡ (A / b) → a ≡ b 
(A /-injective) a b A/a≡A/b =
  let module A = OrdinalStr (snd A)
      module A/a = OrdinalStr (snd (A / a))
      module A/b = OrdinalStr (snd (A / b))
      A/a = A / a -include
      A/b = A / b -include

      fun : Simulation (A / a) (A / b)
      fun = transport (λ i → Simulation (A / a) (A/a≡A/b i)) (idsim (A / a))
      A/a≡A/b∘fun : ∀ x → fst A/a x ≡ fst A/b (fst fun x)
      A/a≡A/b∘fun x i = 
        hcomp (λ j → λ where
                        (i = i0) → fst x
                        (i = i1) → fst A/b (fst fun x))
              {!   !}

      <a→<b : ∀ x → x A.< a → x A.< b 
      <a→<b x x<a =
        let x' = fst fun (x , x<a)
            x'≡x : fst x' ≡ x
            x'≡x = {!   !}
            r = IsSimulation.pres< (snd A/a) {!   !} {!   !}
        in {!   !}
  in
  A.extensional a b λ c →
  (λ c<a → let c' , c'<b = transport (λ i → fst (A/a≡A/b i)) (c , c<a)
               c≡c' = {!   !}
           in {!   !}) ,
  λ c<b → {!   !}

module _ {M : Ordinal ℓ₀ ℓ₀'} {N : Ordinal ℓ₁ ℓ₁'} (f : Simulation M N) where

  IsBoundedSimulation : Type _
  IsBoundedSimulation = ∃[ b ∈ ⟨ N ⟩ ] OrdinalEquiv M (N / b)


private
  module _ where
    open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-elim)
    open import Cubical.Relation.Nullary

    open import Cubical.Data.Nat
    open import Cubical.Data.Nat.Order

    ℕ-IsOrdinal : IsOrdinal _<_
    IsOrdinal.is-set ℕ-IsOrdinal = isSetℕ
    IsOrdinal.is-prop-valued ℕ-IsOrdinal m n = m≤n-isProp
    IsOrdinal.is-trans ℕ-IsOrdinal l m n = <-trans
    IsOrdinal.well-founded ℕ-IsOrdinal = <-wellfounded
    IsOrdinal.extensional ℕ-IsOrdinal = extensional
      where
        extensional : ∀ a b → (∀ c → (c < a → c < b) × (c < b → c < a)) → a ≡ b
        extensional a b hyp with a ≟ b
        ... | lt a<b = ⊥-elim (¬m<m (snd (hyp a) a<b))
        ... | eq a≡b = a≡b
        ... | gt b<a = ⊥-elim (¬m<m (fst (hyp b) b<a))

    ω : Ordinal _ _
    ω = ℕ , ordinalstr _ ℕ-IsOrdinal
