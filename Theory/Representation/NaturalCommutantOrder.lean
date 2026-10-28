module
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.Representation.BinaryDoubledNaturalCentralizer
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.GroupTheory.Index

/-!
# Orders of marked natural-module commutants

The additive transvection calculations make the natural commutant scalar.
Invertibility forces a nonzero scalar, embedding the automorphism commutant
in the field units. For SL₂ its order divides q-1 and hence |SL₂(q)|; over
F₂ the natural SLₙ commutant is trivial. The marking is surjective on actors
and equivariant on the actual space. These results concern one natural copy,
without silently suppressing multiplicities.

Source: Aschbacher--Smith, 10.2.3(2), printed p.745, natural rows of 10.1.1.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {F V W A : Type*} [Field F] [AddCommGroup V] [Module F V]
  [Group W] [Group A]

private noncomputable def scalarAutomorphisms : Fˣ →* MulAut (Multiplicative V) where
  toFun c := AddEquiv.toMultiplicative (LinearEquiv.smulOfUnit c).toAddEquiv
  map_one' := by ext v; exact one_smul F v.toAdd
  map_mul' c d := by ext v; exact mul_smul (c : F) (d : F) v.toAdd

/-- Scalar commutation embeds the actual automorphism commutant in the field units. -/
theorem commutant_card_dvd_scalars [Finite F] [Nontrivial V]
    (f : A →* MulAut W) (e : W ≃* Multiplicative V)
    (hs : ∀ c ∈ centralizer (f.range : Set (MulAut W)),
      ∃ d : F, ∀ w, (e (c w)).toAdd = d • (e w).toAdd) :
    Nat.card (centralizer (f.range : Set (MulAut W))) ∣ Nat.card F - 1 := by
  let C := centralizer (f.range : Set (MulAut W))
  let a := MulAut.congr e
  have hC : C.map a.toMonoidHom ≤ (scalarAutomorphisms (F := F) (V := V)).range := by
    rintro z ⟨c,hc,rfl⟩
    obtain ⟨d,hd⟩ := hs c hc
    have hd0 : d ≠ 0 := by
      intro hz
      obtain ⟨v,hv⟩ := exists_ne (0 : V)
      obtain ⟨w,hw⟩ := (e.surjective.comp c.surjective) (Multiplicative.ofAdd v)
      have hh := hd w
      change e (c w) = Multiplicative.ofAdd v at hw
      rw [hw,hz,zero_smul] at hh
      exact hv hh
    refine ⟨Units.mk0 d hd0,?_⟩
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    change d • v.toAdd = (e (c (e.symm v))).toAdd
    rw [hd,e.apply_symm_apply]
  have h := (card_dvd_of_le hC).trans (card_range_dvd (scalarAutomorphisms (F := F) (V := V)))
  rwa [card_map_of_injective a.injective,Nat.card_units] at h

variable [Finite F] {n : ℕ}

/-- A surjective natural marking transports an additive scalar-commutant calculation. -/
theorem natural_commutant_card_dvd
    (f : A →* MulAut W)
    (q : A →* Matrix.SpecialLinearGroup (Fin n) F) (hq : Function.Surjective q)
    (e : W ≃* Multiplicative (Fin n → F))
    (he : ∀ a w, (e (f a w)).toAdd = (q a).val.mulVec (e w).toAdd)
    (hn : 0 < n)
    (hscalar : ∀ b : (Fin n → F) →+ (Fin n → F),
      (∀ g : Matrix.SpecialLinearGroup (Fin n) F, ∀ v,
        b (g.val.mulVec v) = g.val.mulVec (b v)) →
      ∃ d : F, ∀ v, b v = d • v) :
    Nat.card (centralizer (f.range : Set (MulAut W))) ∣ Nat.card F - 1 := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  apply commutant_card_dvd_scalars f e
  intro c hc
  let b := AddMonoidHom.toMultiplicative.symm ((MulAut.congr e c).toMonoidHom)
  have hb : ∀ g : Matrix.SpecialLinearGroup (Fin n) F, ∀ v,
      b (g.val.mulVec v) = g.val.mulVec (b v) := by
    intro g v
    obtain ⟨a,rfl⟩ := hq g
    obtain ⟨w,rfl⟩ := e.surjective (Multiplicative.ofAdd v)
    have hh := congrArg (fun t : MulAut W => (e (t w)).toAdd)
      (hc (f a) (⟨a,rfl⟩))
    change (e (f a (c w))).toAdd = (e (c (f a w))).toAdd at hh
    rw [he] at hh
    change (e (c (e.symm (Multiplicative.ofAdd ((q a).val.mulVec (e w).toAdd))))).toAdd = _
    rw [←he]
    change (e (c (e.symm (e (f a w))))).toAdd =
      (q a).val.mulVec (e (c (e.symm (e w)))).toAdd
    rw [e.symm_apply_apply,e.symm_apply_apply]
    exact hh.symm
  obtain ⟨d,hd⟩ := hscalar b hb
  refine ⟨d,fun w => ?_⟩
  have h := hd (e w).toAdd
  change (e (c (e.symm (e w)))).toAdd = d • (e w).toAdd at h
  rwa [e.symm_apply_apply] at h

/-- The commutant of one marked natural SL₂ copy has order dividing the actor order. -/
theorem sl2_natural_commutant_card_dvd
    (f : A →* MulAut W)
    (q : A →* Matrix.SpecialLinearGroup (Fin 2) F) (hq : Function.Surjective q)
    (e : W ≃* Multiplicative (Fin 2 → F))
    (he : ∀ a w, (e (f a w)).toAdd = (q a).val.mulVec (e w).toAdd) :
    Nat.card (centralizer (f.range : Set (MulAut W))) ∣
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
  apply (natural_commutant_card_dvd f q hq e he (by decide)
    (fun b hb => Representation.SL2NaturalOffenders.centralizer_scalar b hb)).trans
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup]
  have hqpos : 0 < Nat.card F := Nat.card_pos
  have hq2 : 1 ≤ Nat.card F ^ 2 := by nlinarith
  refine ⟨Nat.card F * (Nat.card F + 1),?_⟩
  have h1 := Nat.sub_add_cancel (show 1 ≤ Nat.card F from hqpos)
  have h2 := Nat.sub_add_cancel hq2
  nlinarith

omit [Field F] [Finite F] in
/-- One marked natural binary SLₙ copy, n ≥ 2, has trivial automorphism commutant. -/
theorem binary_natural_commutant_card_eq_one
    [NeZero n] (hn : 2 ≤ n)
    (f : A →* MulAut W)
    (q : A →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (hq : Function.Surjective q)
    (e : W ≃* Multiplicative (Fin n → ZMod 2))
    (he : ∀ a w, (e (f a w)).toAdd = (q a).val.mulVec (e w).toAdd) :
    Nat.card (centralizer (f.range : Set (MulAut W))) = 1 := by
  have h := natural_commutant_card_dvd f q hq e he (by omega)
    (fun b hb => Representation.BinaryDoubledNatural.natural_centralizer_scalar hn b hb)
  simpa only [Nat.card_zmod, Nat.reduceSub, Nat.dvd_one] using h

end Theory.GroupTheory
