module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition
public import Theory.Representation.SL2.BinaryHermitianRecognition.CardFourTrace
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.AlternatingFive
public import Theory.Representation.Quotient

/-!
# The complete binary irreducible A₅ module alternatives

There are exactly two nontrivial irreducible binary A₅ modules: the scalar
restriction of the natural SL₂(4) module and the deleted permutation module.
The unrestricted highest-weight classification gives weights one, two and
three. The first two have Schur degree two; the weight-three trace calculation
forces Schur degree one. Thus every case has binary dimension four, without
assuming a degree or offender bound.

The recognition maps are actual action intertwiners. The Hermitian comparison
uses the five singular points to identify the deleted permutation action.

Source: the SL₂ highest-weight and descent results of GLS3, §§2.8.6–2.8.10;
Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3 and I.1.6(3).
-/

public section
open scoped MatrixGroups MonoidAlgebra TensorProduct
open Representation Representation.SL2
variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,K) V) [ρ.IsIrreducible]

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic

/-- Every nontrivial irreducible binary action of SL₂ over a field of four
elements is natural or Hermitian. Both alternatives retain actual intertwiners,
and their distinct Schur degrees distinguish the two models. -/
theorem binary_card_four_module_alternatives
    (hc : Nat.card K = 4) (hρ : ∃ g, ρ g ≠ 1) :
    Module.finrank (ZMod 2) V = 4 ∧
      ((Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule) = 2 ∧
        BinarySmall.IsNatural ρ) ∨
      (Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule) = 1 ∧
        BinarySmall.IsHermitian ρ 1)) := by
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let s := Module.finrank (ZMod 2) E
  obtain ⟨hs, w, hw, hsdiv, hperiod, hdim, e, he⟩ :=
    exists_binary_highestWeight_parameters ρ hρ 2 (by simpa using hc)
  have hperiod : 3 ∣ w.val * (2 ^ s - 1) := by simpa only [hc] using hperiod
  change Module.finrank (ZMod 2) V = s * ∏ i : Fin 2, (w.val / 2 ^ (i : ℕ) % 2 + 1) at hdim
  have hsalt : s = 1 ∨ s = 2 := by
    simpa only [Nat.dvd_prime Nat.prime_two] using hsdiv
  have hwlt : w.val < 4 := by simpa only [hc] using w.isLt
  have hwalt : w.val = 1 ∨ w.val = 2 ∨ w.val = 3 := by omega
  have hweight (n : ℕ) (hn : w.val = n) :
      Nonempty ((extendScalars (AlgebraicClosure E) ρ.endFieldRep).Equiv
        (highestWeightSpan e n).toRepresentation) :=
    (congrArg (fun m => Nonempty ((extendScalars (AlgebraicClosure E) ρ.endFieldRep).Equiv
      (highestWeightSpan e m).toRepresentation)) hn).mp he
  rcases hwalt with hw1 | hw2 | hw3
  · have hs2 : s = 2 := by
      rcases hsalt with hs1 | hs2
      · rw [hw1, hs1] at hperiod
        norm_num at hperiod
      · exact hs2
    constructor
    · simpa [hw1, Fin.prod_univ_two, hs2] using hdim
    · left
      refine ⟨hs2, ?_⟩
      exact BinarySmall.isNatural_of_highestWeight_pow_two ρ 2 (by decide)
        (by simpa using hc) hs2 0 (by decide) e (hweight _ hw1)
  · have hs2 : s = 2 := by
      rcases hsalt with hs1 | hs2
      · rw [hw2, hs1] at hperiod
        norm_num at hperiod
      · exact hs2
    constructor
    · simpa [hw2, Fin.prod_univ_two, hs2] using hdim
    · left
      refine ⟨hs2, ?_⟩
      exact BinarySmall.isNatural_of_highestWeight_pow_two ρ 2 (by decide)
        (by simpa using hc) hs2 1 (by decide) e (hweight _ hw2)
  · have hs1 : s = 1 := BinaryHermitian.schur_degree_one_of_highestWeight_three ρ hc e (hweight _ hw3)
    constructor
    · simpa [hw3, Fin.prod_univ_two, hs1] using hdim
    · right
      refine ⟨hs1, ?_⟩
      exact BinaryHermitian.isHermitian_of_highestWeight_pair ρ (by decide : 0 < 1)
        (by simpa using hc) hs1 0 (by decide) e (hweight _ hw3)

noncomputable section

private def slFieldEquiv {K F : Type*} [Field K] [Field F] (e : K ≃+* F) :
    SL(2,K) ≃* SL(2,F) where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by ext i j; exact e.symm_apply_apply (g.val i j)
  right_inv g := by ext i j; exact e.apply_symm_apply (g.val i j)
  map_mul' := (Matrix.SpecialLinearGroup.map e.toRingHom).map_mul

open Representation.OrthogonalFourMinus.AlternatingFive

variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,K) V)

omit [Finite K] [CharP K 2] [FiniteDimensional (ZMod 2) V] in
/-- The actual Hermitian model at half-degree one is the deleted five-point
permutation module, retaining its induced group identification. -/
theorem deleted_of_hermitian (h : BinarySmall.IsHermitian ρ 1) :
    ∃ e : SL(2,K) ≃* alternatingGroup (Fin 5),
      Nonempty (ρ.Equiv (alternatingRepresentation.comp e.toMonoidHom)) := by
  let aH := moduleEquiv.toAddEquiv
  let := BinarySmall.spaceBinaryModule 1
  obtain ⟨f, ⟨u⟩⟩ := h
  let e := (slFieldEquiv f).trans groupEquiv
  let a := u.toLinearEquiv.toAddEquiv.trans aH
  let b : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
    LinearEquiv.ofBijective (a.toAddMonoidHom.toZModLinearMap 2) a.bijective
  refine ⟨e, ⟨Representation.Equiv.mk b ?_⟩⟩
  intro g
  apply LinearMap.ext
  intro v
  change aH (u (ρ g v)) = alternatingRepresentation (e g) (aH (u v))
  exact (congrArg aH (Representation.IntertwiningMap.isIntertwining ρ _
    u.toIntertwiningMap g v)).trans
    (binaryAction_intertwines (Matrix.SpecialLinearGroup.map f.toRingHom g) (u v))

variable [ρ.IsIrreducible]
/-- The two field-four alternatives with literal natural and deleted actions. -/
theorem binary_card_four_action_alternatives (hc : Nat.card K = 4) (hρ : ∃ g, ρ g ≠ 1) :
    Module.finrank (ZMod 2) V = 4 ∧
      (BinarySmall.IsNatural ρ ∨
        ∃ e : SL(2,K) ≃* alternatingGroup (Fin 5),
          Nonempty (ρ.Equiv (alternatingRepresentation.comp e.toMonoidHom))) := by
  obtain ⟨hd, h | h⟩ := binary_card_four_module_alternatives ρ hc hρ
  · exact ⟨hd, Or.inl h.2⟩
  · exact ⟨hd, Or.inr (deleted_of_hermitian ρ h.2)⟩


private def equivFromPullback {F G J U W : Type*} [Field F] [Group G] [Group J]
    [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W]
    (e : G ≃* J) (τ : Representation F J U) (υ : Representation F G W)
    (u : Representation.Equiv (τ.comp e.toMonoidHom) υ) :
    τ.Equiv (υ.comp e.symm.toMonoidHom) := by
  refine Representation.Equiv.mk u.toLinearEquiv ?_
  intro g
  apply LinearMap.ext
  intro v
  have hu := Representation.IntertwiningMap.isIntertwining
    (τ.comp e.toMonoidHom) υ u.toIntertwiningMap (e.symm g) v
  change u (τ (e (e.symm g)) v) = υ (e.symm g) (u v) at hu
  change u (τ g v) = υ (e.symm g) (u v)
  simpa only [e.apply_symm_apply] using hu

local instance : Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

variable {J W : Type*} [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]

/-- Every nontrivial irreducible binary action of an arbitrary group identified
with A₅ is naturally or deleted-permutation marked. The original actor and
vector space are retained; no degree or offender bound is assumed. -/
theorem alternating_five_irreducible_action_alternatives
    (σ : Representation (ZMod 2) J W) [σ.IsIrreducible]
    (e : J ≃* alternatingGroup (Fin 5)) (hσ : ∃ g, σ g ≠ 1) :
    Module.finrank (ZMod 2) W = 4 ∧
      ((∃ f : J ≃* SL(2,Representation.OrthogonalFourMinus.FiniteModel.Field 1),
          Nonempty (σ.Equiv ((BinarySmall.natural).comp f.toMonoidHom))) ∨
        ∃ f : J ≃* alternatingGroup (Fin 5),
          Nonempty (σ.Equiv (alternatingRepresentation.comp f.toMonoidHom))) := by
  let t := groupEquiv.trans e.symm
  let τ : Representation (ZMod 2) (Representation.OrthogonalFourMinus.AlternatingFive.Group) W :=
    σ.comp t.toMonoidHom
  let : τ.IsIrreducible :=
    (irreducible_comp_surjective_iff t.toMonoidHom t.surjective σ).mpr inferInstance
  have hτ : ∃ g, τ g ≠ 1 := by
    obtain ⟨g, hg⟩ := hσ
    refine ⟨t.symm g, ?_⟩
    change σ (t (t.symm g)) ≠ 1
    rwa [t.apply_symm_apply]
  have hc : Nat.card (Representation.OrthogonalFourMinus.FiniteModel.Field 1) = 4 :=
    GaloisField.card 2 2 (by decide)
  obtain ⟨hd, h | h⟩ := binary_card_four_action_alternatives τ hc hτ
  · exact ⟨hd, Or.inl ⟨t.symm, ⟨equivFromPullback t σ _ h.some⟩⟩⟩
  · obtain ⟨f, ⟨u⟩⟩ := h
    exact ⟨hd, Or.inr ⟨t.symm.trans f, ⟨equivFromPullback t σ _ u⟩⟩⟩

end
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic
