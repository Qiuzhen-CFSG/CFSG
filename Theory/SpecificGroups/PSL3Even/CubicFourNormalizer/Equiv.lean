module

public import Theory.SpecificGroups.PSL3Even.CubicFourNormalizer
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# The normal four-group screen under group equivalence

An equivalence with PSL₃(F) maps the literal intrinsic Sylow subgroup onto a
projective Sylow subgroup. Restricting the equivalence to that Sylow transports
its upper-unitriangular marking back to the original group. The normal-four
calculation can therefore retain the original subgroup, normalizer containment
and intrinsic center condition without choosing ambient conjugating elements.

Source: Aschbacher–Smith, 2.4.32, printed p.547, paired A₃ screen. The actual component and
central-quotient consumers supply the intrinsic Sylow normalization assumption.
-/

public section
open scoped MatrixGroups
open Subgroup
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3Even.CubicFourNormalizer

/-- Apply the projective normal-four screen through an arbitrary group equivalence. -/
theorem field_card_two_of_equiv_sylow_normal_four
    (F : Type*) [Field F] [Finite F] {K : Type*} [Group K] [Finite K]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : K ≃* PSL(3,F)) (P : Sylow 2 K) (A : Subgroup K)
    (hcard : Nat.card A = 4) (hAP : A ≤ (P : Subgroup K))
    (hPN : (P : Subgroup K) ≤ Subgroup.normalizer A)
    (hne : ¬ A.subgroupOf (P : Subgroup K) ≤ Subgroup.center (P : Subgroup K)) :
    Nat.card F = 2 := by
  let Q : Sylow 2 PSL(3,F) := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let eP : P ≃* Q := e.subgroupMap (P : Subgroup K)
  let Q₀ := Matrix.PSL3.LinearThree.unipotentSylow F hn hF
  let m : U F ≃* Q :=
    (Matrix.PSL3.LinearThree.unipotentEquiv F).trans (Sylow.equiv Q₀ Q)
  exact field_card_two_of_marked_normal_four F (P : Subgroup K) A (m.trans eP.symm)
    hcard hAP hPN hne

/-- Identify the binary projective model after the normal-four screen. -/
theorem binary_model_of_equiv_sylow_normal_four
    (F : Type*) [Field F] [Finite F] {K : Type*} [Group K] [Finite K]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : K ≃* PSL(3,F)) (P : Sylow 2 K) (A : Subgroup K)
    (hcard : Nat.card A = 4) (hAP : A ≤ (P : Subgroup K))
    (hPN : (P : Subgroup K) ≤ Subgroup.normalizer A)
    (hne : ¬ A.subgroupOf (P : Subgroup K) ≤ Subgroup.center (P : Subgroup K)) :
    Nonempty (K ≃* Matrix.PSL3Two.PSL) := by
  have htwo := field_card_two_of_equiv_sylow_normal_four F hn hF e P A hcard hAP hPN hne
  let := Fintype.ofFinite F
  let s : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ZMod.card]
    exact htwo)
  exact ⟨e.trans (Atlas.fieldEquivPSL 3 s)⟩

end Matrix.PSL3Even.CubicFourNormalizer
