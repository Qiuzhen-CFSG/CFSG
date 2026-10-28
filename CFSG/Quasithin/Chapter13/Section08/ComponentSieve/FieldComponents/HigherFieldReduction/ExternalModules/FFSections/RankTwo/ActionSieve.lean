module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.FullList
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.UnitaryModels
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.MarkingRigidity
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity.LinearModels

/-!
# The complete rank-two FF action sieve

The faithful irreducible FF action is classified using the full universal
B.4.2 implication. Every even-degree unitary possibility is excluded through
an actual component isomorphism, retaining the quadratic matrix field and
the literal special-to-projective projection. In odd ternary linear degree,
the central quotient, two-part and two-rank comparisons exclude every other
model, including the binary symplectic and full/derived G₂ endpoints.

The surviving action retains its natural coordinates and ratio 1/2. The
central quotient comparison recovers the field cardinality; automorphism
alignment then gives natural or binary dual-natural coordinates under the
original projective marking. No filtered model list or naturality is assumed.
The F.9.18(6) extension argument is separate from this constituent sieve.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2,
printed pp.86–87, and proof of 13.8.20(a), printed pp.954–955.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

/-- Transport the complete component catalogue through an actual isomorphism. -/
theorem transport_quasisimpleModel {L R : Type*} [Group L] [Group R]
    (e : R ≃* L) (h : QuasisimpleModel L) : QuasisimpleModel R := by
  cases h with
  | linearTwo B a => exact .linearTwo B (e.trans a)
  | linearThree B a => exact .linearThree B (e.trans a)
  | symplecticFour B a => exact .symplecticFour B (e.trans a)
  | g2 B a => exact .g2 B (e.trans a)
  | g2DerivedTwo a => exact .g2DerivedTwo (e.trans a)
  | alternatingSix a => exact .alternatingSix (e.trans a)
  | alternatingSeven a => exact .alternatingSeven (e.trans a)
  | tripleSix z a =>
    exact .tripleSix ((centerCongr e).trans z) ((centralQuotientCongr e).trans a)
  | linearFourTwo a => exact .linearFourTwo (e.trans a)
  | linearFiveTwo a => exact .linearFiveTwo (e.trans a)

variable {F : Type} [Field F] [Finite F] {n : ℕ}

/-- Odd degree removes the scalar center before any action is compared. -/
theorem projectiveThree_center_eq_bot (ho : Odd n) (hF : Nat.card F = 2 ^ n) :
    center PSL(3,F) = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  intro g hg
  let e := slThreeEquivProjective hF ho
  have hz := (centerCongr e.symm ⟨g,hg⟩).property
  change e.symm g ∈ center SL(3,F) at hz
  have hz0 := mem_bot.mp ((slThree_center_eq_bot hF ho).le hz)
  exact mem_bot.mpr (e.symm.injective (hz0.trans e.symm.map_one.symm))

private def projectiveCenterEquiv (ho : Odd n) (hF : Nat.card F = 2 ^ n) :
    (PSL(3,F) ⧸ center PSL(3,F)) ≃* PSL(3,F) :=
  (QuotientGroup.quotientMulEquivOfEq (projectiveThree_center_eq_bot ho hF)).trans
    QuotientGroup.quotientBot

/-- Every non-SL₃ alternative is excluded on the actual odd-degree component.
The binary symplectic and full G₂ endpoints are included in the invariant calculation. -/
theorem not_otherModel_projectiveThree (hn : 1 < n) (ho : Odd n)
    (hF : Nat.card F = 2 ^ n) {L : Type*} [Group L] (e : L ≃* PSL(3,F)) :
    ¬ OtherModel L := by
  intro hm
  have eliminate {family q} (h : ComponentModel PSL(3,F) family q)
      (hne : family ≠ .linearThree) : False :=
    hne (pslThree_componentModel hn ho hF h).1
  let c : PSL(3,F) ≃* (L ⧸ center L) :=
    (projectiveCenterEquiv ho hF).symm.trans (centralQuotientCongr e).symm
  cases hm with
  | linearTwo B a =>
    exact eliminate (.linearTwo B.Carrier B.degree_pos B.card_eq
      (c.trans (centralQuotientCongr a))) (by decide)
  | symplecticFour B a =>
    have hp := (pslThree_invariants (by omega) hF).2
    have hq := (spFour_invariants B.degree_pos B.card_eq).2
    have he := Nat.card_congr (c.trans (centralQuotientCongr a)).toEquiv
    rw [he, hq] at hp
    obtain ⟨k,hk⟩ := ho
    omega
  | g2 B a =>
    have hp := (pslThree_invariants (by omega) hF).2
    have hq := (gTwo_invariants B.degree_pos B.card_eq).2
    rw [Nat.card_congr (e.symm.trans a).toEquiv, hq] at hp
    obtain ⟨k,hk⟩ := ho
    omega
  | g2DerivedTwo a => exact eliminate (.gTwoTwoDerived (e.symm.trans a)) (by decide)
  | alternatingSix a => exact eliminate (.alternatingSix (e.symm.trans a)) (by decide)
  | alternatingSeven a => exact eliminate (.alternatingSeven (e.symm.trans a)) (by decide)
  | tripleSix _ a => exact eliminate (.alternatingSix (c.trans a)) (by decide)
  | linearFourTwo a =>
    exact eliminate (.linearFourTwo (c.trans (centralQuotientCongr a))) (by decide)
  | linearFiveTwo a =>
    exact eliminate (.linearFiveTwo (c.trans (centralQuotientCongr a))) (by decide)

/-- An SL₃ action model has exactly the source field cardinality. -/
theorem natural_field_card (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n)
    {L : Type*} [Group L] (e : L ≃* PSL(3,F)) (B : BinaryField)
    (a : L ≃* SL(3,B.Carrier)) : Nat.card B.Carrier = Nat.card F := by
  let c := (projectiveCenterEquiv ho hF).symm.trans
    (centralQuotientCongr (e.symm.trans a))
  have h := (pslThree_componentModel hn ho hF
    (.linearThree B.Carrier B.degree_pos B.card_eq c)).2
  exact B.card_eq.trans (h.trans hF.symm)

universe u v
variable {E : Type u} [Group E] {U : Type v} [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) E U)

/-- The full action list, with all exceptional models checked, leaves the
natural SL₃ module over the recovered field and its exact quadratic ratio. -/
theorem natural_of_full_list (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n)
    {L H : Subgroup E} (e : L ≃* PSL(3,F)) (hc : IrreducibleActionCase σ L H) :
    ∃ B : BinaryField, Nat.card B.Carrier = Nat.card F ∧ H = L ∧
      Nonempty (ActionEquiv (σ.comp L.subtype) (linearNatural B 3)) ∧
      quadraticRatio σ = 1 / 2 := by
  rcases linearThree_or_other σ hc with ⟨B,hH,⟨a⟩,hq⟩ | hm
  · exact ⟨B,natural_field_card hn ho hF e B a.groupEquiv,hH,⟨a⟩,hq⟩
  · exact (not_otherModel_projectiveThree hn ho hF e hm).elim

variable [Finite E] [Finite U]

/-- Every case of B.4.2 contradicts an actual even-degree projective unitary
component, with the matrix field of order 2^(2*n). -/
theorem unitary_not_ff {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    (h : B4Hypotheses 𝒦 σ)
    {Q : Type*} [Field Q] [Finite Q]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 Q)
    {d : ℕ} (hd : 0 < d) (heven : Even d) (hQ : Nat.card Q = 2 ^ (2 * d))
    (hconj : ∀ x, J.conj x = x ^ (2 ^ d))
    (e : generalizedFitting E ≃*
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    ¬ IsFFModule σ := by
  intro hff
  obtain ⟨A,hA⟩ := h.exists_bestOffender hff
  exact unitary_not_quasisimpleModel_even J hd heven hQ hconj
    (transport_quasisimpleModel e.symm ((hB42 E U σ A hA).model σ))

/-- The genuine SU₃-to-PSU₃ comparison excludes the special carrier too. -/
theorem specialUnitary_not_ff {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    (h : B4Hypotheses 𝒦 σ)
    {Q : Type*} [Field Q] [Finite Q]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 Q)
    {d : ℕ} (hd : 0 < d) (heven : Even d) (hQ : Nat.card Q = 2 ^ (2 * d))
    (hconj : ∀ x, J.conj x = x ^ (2 ^ d))
    (e : generalizedFitting E ≃* J.specialSubgroup) : ¬ IsFFModule σ :=
  unitary_not_ff σ hB42 h J hd heven hQ hconj
    (e.trans (specialProjectiveEquivEven J heven hconj))

/-- Apply the complete universal B.4.2 implication to a faithful irreducible
FF action and retain natural coordinates, field size, and the generated subgroup. -/
theorem natural_of_ff {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    (h : B4Hypotheses 𝒦 σ) (hff : IsFFModule σ)
    (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n)
    (e : generalizedFitting E ≃* PSL(3,F)) :
    ∃ B : BinaryField, Nat.card B.Carrier = Nat.card F ∧
      offenderSubgroup σ = generalizedFitting E ∧
      Nonempty (ActionEquiv (σ.comp (generalizedFitting E).subtype) (linearNatural B 3)) ∧
      quadraticRatio σ = 1 / 2 := by
  obtain ⟨A,hA⟩ := h.exists_bestOffender hff
  exact natural_of_full_list σ hn ho hF e (hB42 E U σ A hA)

variable [Algebra (ZMod 2) F]

/-- The original projective marking, including its Borel, is preserved.
No naturality or field comparison is an input. -/
theorem naturalOrDual_of_ff {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    (h : B4Hypotheses 𝒦 σ) (hff : IsFFModule σ)
    (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n)
    (e : generalizedFitting E ≃* PSL(3,F)) :
    IsProjectiveNaturalOrDual ho hF
      ((σ.comp (generalizedFitting E).subtype).comp e.symm.toMonoidHom) := by
  obtain ⟨B,hB,_,⟨a⟩,_⟩ := natural_of_ff σ hB42 h hff hn ho hF e
  exact MarkingRigidity.actionEquiv_naturalOrDual ho hF hn _ B hB a e

/-- A compatible component and multiplicity map transfers the recognized
constituent to the specified action. Both maps are retained literally. -/
theorem naturalOrDual_of_ff_coordinates
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    (h : B4Hypotheses 𝒦 σ) (hff : IsFFModule σ)
    (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n)
    {K M : Type*} [Group K] [AddCommGroup M] [Module (ZMod 2) M]
    (μ : Representation (ZMod 2) K M) (e : K ≃* PSL(3,F))
    (a : generalizedFitting E ≃* K) (b : U ≃ₗ[ZMod 2] M)
    (hb : ∀ (g : generalizedFitting E) v, b (σ g v) = μ (a g) (b v)) :
    IsProjectiveNaturalOrDual ho hF (μ.comp e.symm.toMonoidHom) := by
  obtain ⟨B,hB,_,⟨c⟩,_⟩ := natural_of_ff σ hB42 h hff hn ho hF (a.trans e)
  let d : ActionEquiv μ (linearNatural B 3) := {
    groupEquiv := a.symm.trans c.groupEquiv
    linearEquiv := b.symm.trans c.linearEquiv
    intertwines := by
      intro k v
      change c.linearEquiv (b.symm (μ k v)) =
        linearNatural B 3 (c.groupEquiv (a.symm k)) (c.linearEquiv (b.symm v))
      rw [← c.intertwines]
      congr 1
      apply b.injective
      rw [b.apply_symm_apply]
      change μ k v = b (σ (a.symm k) (b.symm v))
      rw [hb, a.apply_symm_apply, b.apply_symm_apply] }
  exact MarkingRigidity.actionEquiv_naturalOrDual ho hF hn μ B hB d e

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo
