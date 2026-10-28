module
public import CFSG.Quasithin.ChapterB.Section02.RelativeThompsonFactors
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.ElementaryAbelian.Injective

/-!
# The moved four-group of a single relative Thompson factor

The stable relative family selects concrete factors in the solvable FF
classification. If its generated image is S₃, any selected factor has
the same order as the whole image and hence equals it. Its natural
support has dimension two. Literal commutator coordinates transfer this
to an order-four subgroup [V,⟨J(R)^G⟩] in the original group.

This supplies the module clause of Aschbacher–Smith 13.4.8(2), printed
p.905, after the local single-factor argument. No kernel or quotient
is silently replaced by a two-core quotient.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

private theorem stable_symmetricThree_moved_finrank
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W)
    (hsolv : Group.IsSolvable H) (hcore : pCore 2 H = ⊥)
    (hfaith : Function.Injective ρ) (hff : IsFFModule ρ)
    (P : Set (Subgroup H)) (hP : IsStable ρ P)
    (hmodel : Nonempty ((generatedBy P ⊤) ≃* Equiv.Perm (Fin 3))) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (generatedBy P ⊤)) = 2 := by
  obtain ⟨d⟩ := solvableFFStructure_nonempty ρ hsolv hcore hfaith hff
  let S := d.toSolvableFFFactors.stableFactorSet P
  obtain ⟨i,hi⟩ := d.toSolvableFFFactors.stableFactorSet_nonempty hfaith d.ratio_one hP
  have he : generatedBy P ⊤ = ⨆ i ∈ S, d.factor i :=
    d.toSolvableFFFactors.stable_generatedBy_eq hfaith d.ratio_one hP
  have hle : d.factor i ≤ generatedBy P ⊤ := by
    rw [he]
    exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
  obtain ⟨e⟩ := hmodel
  have hcard : Nat.card (generatedBy P ⊤) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have heq : d.factor i = generatedBy P ⊤ := eq_of_le_of_card_ge hle (by
    rw [hcard, d.toSolvableFFFactors.factor_card])
  rw [← heq]
  exact d.toSolvableFFFactors.support_finrank i

/-- A single symmetric-three relative Thompson factor moves a literal four-group. -/
theorem relative_thompson_span_commutator_card
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V] (hVR : V ≤ R)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hJ : ¬ elementaryAbelianMaxJ R ≤ q.ker)
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 H = ⊥)
    (hmodel : Nonempty (((conjugateSpanBy (elementaryAbelianMaxJ R) ⊤).map q) ≃*
      Equiv.Perm (Fin 3))) :
    Nat.card (⁅V,conjugateSpanBy (elementaryAbelianMaxJ R) ⊤⁆ : Subgroup G) = 4 := by
  let := hsolv
  let ρ := NormalElementaryQuotient.representation V q hq hker
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) ⊤
  have hs := lemma_B_2_10_relative V R hVR q hq hker hJ
  have hfaith : Function.Injective ρ :=
    NormalElementaryQuotient.representation_injective V q hq hker
  have he := relative_thompson_span_image V R hVR q hq hker hJ
  have hm : Nonempty ((generatedBy (relativeMaxOffenderImages R V q) ⊤) ≃*
      Equiv.Perm (Fin 3)) := he ▸ hmodel
  have hf := stable_symmetricThree_moved_finrank ρ (Group.isSolvable_of_surjective hq)
    hcore hfaith hs.1 _ hs.2.1 hm
  rw [← he] at hf
  let : IsElementaryAbelian 2 (⁅V,I⁆ : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion (commutator_le_left V I))
      (inclusion_injective _)
  have hc : Module.finrank (ZMod 2) (Additive (⁅V,I⁆ : Subgroup G)) = 2 := by
    rw [(NormalElementaryQuotient.movedEquiv V q hq hker I).finrank_eq]
    exact hf
  change Nat.card (Additive (⁅V,I⁆ : Subgroup G)) = 4
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hc]
  rfl

end CFSG.Quasithin.ChapterB
