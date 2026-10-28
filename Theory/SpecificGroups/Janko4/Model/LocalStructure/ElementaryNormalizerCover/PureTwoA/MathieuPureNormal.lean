module
public import Theory.Quasithin.Rank
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuBranch
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.NormalFour
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ExtraspecialReduction

/-!
# Pure first-class subgroups cannot be normal in the Mathieu local

A normal elementary two-subgroup of the literal max1 subgroup lies in its
certified binary kernel. The two nonidentity kernel orbits have sizes 276 and
1771. Purity excludes the second-class seed orbit. Containing the first-class
orbit forces the subgroup, whose order divides 2048, to equal the full kernel;
this again contains the second-class seed. Thus the subgroup is trivial.

For a nontrivial pure elementary subgroup, whole-normalizer containment in
any conjugate of max1 consequently contradicts maximality among TWO-locals.
The conjugation argument retains the original ambient matrix model.

This supplies the maximal-two-local consequence of the trivial-image branch
in Kleidman--Wilson (1988), Section 2.1, pp.488--489, directly from the native
kernel orbit certificates. It assumes no printed MOG coordinate marking or
exhaustive local cover.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA
open Cardinality
open Simplicity.Max1Fusion
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
set_option backward.isDefEq.respectTransparency true

/-- A normal elementary subgroup of max1 pure in the ambient first class is trivial. -/
theorem mathieu_pure_normal_eq_bot (V : Subgroup max1) [V.Normal]
    [IsElementaryAbelian 2 V]
    (hpure : ∀ x ∈ V, x ≠ 1 → IsConj a (x : Model)) : V = ⊥ := by
  by_contra hne
  have hVK : V ≤ localKernel matrixA_mul_self matrixB_pow_four := by
    rw [localKernel_eq_twoCore]
    exact le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 V⟩
  have hseed : (localKernelSeed matrixA_mul_self matrixB_pow_four : max1) ∉ V := by
    intro hs
    apply first_not_isConj_second
    apply hpure _ hs
    intro he
    have hh : localKernel matrixA_mul_self matrixB_pow_four = ⊥ := by
      unfold localKernel
      rw [he]
      simp
    exact localKernel_ne_bot _ _ hh
  obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hz' : (z : max1) ≠ 1 := fun he => hz (Subtype.ext he)
  obtain ⟨g,hg | hg⟩ := kernel_nonidentity_orbits matrixA_mul_self matrixB_pow_four
    z (hVK z.property) hz'
  · apply hseed
    rw [hg]
    exact Normal.conj_mem inferInstance (z : max1) z.property g
  · have hs : Max1RelativeRigidity.v ∈ V := by
      rw [show Max1RelativeRigidity.v = g * z * g⁻¹ from hg]
      exact Normal.conj_mem inferInstance (z : max1) z.property g
    have hsub : MulAction.orbit (ConjAct Max1RelativeRigidity.M)
        Max1RelativeRigidity.v ⊆ (V : Set max1) := by
      rintro w ⟨b,rfl⟩
      exact Normal.conj_mem inferInstance _ hs b.ofConjAct
    have hlo := Nat.card_le_card_of_injective _ (Set.inclusion_injective hsub)
    change Nat.card (MulAction.orbit (ConjAct Max1RelativeRigidity.M)
      Max1RelativeRigidity.v) ≤ Nat.card V at hlo
    rw [Max1RelativeRigidity.pair_orbit_card] at hlo
    have hdvd := card_dvd_of_le hVK
    rw [localKernel_card] at hdvd
    have hecard : Nat.card V = 2048 := by
      obtain ⟨k,hk⟩ := hdvd
      have hkpos : 0 < k := by nlinarith
      have hkone : k = 1 := by
        by_contra hk1
        have hk2 : 2 ≤ k := by omega
        nlinarith
      simpa [hkone] using hk.symm
    have he : V = localKernel matrixA_mul_self matrixB_pow_four :=
      eq_of_le_of_card_ge hVK (by rw [localKernel_card,hecard])
    apply hseed
    rw [he]
    exact localKernelSeed_mem _ _

/-- A nontrivial pure elementary subgroup cannot have max1 as its whole normalizer. -/
theorem pure_normalizer_ne_max1 (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hne : X ≠ ⊥) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    normalizer (X : Set Model) ≠ max1 := by
  intro he
  have hXM : X ≤ max1 := X.le_normalizer.trans he.le
  let : (X.subgroupOf max1).Normal :=
    (normal_subgroupOf_iff_le_normalizer hXM).mpr he.ge
  let : IsElementaryAbelian 2 (X.subgroupOf max1) := IsElementaryAbelian.subgroupOf hXM
  have hbot := mathieu_pure_normal_eq_bot (X.subgroupOf max1) (by
    intro x hx hx1
    exact hpure x hx (fun hh => hx1 (Subtype.ext hh)))
  apply hne
  rw [← map_subgroupOf_eq_of_le hXM,hbot,Subgroup.map_bot]

/-- Whole-normalizer containment in max1 rules out maximal TWO-locality for pure groups. -/
theorem pure_normalizer_not_maximal_of_le_max1 (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hne : X ≠ ⊥)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hN : normalizer (X : Set Model) ≤ max1) :
    ¬ IsMaximalTwoLocal (normalizer (X : Set Model)) := by
  intro hmax
  exact pure_normalizer_ne_max1 X hne hpure
    (hmax.eq_of_le embedded_localKernel_isTwoLocal hN)

/-- The same obstruction holds for every literal ambient conjugate of max1. -/
theorem pure_normalizer_ne_mathieu_conjugate (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hne : X ≠ ⊥)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x) (g : Model) :
    normalizer (X : Set Model) ≠ max1.map (MulAut.conj g).toMonoidHom := by
  intro he
  let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hYne : Y ≠ ⊥ := by
    intro hbot
    exact hne ((map_eq_bot_iff_of_injective X (MulAut.conj g⁻¹).injective).mp hbot)
  have hYpure : ∀ y ∈ Y, y ≠ 1 → IsConj a y := by
    rintro y ⟨x,hx,rfl⟩ hy
    have hx1 : x ≠ 1 := by intro hx1; exact hy (by rw [hx1,map_one])
    exact (hpure x hx hx1).trans (isConj_iff.mpr ⟨g⁻¹,rfl⟩)
  apply pure_normalizer_ne_max1 Y hYne hYpure
  rw [show Y = X.map (MulAut.conj g⁻¹).toMonoidHom from rfl,
    ← map_equiv_normalizer_eq,he,map_map]
  have hc : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Model := by ext x; simp [mul_assoc]
  rw [hc,map_id]

/-- Pure whole-normalizer containment in a Mathieu conjugate is never maximal TWO-local. -/
theorem pure_normalizer_not_maximal_of_mathieu_containment (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hne : X ≠ ⊥)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x) (g : Model)
    (hN : normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom) :
    ¬ IsMaximalTwoLocal (normalizer (X : Set Model)) := by
  intro hmax
  exact pure_normalizer_ne_mathieu_conjugate X hne hpure g
    (hmax.eq_of_le (embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj g)) hN)

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA
