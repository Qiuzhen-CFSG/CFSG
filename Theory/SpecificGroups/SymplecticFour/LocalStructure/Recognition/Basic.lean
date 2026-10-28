module

public import Theory.Representation.SL2NaturalFirstCohomology
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PResidual.Defs

/-!
# Recognition of natural elementary abelian extensions

An explicit surjection onto SL₂ and its actual conjugation module identify
the two-core, prove perfectness, and determine the generalized Fitting subgroup.
Faithfulness gives a self-centralizing kernel. The component dichotomy and the
nonabelian simple quotient then control all of the generalized Fitting subgroup.

Source: Aschbacher–Smith, C.1.7/C.1.12 and F.1.12(I)(2), printed pp.123–124
and 262–264. The finite-field parameter argument follows the existing proof in
`GorensteinWalter/SL2ProjectiveCover.lean`, without its odd-field dependencies.
-/

@[expose] public section

open Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.SpecificGroups.SymplecticFour

variable {F L : Type*} [Field F] [Group L]

/-- The actual conjugate inside a normal subgroup. -/
def extensionConjugate (Q : Subgroup L) [Q.Normal] (l : L) (u : Q) : Q :=
  ⟨l * (u : L) * l⁻¹, (inferInstance : Q.Normal).conj_mem u u.property l⟩

/-- Explicit extension and equivariant natural-module data. -/
structure NaturalExtension (Q : Subgroup L) [Q.Normal] where
  elementary : IsElementaryAbelian 2 Q
  projection : L →* Matrix.SpecialLinearGroup (Fin 2) F
  surjective : Function.Surjective projection
  kernel : projection.ker = Q
  commutator_eq : ⁅Q, ⊤⁆ = Q
  moduleIso : (Q ⧸ (Subgroup.center L).subgroupOf Q) ≃* Multiplicative (Fin 2 → F)
  intertwining : ∀ (l : L) (u : Q),
    Multiplicative.toAdd (moduleIso (QuotientGroup.mk'
      ((Subgroup.center L).subgroupOf Q) (extensionConjugate Q l u))) =
    Matrix.mulVec (projection l).val (Multiplicative.toAdd
      (moduleIso (QuotientGroup.mk' ((Subgroup.center L).subgroupOf Q) u)))

namespace NaturalExtension
variable {Q : Subgroup L} [Q.Normal] (d : NaturalExtension (F := F) Q)
include d

/-- A perfect quotient and a commutator-generated kernel force perfectness. -/
theorem perfect_of_quotient [Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F)] :
    Group.IsPerfect L := by
  have hle : Q ≤ commutator L := by
    rw [← d.commutator_eq]
    exact Subgroup.commutator_mono le_top le_rfl
  have hm : (commutator L).map d.projection = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ d.surjective]
    exact Group.IsPerfect.commutator_eq_top
  have hh := congrArg (Subgroup.comap d.projection) hm
  rw [Subgroup.comap_map_eq, d.kernel, sup_eq_left.mpr hle, Subgroup.comap_top] at hh
  exact ⟨hh⟩

/-- The centralizer of the kernel is exactly the kernel, by faithfulness. -/
theorem centralizer_eq : Subgroup.centralizer (Q : Set L) = Q := by
  let := d.elementary
  apply le_antisymm
  · intro l hl
    rw [← d.kernel, MonoidHom.mem_ker]
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    obtain ⟨x, hx⟩ := d.moduleIso.surjective (Multiplicative.ofAdd v)
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective ((Subgroup.center L).subgroupOf Q) x
    have hc : extensionConjugate Q l u = u := by
      apply Subtype.ext
      change l * (u : L) * l⁻¹ = u
      rw [← (Subgroup.mem_centralizer_iff.mp hl u u.property), mul_inv_cancel_right]
    have hi := d.intertwining l u
    rw [hc, hx] at hi
    simpa using hi.symm
  · intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact congrArg Subtype.val (mul_comm (⟨u, hu⟩ : Q) ⟨l, hl⟩)

variable [Finite F] [CharP F 2]

omit d in
private theorem field_parameter (hF : 2 < Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  let := Fintype.ofFinite F
  by_contra h
  push Not at h
  have hs : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have he : a = 1 := CharTwo.sq_injective (by simpa using h a ha)
      simp [he]
  have hc := Finset.card_le_card hs
  have hb : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
  have : Nat.card F ≤ 2 := by simpa using hc.trans hb
  omega

omit d in
/-- The actual special linear group is perfect for the nonbinary parameters. -/
theorem model_perfect (hF : 2 < Nat.card F) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨a, ha, hs⟩ := field_parameter hF
  exact ⟨Matrix.SL2.commutator_eq_top ha hs⟩

omit d in
/-- Characteristic two removes the scalar center from the simple projective group. -/
theorem model_simple (hF : 2 < Nat.card F) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' (field_parameter hF)
  exact (MulEquiv.isSimpleGroup_congr
    (Representation.SL2NaturalH1.projectiveEquiv (K := F))).mp inferInstance

/-- Perfectness of the extension is derived, not supplied. -/
theorem perfect (hF : 2 < Nat.card F) : Group.IsPerfect L := by
  let := model_perfect hF
  exact d.perfect_of_quotient

variable [Finite L]

omit [Finite L] in
private theorem nilpotent_normal_le (hF : 2 < Nat.card F)
    (N : Subgroup L) [N.Normal] [Group.IsNilpotent N] : N ≤ Q := by
  let := model_perfect hF
  let := model_simple hF
  let : (N.map d.projection).Normal := (inferInstance : N.Normal).map d.projection d.surjective
  rcases (inferInstance : (N.map d.projection).Normal).eq_bot_or_eq_top with hb | ht
  · rw [← d.kernel]
    exact (Subgroup.map_eq_bot_iff N).mp hb
  · have hs : Function.Surjective (d.projection.comp N.subtype) := by
      intro g
      have : g ∈ N.map d.projection := ht ▸ Subgroup.mem_top g
      obtain ⟨l, hl, rfl⟩ := this
      exact ⟨⟨l, hl⟩, rfl⟩
    exact (Group.IsPerfect.not_isNilpotent (Matrix.SpecialLinearGroup (Fin 2) F)
      (Group.nilpotent_of_surjective _ hs)).elim

/-- The elementary abelian kernel is the full two-core. -/
theorem core_eq (hF : 2 < Nat.card F) : pCore 2 L = Q := by
  let := d.elementary
  let : Group.IsNilpotent (pCore 2 L) := pCore_isNilpotent
  exact le_antisymm (d.nilpotent_normal_le hF (pCore 2 L))
    (le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 Q⟩)

/-- The first isomorphism theorem for the actual two-core. -/
noncomputable def quotientIso (hF : 2 < Nat.card F) :
    (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.quotientMulEquivOfEq ((d.core_eq hF).trans d.kernel.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.projection d.surjective)

@[simp] theorem quotientIso_mk (hF : 2 < Nat.card F) (l : L) :
    d.quotientIso hF (QuotientGroup.mk' (pCore 2 L) l) = d.projection l := rfl

/-- The Fitting subgroup maps trivially into the simple nonabelian quotient;
components centralize the abelian kernel or are contained in it. -/
theorem generalizedFitting_eq (hF : 2 < Nat.card F) :
    generalizedFitting L = pCore 2 L := by
  apply le_antisymm
  · rw [d.core_eq hF, generalizedFitting]
    refine sup_le (d.nilpotent_normal_le hF (fittingSubgroup L)) ?_
    apply sSup_le
    intro K hK
    rcases hK.normal_dichotomy Q with h | h
    · exact h
    · simpa [d.centralizer_eq] using
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  · exact (pCore_le_fitting L 2).trans (fitting_le_generalizedFitting L)

/-- The quotient is genuinely quasisimple, in fact simple. -/
theorem quotient_quasisimple (hF : 2 < Nat.card F) :
    IsQuasisimple (L ⧸ pCore 2 L) := by
  let := model_perfect hF
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' (field_parameter hF)⟩
  exact IsQuasisimple.of_mulEquiv (d.quotientIso hF).symm

/-- No nontrivial two-group quotient survives perfectness. -/
theorem twoPerfect (hF : 2 < Nat.card F) : IsPPerfect 2 L := by
  let := d.perfect hF
  intro N hN hp
  let := hN
  apply top_unique
  intro l _
  apply (QuotientGroup.eq_one_iff l).mp
  by_contra h
  have : Nontrivial (L ⧸ N) := ⟨⟨QuotientGroup.mk l, 1, h⟩⟩
  exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hp.isNilpotent

end NaturalExtension
end Theory.SpecificGroups.SymplecticFour
