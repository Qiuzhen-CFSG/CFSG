module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.Construction.StandardModel
public import Theory.LinearAlgebra.Hermitian.ProjectivePairTransport

/-!
# Reduction to a concrete PGU embedding and its socle conjugacy

Choose one PGU₃ over GF(q²) with the identity Hermitian form. A simultaneous
PSU/PGU field-and-form equivalence transfers its embedding to the supplied
Hermitian form. Conjugating the resulting embedding sends its special image
to the exact supplied subgroup of the Ree group. No marking of the supplied
socle equivalence is required to extend.

The assembly is conditional: constructing the standard embedding from the
Ree root matrices and proving its socle-conjugacy property are separate
geometric obligations. This module does not yet prove
`unitaryEmbeddingExtensions`.

Source: Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E; case 7 of the unconditional list inside the
proof of Theorem 5 of Himstedt–Nguyen–Tiep, arXiv:0910.4758, p.3.
-/

public noncomputable section

namespace ReeF4.MaximalSubgroups.SimpleNormal

open Subgroup Matrix BenderSuzuki.MatrixGroups Construction

private def restrictEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (U : Subgroup G) (V : Subgroup H)
    (h : ∀ x, e x ∈ V ↔ x ∈ U) : U ≃* V where
  toFun x := ⟨e x, (h x).2 x.property⟩
  invFun x := ⟨e.symm x, (h _).1 (by simp)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp

private theorem extension_of_conjugate_pair
    {G : Type*} [Group G] (S : Subgroup G)
    {F E : Type*} [Field F] [Field E]
    (J : HermitianForm 3 F) (K : HermitianForm 3 E)
    (j : K.unitarySubgroup.map ProjGenLinGroup.mk →* G)
    (hj : Function.Injective j)
    (e : ProjGenLinGroup (Fin 3) F ≃* ProjGenLinGroup (Fin 3) E)
    (hu : ∀ x, e x ∈ K.unitarySubgroup.map ProjGenLinGroup.mk ↔
      x ∈ J.unitarySubgroup.map ProjGenLinGroup.mk)
    (hs : ∀ x, e x ∈ ProjectiveSpecialUnitaryMatrixGroup K ↔
      x ∈ ProjectiveSpecialUnitaryMatrixGroup J)
    (g : G)
    (hg : ((j.comp (projectiveSpecialInclusion K)).range).map
      (MulAut.conj g).toMonoidHom = S) : Nonempty (ProjectiveExtension S J) := by
  let u := restrictEquiv e _ _ hu
  let s := restrictEquiv e _ _ hs
  have he : (j.comp u.toMonoidHom).comp (projectiveSpecialInclusion J) =
      (j.comp (projectiveSpecialInclusion K)).comp s.toMonoidHom := by
    ext x
    rfl
  have hr : ((j.comp u.toMonoidHom).comp (projectiveSpecialInclusion J)).range =
      (j.comp (projectiveSpecialInclusion K)).range := by
    have hsrange : s.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr s.surjective
    rw [he, MonoidHom.range_comp, hsrange, ← MonoidHom.range_eq_map]
  refine ⟨{
    embedding := (MulAut.conj g).toMonoidHom.comp (j.comp u.toMonoidHom)
    injective := (MulAut.conj g).injective.comp (hj.comp u.injective)
    socle_range_eq := ?_ }⟩
  change ((MulAut.conj g).toMonoidHom.comp
    ((j.comp u.toMonoidHom).comp (projectiveSpecialInclusion J))).range = S
  rw [MonoidHom.range_comp, hr, hg]

/-- A standard projective embedding and its socle-conjugacy property suffice.
Both geometric premises must be proved before the unconditional extension
theorem can be asserted. Field, form and subgroup-range transport are
discharged here. -/
theorem unitaryEmbeddingExtensions_of_standard_embedding_and_conjugacy
    (hEmbedding : StandardProjectiveEmbeddings)
    (hConjugacy : StandardSocleConjugacy) : UnitaryEmbeddingExtensions := by
  intro m hm M hM hsolv hR S hSn hSs hSa hC F _ _ J hcard hconj e
  obtain ⟨j, hj⟩ := hEmbedding m hm
  obtain ⟨g, hg⟩ :=
    hConjugacy m hm M hM hsolv hR S hSn hSs hSa hC F J hcard hconj e j hj
  have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ (2 * m + 1) :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 (2 * m + 1)
      (by omega) hcard hconj
  obtain ⟨f, hu, hs⟩ :=
    HermitianForm.ProjectivePairTransport.exists_projective_pair_equiv_of_card
      J (standardForm m) (2 ^ (2 * m + 1)) hcard hfixed
      (standardField_card m) (standardForm_fixed_card m)
  exact extension_of_conjugate_pair (S.map M.subtype) J (standardForm m)
    j hj f hu hs g hg

end ReeF4.MaximalSubgroups.SimpleNormal
