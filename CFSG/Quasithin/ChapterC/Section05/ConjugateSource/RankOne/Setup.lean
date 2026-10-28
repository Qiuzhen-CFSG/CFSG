module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Transport
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Lifting
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Covers
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal

/-!
# The rank-one data preceding C.5.6

The selected block is one of the original C.5.3 blocks. The Baumann group
normalizes it and its actual two-core is its module centralizer, by C.5.4.
The marked action retains the full module and its central quotient; the
quotient of the block extended by S is SL₂ with the full upper-root image.
In the A₃ case this is SL₂(2), although the block quotient itself is A₃.
No normalization by the whole Sylow subgroup, split cover, conjugate span,
or factorization is included.

Source: Aschbacher–Smith, C.5.3–4 and C.5.6, printed pp.155–157.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] {F : Type*} [Field F]

structure Setup (R L : Subgroup G) (F : Type*) [Field F] where
  coordinates : ActionCoordinates R L F
  block : (∃ n, IsL2EvenBlock L n ∧ coordinates.IsInternal) ∨ IsAlternatingBlock L 3
  module_le : U L ≤ S R
  normalizes : S R ≤ normalizer (L : Set G)
  core : Q R L = S R ⊓ centralizer (U L : Set G)
  quotient : (L ⊔ S R : Subgroup G) →* Matrix.SpecialLinearGroup (Fin 2) F
  surjective : Function.Surjective quotient
  kernel : quotient.ker = (Q R L).subgroupOf (L ⊔ S R)
  image : ((S R).subgroupOf (L ⊔ S R)).map quotient =
    Matrix.SpecialLinearGroup.upperUnipotent F

variable {R L : Subgroup G}
theorem Setup.short (h : Setup R L F) : IsShort L := by
  rcases h.block with ⟨n, hn, _⟩ | ha
  · exact hn.2.1
  · exact ha.2.1

theorem Setup.elementary (h : Setup R L F) : IsElementaryAbelian 2 (U L) := by
  let := h.short.elementary
  exact IsElementaryAbelian.map L.subtype

/-- Intrinsic central-cover lifting applies to the original Baumann action. -/
theorem Setup.fixedLift (h : Setup R L F) : h.coordinates.FixedLift := by
  rcases h.block with ⟨n, hn, hi⟩ | ha
  · exact fixedLift_of_linearCover h.coordinates linearCoverInput hn hi
  · exact fixedLift_of_blockFixed_eq_bot h.coordinates (alternatingThreeCoverInput L ha)

/-- The original right conjugator normalizes the Baumann group. -/
theorem Setup.stable (_h : Setup R L F) {x : G} (hx : x ∈ normalizer (R : Set G)) :
    (S R).map (MulAut.conj x⁻¹).toMonoidHom = S R :=
  mem_normalizer_iff_map_conj_eq.mp
    (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx))

theorem Setup.conjugate_le (h : Setup R L F) {x : G} (hx : x ∈ normalizer (R : Set G)) :
    (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ S R :=
  (map_mono h.module_le).trans_eq (h.stable hx)

theorem Setup.conjugate_normalized (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G)) :
    S R ≤ normalizer ((U L).map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
  rw [← map_equiv_normalizer_eq, ← h.stable hx]
  exact map_mono h.coordinates.normalizes

theorem Setup.module_le_core (h : Setup R L F) : U L ≤ Q R L := by
  let := h.elementary
  rw [h.core]
  exact le_inf h.module_le (le_centralizer_iff_isMulCommutative.mpr inferInstance)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
