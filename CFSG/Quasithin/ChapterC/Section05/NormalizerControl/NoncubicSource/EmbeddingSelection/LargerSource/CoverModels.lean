module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SourceParameters
public import GorensteinWalter.PSL2EvenDefiningKernel
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.GroupTheory.Commutator.TwoCoverComparison
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
/-!
# The actual binary short-image cover alternatives

A finite quasisimple group with binary PSL₂ two-core quotient is that
simple group, except at field order four where a nontrivial central
two-cover is the actual SL₂(5) model. The even-field defining-kernel
calculation excludes every larger field; the perfect central-cover
comparison identifies the exceptional image with its original kernel.
This retains the central two-cover needed in the natural C.5.12 branch.
Source: Aschbacher–Smith I.1.3–4 and C.5.12, printed pp.407–408,163.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02.LocalModels
variable {B : Type*} [Group B] [Finite B] [IsQuasisimple B]
theorem quasisimple_binary_core_models {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) :
    ClassicalGroup.IsPSL B 2 (2^n) ∨ n = 2 ∧ IsSL B 2 5 := by
  by_cases hb : pCore 2 B = ⊥
  · let e : (B ⧸ pCore 2 B) ≃* B :=
      (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
    exact .inl (hm.of_mulEquiv e.symm)
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let f : B →* PSL(2,F) := eF.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  have hf : Function.Surjective f := eF.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 B := by
    rw [MonoidHom.ker_comp_of_injective _ _ eF.injective,QuotientGroup.ker_mk']
  have hcentral : f.ker ≤ center B := hk ▸ IsQuasisimple.pCore_le_center 2
  have hn2 : n = 2 := by
    by_contra hn2
    have hlarge : 8 ≤ Nat.card F := by
      rw [hF]
      exact (by decide : 8 ≤ 2^3).trans (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega))
    have heven : Even (Nat.card F) := by
      rw [hF]
      exact (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega)))
    have hc : ringChar F = 2 := by
      let : Fintype F := Fintype.ofFinite F
      apply FiniteField.even_card_iff_char_two.mpr
      simpa only [← Nat.card_eq_fintype_card] using Nat.even_iff.mp heven
    have hnot := GorensteinWalter.PSL2Cover.defining_prime_not_dvd_kernel_of_even F heven hlarge f hf hcentral
    rw [hc,hk] at hnot
    obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
    have hm0 : m = 0 := by
      by_contra hm0
      exact hnot (hm ▸ dvd_pow_self 2 hm0)
    apply hb
    apply Subgroup.card_eq_one.mp
    simpa [hm0] using hm
  subst n
  have hF4 : Nat.card F = 4 := by simpa using hF
  obtain ⟨e4⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF4
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  let e : (B ⧸ pCore 2 B) ≃* PSL(2,ZMod 5) := (eF.trans e4).trans e5.symm
  let q : B →* PSL(2,ZMod 5) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = pCore 2 B := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hqcentral : q.ker ≤ center B := hqk ▸ IsQuasisimple.pCore_le_center 2
  have hq2 : IsPGroup 2 q.ker := hqk ▸ pCore_isPGroup
  have hqn : q.ker ⊓ _root_.commutator B ≠ ⊥ := by
    rw [Group.IsPerfect.commutator_eq_top,inf_top_eq,hqk]
    exact hb
  obtain ⟨hg,hgc,hgcard,hg2,hperfect,hdihedral⟩ :=
    GorensteinWalter.sl2_projective_cover_model (ZMod 5) (by norm_num) (by norm_num)
  let : Group.IsPerfect SL(2,ZMod 5) := hperfect
  obtain ⟨ec⟩ := CentralExtension.commutator_mulEquiv_of_central_two_covers
    q (GorensteinWalter.sl2ProjectiveProjection (ZMod 5)) hq hg hqcentral hgc hq2 hg2 hqn hgcard hdihedral
  refine .inr ⟨rfl,ZMod 5,inferInstance,inferInstance,Nat.card_zmod 5,?_⟩
  exact ⟨(Subgroup.topEquiv.symm.trans
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm)).trans ec⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
