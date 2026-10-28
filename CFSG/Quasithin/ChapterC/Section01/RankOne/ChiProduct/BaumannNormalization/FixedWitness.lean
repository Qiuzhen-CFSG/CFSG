module
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Fixed witnesses prevent Baumann permutation of commuting factors

An elementary Thompson-fixed subgroup inside R lies in the omega center
of J(R). Its vectors are fixed by Baum(R). A vector in one factor which
does not centralize that factor cannot also lie in a distinct commuting
factor, so every Baumann element fixes the factor. For a module with
trivial fixed layer, the requisite witness follows from the two-group
fixed-point congruence.

Source: Aschbacher--Smith C.1.16(2), printed pp.125--126; the application
to the block orbit is C.5.4(1), printed p.155.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BaumannNormalization
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normalizes_of_moved (R K : Subgroup G)
    (h : K = ⁅K,elementaryAbelianMaxJ R⁆) :
    elementaryAbelianMaxJ R ≤ normalizer K :=
  le_normalizer_iff_commutator_le_left.mpr h.ge

omit [Finite G] in
theorem normalizes_of_alpha_witness {ι : Type*} (R : Subgroup G)
    (K : ι → Subgroup G)
    (hperm : ∀ g ∈ R, ∀ i, ∃ j, (K i).map (MulAut.conj g).toMonoidHom = K j)
    (hcomm : Pairwise fun i j => ⁅K i,K j⁆ = ⊥)
    (i : ι) (hw : ∃ u ∈ K i, u ∈ ChapterB.thompsonAlpha R ∧
      u ∉ centralizer (K i : Set G)) :
    ChapterB.baumann R ≤ normalizer (K i) := by
  obtain ⟨u,hu,hua,huc⟩ := hw
  intro g hg
  obtain ⟨j,hj⟩ := hperm g hg.1 i
  have hfix : g*u*g⁻¹=u :=
    mul_inv_eq_iff_eq_mul.mpr (hg.2 u hua).symm
  have huj : u ∈ K j := by
    rw [←hj,←hfix]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom hu
  have hij : i=j := by
    by_contra hn
    exact huc ((commutator_eq_bot_iff_le_centralizer.mp (hcomm (Ne.symm hn))) huj)
  exact mem_normalizer_iff_map_conj_eq.mpr (hij ▸ hj)

theorem normalizes_of_fixed_witness {ι : Type*} (R : Subgroup G)
    (K : ι → Subgroup G)
    (hperm : ∀ g ∈ R, ∀ i, ∃ j, (K i).map (MulAut.conj g).toMonoidHom = K j)
    (hcomm : Pairwise fun i j => ⁅K i,K j⁆ = ⊥)
    (i : ι) (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hUR : U ≤ R) (hUK : U ≤ K i)
    (hw : ¬ U ⊓ centralizer (elementaryAbelianMaxJ R : Set G) ≤
      centralizer (K i : Set G)) :
    ChapterB.baumann R ≤ normalizer (K i) := by
  apply normalizes_of_alpha_witness R K hperm hcomm i
  obtain ⟨u,hu,huc⟩ := SetLike.not_le_iff_exists.mp hw
  let : IsElementaryAbelian 2 ↥(U ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) :=
    IsElementaryAbelian.of_le inf_le_left
  exact ⟨u,hUK hu.1,
    elementary_centralizer_maxJ_le_omegaCenter R _ (inf_le_left.trans hUR) inf_le_right hu,huc⟩

theorem fixed_noncentral_of_trivial_center (R U K : Subgroup G)
    (hR : IsPGroup 2 R) [IsElementaryAbelian 2 U]
    (hne : U ≠ ⊥) (hn : elementaryAbelianMaxJ R ≤ normalizer U)
    (hcen : U ⊓ centralizer (K : Set G) = ⊥) :
    ¬ U ⊓ centralizer (elementaryAbelianMaxJ R : Set G) ≤ centralizer (K : Set G) := by
  intro hc
  have hzero : U ⊓ centralizer (elementaryAbelianMaxJ R : Set G) = ⊥ :=
    bot_unique ((le_inf inf_le_left hc).trans_eq hcen)
  have hpJ : IsPGroup 2 (elementaryAbelianMaxJ R) :=
    hR.to_le (sSup_le fun A hA => hA.1)
  have hcmod := card_modEq_card_inf_centralizer (elementaryAbelianMaxJ R) U hpJ hn
  rw [hzero,card_bot] at hcmod
  have hdiv : 2 ∣ Nat.card U := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
    have hn0 : n ≠ 0 := by
      intro hz
      rw [hz,pow_zero] at hn
      exact hne (Subgroup.card_eq_one.mp hn)
    rw [hn]
    exact dvd_pow_self 2 hn0
  simp [Nat.ModEq, Nat.mod_eq_zero_of_dvd hdiv] at hcmod
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BaumannNormalization
