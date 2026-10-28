module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.Sylow
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.Bruhat
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.StandardOvergroups
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# The solvable Sylow overgroup in GL₄(2)

Conjugate a supplied Sylow subgroup to the standard full-flag stabilizer.
The checked Bruhat exhaustion identifies its overgroups with partial-flag
stabilizers. A one-space or three-space stabilizer has a two-group kernel
and diagonal quotient GL₁(2) × GL₃(2), whose order is not divisible by nine.
Thus an overgroup with order divisible by nine can retain only the plane
cut. Solvability excludes the empty flag, since GL₄(2) is nontrivial and
perfect. The singleton-cut stabilizer is maximal by the same exhaustion.

Source: Aschbacher–Smith, 15.3.24, first two paragraphs of the proof,
combined manuscript (1 March 2004), printed p.1129. This argument needs
no assertion about the outer or diagram action.
-/

public section
open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation.PlaneGeometry
open FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
open FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four

private instance : Finite (LinearGroup 4) := Finite.of_injective
  (fun g : LinearGroup 4 => (g : Space 4 → Space 4)) DFunLike.coe_injective

private theorem linearGroup_card_formula (n : ℕ) :
    Nat.card (LinearGroup n) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp

private theorem solvable_ne_top (B : Subgroup (LinearGroup 4))
    (hs : Group.IsSolvable B) : B ≠ ⊤ := by
  intro ht
  let : Group.IsSolvable (⊤ : Subgroup (LinearGroup 4)) := ht ▸ hs
  let : Group.IsSolvable (LinearGroup 4) :=
    Group.isSolvable_of_surjective (f := (Subgroup.topEquiv :
      (⊤ : Subgroup (LinearGroup 4)) ≃* LinearGroup 4).toMonoidHom) Subgroup.topEquiv.surjective
  let : Group.IsPerfect (LinearGroup 4) := linearGroup_isPerfect 4 (by decide)
  let : Nontrivial (LinearGroup 4) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [linearGroup_card_formula]
    decide
  exact Group.IsPerfect.not_isSolvable (LinearGroup 4) inferInstance

private theorem nine_not_dvd_endpoint (W : Submodule (ZMod 2) (Space 4))
    (hdim : Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 3) :
    ¬ 9 ∣ Nat.card (parabolic W) := by
  let r := Module.finrank (ZMod 2) W
  let s := Module.finrank (ZMod 2) (Space 4 ⧸ W)
  let a : W ≃ₗ[ZMod 2] Space r := LinearEquiv.ofFinrankEq _ _
    (Module.finrank_fin_fun (ZMod 2)).symm
  let b : (Space 4 ⧸ W) ≃ₗ[ZMod 2] Space s := LinearEquiv.ofFinrankEq _ _
    (Module.finrank_fin_fun (ZMod 2)).symm
  let e := (linearGroupCongr a).prodCongr (linearGroupCongr b)
  let f := blockAction W
  have hk : IsPGroup 2 f.ker := by
    rw [show f.ker = pCore 2 (parabolic W) from ker_blockAction_eq_twoCore W]
    exact pCore_isPGroup
  obtain ⟨k, hk⟩ := hk.exists_card_eq
  intro h9
  have hc := f.ker.card_mul_index
  rw [index_ker, hk, f.range_eq_top_of_surjective (blockAction_surjective W), card_top] at hc
  rw [← hc] at h9
  have hd := ((by decide : Nat.Coprime 9 2).pow_right k).dvd_of_dvd_mul_left h9
  rw [Nat.card_congr e.toEquiv, Nat.card_prod,
    linearGroup_card_formula, linearGroup_card_formula] at hd
  have hrs : r + s = 4 := by
    have hh := W.finrank_quotient_add_finrank
    rw [Module.finrank_fin_fun] at hh
    change s + r = 4 at hh
    omega
  change r = 1 ∨ r = 3 at hdim
  rcases hdim with hr | hr
  · have hs : s = 3 := by omega
    rw [hr, hs] at hd
    exact (by decide : ¬ 9 ∣ (∏ i : Fin 1, (2 ^ 1 - 2 ^ i.val)) *
      ∏ i : Fin 3, (2 ^ 3 - 2 ^ i.val)) hd
  · have hs : s = 1 := by omega
    rw [hr, hs] at hd
    exact (by decide : ¬ 9 ∣ (∏ i : Fin 3, (2 ^ 3 - 2 ^ i.val)) *
      ∏ i : Fin 1, (2 ^ 1 - 2 ^ i.val)) hd

private theorem singleton_isCoatom (i : Fin 3) :
    IsCoatom (cutStabilizer standardBasis {i}) := by
  constructor
  · intro he
    have h : cutStabilizer standardBasis ∅ ≤ cutStabilizer standardBasis {i} := by
      rw [he]
      exact le_top
    simpa using (cutStabilizer_le_iff standardBasis ∅ {i}).mp h (Set.mem_singleton i)
  · intro Q hQ
    obtain ⟨s, hs⟩ := standard_overgroups_of_bruhat hasBruhatDecomposition Q
      ((cutStabilizer_antitone standardBasis (Set.subset_univ {i})).trans hQ.le)
    have hi : s ⊆ {i} := (cutStabilizer_le_iff standardBasis _ _).mp (hQ.le.trans_eq hs)
    have he : s = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hj' : j = i := hi hj
      have hback : Q ≤ cutStabilizer standardBasis {i} := by
        rw [hs, cutStabilizer_le_iff]
        exact Set.singleton_subset_iff.mpr (hj' ▸ hj)
      exact hQ.not_ge hback
    simp [hs, he, cutStabilizer]

private theorem standard_solvable_overgroup (B : Subgroup (LinearGroup 4))
    (hTB : standardBorel ≤ B) (hs : Group.IsSolvable B) (h9 : 9 ∣ Nat.card B) :
    B = cutStabilizer standardBasis {1} := by
  obtain ⟨cuts, hB⟩ := standard_overgroups_of_bruhat hasBruhatDecomposition B hTB
  have hc : ∀ i ∈ cuts, i = (1 : Fin 3) := by
    intro i hi
    have hle : B ≤ parabolic (cutSpace standardBasis i) := by
      rw [hB]
      intro g hg
      exact ((mem_cutStabilizer _ _ _).mp hg) i hi
    have hd := h9.trans (card_dvd_of_le hle)
    have hdim := cutSpace_finrank standardBasis i
    fin_cases i
    · exact (nine_not_dvd_endpoint _ (Or.inl hdim) hd).elim
    · rfl
    · exact (nine_not_dvd_endpoint _ (Or.inr hdim) hd).elim
  have hn : cuts.Nonempty := by
    by_contra hn
    have hz : cuts = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    apply solvable_ne_top B hs
    simp [hB, hz, cutStabilizer]
  have he : cuts = {1} := by
    obtain ⟨i, hi⟩ := hn
    apply Set.Subset.antisymm hc
    exact Set.singleton_subset_iff.mpr (hc i hi ▸ hi)
  rw [hB, he]

/-- A solvable Sylow overgroup of order divisible by nine is a maximal plane stabilizer. -/
theorem solvable_sylow_overgroup_plane (T : Sylow 2 (LinearGroup 4))
    (B : Subgroup (LinearGroup 4)) (hTB : (T : Subgroup _) ≤ B)
    (hs : Group.IsSolvable B) (h9 : 9 ∣ Nat.card B) :
    ∃ W : Submodule (ZMod 2) (Space 4), Module.finrank (ZMod 2) W = 2 ∧
      B = parabolic W ∧ IsCoatom (parabolic W) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (LinearGroup 4) standardSylow T
  have hmap : standardBorel.map (MulAut.conj g).toMonoidHom =
      (T : Subgroup (LinearGroup 4)) := by
    change ((g • standardSylow : Sylow 2 (LinearGroup 4)) : Subgroup (LinearGroup 4)) = _
    rw [hg]
  let Q := B.map (MulAut.conj g).symm.toMonoidHom
  have hTQ : standardBorel ≤ Q := by
    intro u hu
    apply mem_map_equiv.mpr
    apply hTB
    rw [← hmap]
    exact mem_map.mpr ⟨u, hu, rfl⟩
  let eQ := B.equivMapOfInjective (MulAut.conj g).symm.toMonoidHom (MulAut.conj g).symm.injective
  have hQsol : Group.IsSolvable Q := by
    let := hs
    exact Group.isSolvable_of_surjective (f := eQ.toMonoidHom) eQ.surjective
  have hQ9 : 9 ∣ Nat.card Q := by rw [← Nat.card_congr eQ.toEquiv]; exact h9
  have hQ := standard_solvable_overgroup Q hTQ hQsol hQ9
  have hQB : Q.map (MulAut.conj g).toMonoidHom = B :=
    (map_symm_eq_iff_map_eq Q (e := MulAut.conj g) (H := B)).mp rfl
  have he : B = parabolic (cutSpace (standardBasis.map g) 1) := by
    rw [← hQB, hQ, cutStabilizer_map_conj]
    simp [cutStabilizer]
  refine ⟨cutSpace (standardBasis.map g) 1, cutSpace_finrank _ _, he, ?_⟩
  rw [← he, ← hQB, hQ]
  exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup _).mpr (singleton_isCoatom 1)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation.PlaneGeometry
