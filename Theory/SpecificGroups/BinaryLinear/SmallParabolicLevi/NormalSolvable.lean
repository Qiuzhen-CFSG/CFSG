module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Normal solvable subgroups of small binary parabolics

A normal solvable subgroup of a binary subspace stabilizer in dimension at
most five has order divisible by nine only if both diagonal blocks have
dimension two. The block-action kernel is a two-group, so it does not
remove the factor nine. A block of dimension at least three is simple and
perfect, hence receives the trivial image of the normal solvable subgroup.
The other block then has dimension at most two and order at most six.
Finally, two small blocks supply nine only when both have dimension two.

This uses the checked higher-rank PSL simplicity port, together with the
actual binary projective-to-linear equivalence; no model tag substitutes
for an isomorphism. The ATLAS attribution is retained in the imported
`Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity` module.

Source application: Aschbacher--Smith, combined manuscript (1 March 2004),
final paragraph of the proof of 15.3.35, printed p.1139.
-/

public section

open Subgroup
namespace BinaryLinear.SmallParabolicLevi
open OuterCyclic

private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem linearGroup_card_formula (n : ℕ) :
    Nat.card (LinearGroup n) = ∏ i : Fin n, (2 ^ n - 2 ^ i.val) := by
  rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
  simp

private theorem linearGroup_card_le_six (n : ℕ) (hn : n ≤ 2) : Nat.card (LinearGroup n) ≤ 6 := by
  rw [linearGroup_card_formula]
  interval_cases n <;> decide

private theorem small_blocks_nine {r s : ℕ} (hr : r ≤ 2) (hs : s ≤ 2)
    (h9 : 9 ∣ Nat.card (LinearGroup r) * Nat.card (LinearGroup s)) : r = 2 ∧ s = 2 := by
  rw [linearGroup_card_formula, linearGroup_card_formula] at h9
  interval_cases r <;> interval_cases s
  all_goals first | exact ⟨rfl, rfl⟩ | norm_num at h9

private theorem normal_solvable_high_eq_bot {n : ℕ} (hn : 3 ≤ n)
    (N : Subgroup (LinearGroup n)) [N.Normal] [Group.IsSolvable N] : N = ⊥ := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    Atlas.psl_simple_high_rank n hn
  let : IsSimpleGroup (LinearGroup n) := (projectiveEquivLinear (by omega : 0 < n)).symm.isSimpleGroup
  let : Group.IsPerfect (LinearGroup n) := linearGroup_isPerfect n hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N inferInstance with h | h
  · exact h
  · have : Group.IsSolvable (⊤ : Subgroup (LinearGroup n)) := h ▸ inferInstance
    have : Group.IsSolvable (LinearGroup n) :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv :
        (⊤ : Subgroup (LinearGroup n)) ≃* LinearGroup n).toMonoidHom) Subgroup.topEquiv.surjective
    exact (Group.IsPerfect.not_isSolvable (LinearGroup n) inferInstance).elim

private theorem not_nine_dvd_high_low {r s : ℕ} (hr : 3 ≤ r) (hs : s ≤ 2)
    (N : Subgroup (LinearGroup r × LinearGroup s)) [N.Normal] [Group.IsSolvable N] :
    ¬ 9 ∣ Nat.card N := by
  let f := MonoidHom.fst (LinearGroup r) (LinearGroup s)
  let B := N.map f
  have hf : Function.Surjective f := fun a => ⟨(a, 1), rfl⟩
  let : B.Normal := Subgroup.Normal.map inferInstance f hf
  let : Group.IsSolvable B := Group.isSolvable_of_surjective (f.subgroupMap_surjective N)
  have hB : B = ⊥ := normal_solvable_high_eq_bot hr B
  have hfirst (x : N) : x.val.1 = 1 := by
    have hx : x.val.1 ∈ B := mem_map_of_mem f x.property
    simpa only [hB, mem_bot] using hx
  let g := (MonoidHom.snd (LinearGroup r) (LinearGroup s)).comp N.subtype
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact Prod.ext ((hfirst x).trans (hfirst y).symm) h
  intro h9
  have hdiv : 9 ∣ Nat.card (LinearGroup s) := h9.trans (card_dvd_of_injective g hg)
  have := (Nat.le_of_dvd Nat.card_pos hdiv).trans (linearGroup_card_le_six s hs)
  omega

private theorem nine_dvd_range_of_two_kernel {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (hk : IsPGroup 2 f.ker) (h9 : 9 ∣ Nat.card A) : 9 ∣ Nat.card f.range := by
  obtain ⟨k, hk⟩ := hk.exists_card_eq
  have hc := f.ker.card_mul_index
  rw [index_ker, hk] at hc
  rw [← hc] at h9
  exact ((by decide : Nat.Coprime 9 2).pow_right k).dvd_of_dvd_mul_left h9

/-- In a binary subspace stabilizer of dimension at most five, a normal
solvable subgroup of order divisible by nine forces both block dimensions to be two. -/
theorem normal_solvable_nine_forces_two_blocks {n : ℕ} (hn : n ≤ 5)
    (W : Submodule (ZMod 2) (Space n))
    (N : Subgroup (parabolic W)) [N.Normal] [Group.IsSolvable N]
    (h9 : 9 ∣ Nat.card N) :
    Module.finrank (ZMod 2) W = 2 ∧ Module.finrank (ZMod 2) (Space n ⧸ W) = 2 := by
  let r := Module.finrank (ZMod 2) W
  let s := Module.finrank (ZMod 2) (Space n ⧸ W)
  let a : W ≃ₗ[ZMod 2] Space r := LinearEquiv.ofFinrankEq _ _
    (Module.finrank_fin_fun (ZMod 2)).symm
  let b : (Space n ⧸ W) ≃ₗ[ZMod 2] Space s := LinearEquiv.ofFinrankEq _ _
    (Module.finrank_fin_fun (ZMod 2)).symm
  let e := (linearGroupCongr a).prodCongr (linearGroupCongr b)
  let f := e.toMonoidHom.comp (blockAction W)
  have hf : Function.Surjective f := e.surjective.comp (blockAction_surjective W)
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = (blockAction W).ker := by
      ext x
      change e (blockAction W x) = 1 ↔ blockAction W x = 1
      exact e.map_eq_one_iff
    rw [he, ker_blockAction_eq_twoCore]
    exact pCore_isPGroup
  let B := N.map f
  let : B.Normal := Subgroup.Normal.map inferInstance f hf
  let : Group.IsSolvable B := Group.isSolvable_of_surjective (f.subgroupMap_surjective N)
  have h9B : 9 ∣ Nat.card B := by
    have hkN : IsPGroup 2 (f.comp N.subtype).ker := hk.comap_subtype
    have h := nine_dvd_range_of_two_kernel (f.comp N.subtype) hkN h9
    simpa only [MonoidHom.range_comp, range_subtype] using h
  have hrs : r + s = n := by
    have h := W.finrank_quotient_add_finrank
    rw [Module.finrank_fin_fun] at h
    change s + r = n at h
    omega
  have hr : r ≤ 2 := by
    by_contra h
    exact not_nine_dvd_high_low (by omega) (by omega : s ≤ 2) B h9B
  have hs : s ≤ 2 := by
    by_contra h
    let t : LinearGroup r × LinearGroup s ≃* LinearGroup s × LinearGroup r := MulEquiv.prodComm
    let C := B.map t.toMonoidHom
    let : C.Normal := Subgroup.Normal.map inferInstance t.toMonoidHom t.surjective
    let : Group.IsSolvable C := Group.isSolvable_of_surjective (t.toMonoidHom.subgroupMap_surjective B)
    have h9C : 9 ∣ Nat.card C := by rwa [card_map_of_injective t.injective]
    exact not_nine_dvd_high_low (by omega) hr C h9C
  have hcard : Nat.card B ∣ Nat.card (LinearGroup r) * Nat.card (LinearGroup s) := by
    simpa only [Nat.card_prod] using card_subgroup_dvd_card B
  exact small_blocks_nine hr hs (h9B.trans hcard)

end BinaryLinear.SmallParabolicLevi
