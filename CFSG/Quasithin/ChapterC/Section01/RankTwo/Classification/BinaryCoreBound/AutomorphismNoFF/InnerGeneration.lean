module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AutomorphismNoFF.Reduction

/-!
# Inner elementary-subgroup generation in Aut(SL₃(2))

Three conjugates of any inner involution, and two automorphism-conjugates of
any inner elementary four-group, generate the entire inner automorphism group.
In particular, they contain the specified Singer actor.

Kernel-checked finite matrix calculations move an involution to `I + E₀₁`
and an independent commuting pair to `I + E₀₁, I + E₀₂`, allowing inverse
transpose for the second inner class of four-groups. Three cyclically arranged
transvections generate SL₃(2), as do the standard four-group and its inverse
transpose: elementary commutator identities recover all six transvections,
and Gaussian elimination gives the whole group. Naturality of the faithful
inner embedding transports these calculations to actual subgroup conjugation
inside `MulAut SL`.

This discharges the concrete `InnerGeneration` input to the direct binary
FF exclusion motivated by Aschbacher–Smith C.1.32, printed pp.135–136, and the
binary SL₃ specialization of B.4.2/B.5.1, in the 1 March 2004 manuscript.
-/

open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterC.BinaryMS.AutomorphismNoFF

private def t01 : SL := ⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩
private def t02 : SL := ⟨!![1,0,1; 0,1,0; 0,0,1], by decide⟩
private def t12 : SL := ⟨!![1,0,0; 0,1,1; 0,0,1], by decide⟩
private def t20 : SL := ⟨!![1,0,0; 0,1,0; 1,0,1], by decide⟩
private def t10 : SL := ⟨!![1,0,0; 1,1,0; 0,0,1], by decide⟩
private def t21 : SL := ⟨!![1,0,0; 0,1,0; 0,1,1], by decide⟩
private def cycle : SL := ⟨!![0,0,1; 1,0,0; 0,1,0], by decide⟩

private theorem three_generate (H : Subgroup SL)
    (h01 : t01 ∈ H) (h12 : t12 ∈ H) (h20 : t20 ∈ H) : H = ⊤ := by
  have h02 : t02 ∈ H := by
    rw [show t02 = t01 * t12 * t01 * t12 by decide]
    exact H.mul_mem (H.mul_mem (H.mul_mem h01 h12) h01) h12
  have h10 : t10 ∈ H := by
    rw [show t10 = t12 * t20 * t12 * t20 by decide]
    exact H.mul_mem (H.mul_mem (H.mul_mem h12 h20) h12) h20
  have h21 : t21 ∈ H := by
    rw [show t21 = t20 * t01 * t20 * t01 by decide]
    exact H.mul_mem (H.mul_mem (H.mul_mem h20 h01) h20) h01
  apply top_unique
  intro g _
  apply Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun g => g ∈ H) g
  · intro i j hij c hc
    have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc
    have hd : Matrix.SpecialLinearGroup.diag2n hij c hc = (1 : SL) := by
      apply Subtype.ext
      simp [Matrix.SpecialLinearGroup.diag2n_coe, hc1]
    rw [hd]
    exact H.one_mem
  · intro i j hij a
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · simp
    · have hcases : ∀ (i j : Fin 3) (hij : i ≠ j),
          Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2) = t01 ∨
          Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2) = t02 ∨
          Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2) = t10 ∨
          Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2) = t12 ∨
          Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2) = t20 ∨
          Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2) = t21 := by decide
      rcases hcases i j hij with h | h | h | h | h | h <;> rw [h] <;> assumption
  · exact fun _ _ => H.mul_mem

private theorem opposite_generate (H : Subgroup SL)
    (h01 : t01 ∈ H) (h02 : t02 ∈ H)
    (hg01 : graphSL 3 t01 ∈ H) (hg02 : graphSL 3 t02 ∈ H) : H = ⊤ := by
  have h12 : t12 ∈ H := by
    rw [show t12 = graphSL 3 t01 * t02 * graphSL 3 t01 * t02 by decide]
    exact H.mul_mem (H.mul_mem (H.mul_mem hg01 h02) hg01) h02
  apply three_generate H h01 h12
  rwa [show t20 = graphSL 3 t02 by decide]

private theorem inner_natural (α : AutSL) (x : SL) :
    MulAut.conj α (MulAut.conj x) = MulAut.conj (α x) := by
  ext y : 1
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply,
    map_mul, map_inv, MulEquiv.apply_symm_apply]

private theorem pullback_conjugate_mem (A : Subgroup AutSL) (α β : AutSL) (x : SL)
    (hx : MulAut.conj (α.symm x) ∈ A) :
    MulAut.conj (α.symm (β x)) ∈ conjugate A (α⁻¹ * β * α) := by
  refine ⟨_, hx, ?_⟩
  change MulAut.conj (α⁻¹ * β * α) (MulAut.conj (α.symm x)) = _
  rw [inner_natural]
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]

private theorem three_conjugates (A : Subgroup AutSL) (α : AutSL)
    (hx : MulAut.conj (α.symm t01) ∈ A) :
    ∃ b c : AutSL, singerActor ∈ (A ⊔ conjugate A b) ⊔ conjugate A c := by
  let β : AutSL := MulAut.conj cycle
  let b := α⁻¹ * β * α
  let c := α⁻¹ * (β * β) * α
  let J := (A ⊔ conjugate A b) ⊔ conjugate A c
  let H : Subgroup SL := J.comap (MulAut.conj.comp α.symm.toMonoidHom)
  have h01 : t01 ∈ H :=
    (le_sup_left.trans le_sup_left : A ≤ J) hx
  have h12 : t12 ∈ H := by
    have ht : β t01 = t12 := by decide
    exact (le_sup_right.trans le_sup_left : conjugate A b ≤ J)
      (ht ▸ pullback_conjugate_mem A α β t01 hx)
  have h20 : t20 ∈ H := by
    have ht : (β * β) t01 = t20 := by decide
    exact (le_sup_right : conjugate A c ≤ J)
      (ht ▸ pullback_conjugate_mem A α (β * β) t01 hx)
  have hH := three_generate H h01 h12 h20
  refine ⟨b, c, ?_⟩
  have hs : α singer ∈ H := hH.symm ▸ Subgroup.mem_top _
  change MulAut.conj (α.symm (α singer)) ∈ J at hs
  change MulAut.conj singer ∈ J
  simpa only [MulEquiv.symm_apply_apply] using hs

private theorem two_conjugates (A : Subgroup AutSL) (α : AutSL)
    (hx : MulAut.conj (α.symm t01) ∈ A)
    (hy : MulAut.conj (α.symm t02) ∈ A) :
    ∃ b : AutSL, singerActor ∈ A ⊔ conjugate A b := by
  let β := graphSL 3
  let b := α⁻¹ * β * α
  let J := A ⊔ conjugate A b
  let H : Subgroup SL := J.comap (MulAut.conj.comp α.symm.toMonoidHom)
  have h01 : t01 ∈ H := (le_sup_left : A ≤ J) hx
  have h02 : t02 ∈ H := (le_sup_left : A ≤ J) hy
  have hg01 : β t01 ∈ H := (le_sup_right : conjugate A b ≤ J)
    (pullback_conjugate_mem A α β t01 hx)
  have hg02 : β t02 ∈ H := (le_sup_right : conjugate A b ≤ J)
    (pullback_conjugate_mem A α β t02 hy)
  have hH := opposite_generate H h01 h02 hg01 hg02
  refine ⟨b, ?_⟩
  have hs : α singer ∈ H := hH.symm ▸ Subgroup.mem_top _
  change MulAut.conj (α.symm (α singer)) ∈ J at hs
  change MulAut.conj singer ∈ J
  simpa only [MulEquiv.symm_apply_apply] using hs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem involution_conjugate : ∀ a : SL, a ^ 2 = 1 → a ≠ 1 →
    ∃ g : SL, g * a * g⁻¹ = t01 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem pair_conjugate : ∀ y : SL, y ^ 2 = 1 → y ≠ 1 → y ≠ t01 →
    y * t01 = t01 * y → ∃ g : SL,
    (g * t01 * g⁻¹ = t01 ∧ g * y * g⁻¹ = t02) ∨
    (g * graphSL 3 t01 * g⁻¹ = t01 ∧ g * graphSL 3 y * g⁻¹ = t02) := by
  decide +kernel

private theorem normalize_pair (x y : SL)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hyx : y ≠ x) (hcomm : y * x = x * y) :
    ∃ α : AutSL, α x = t01 ∧ α y = t02 := by
  obtain ⟨g, hg⟩ := involution_conjugate x hx hx1
  let δ : AutSL := MulAut.conj g
  have hδ : δ x = t01 := hg
  have hs : (δ y) ^ 2 = 1 := by rw [← map_pow, hy, map_one]
  have hn : δ y ≠ 1 := fun he => hy1 (δ.map_eq_one_iff.mp he)
  have hne : δ y ≠ t01 := fun he => hyx (δ.injective (he.trans hδ.symm))
  have hc : δ y * t01 = t01 * δ y := by
    rw [← hδ, ← map_mul, ← map_mul, hcomm]
  obtain ⟨k, hk⟩ := pair_conjugate (δ y) hs hn hne hc
  rcases hk with ⟨hkx, hky⟩ | ⟨hkx, hky⟩
  · refine ⟨MulAut.conj k * δ, ?_, ?_⟩
    · simpa only [MulAut.mul_apply, MulAut.conj_apply, hδ] using hkx
    · exact hky
  · refine ⟨MulAut.conj k * graphSL 3 * δ, ?_, ?_⟩
    · simpa only [MulAut.mul_apply, hδ, MulAut.conj_apply] using hkx
    · exact hky

open Representation.BinaryOffender
open scoped IsMulCommutative

/-- Nontrivial elementary subgroups of the actual inner automorphism group
have the required rank-one or rank-two Singer-generation witnesses. -/
public theorem innerGeneration : InnerGeneration := by
  classical
  intro A hA hi
  let : IsElementaryAbelian 2 A := hA.2
  have hinj : Function.Injective (MulAut.conj : SL → AutSL) :=
    MulAut.conj_injective_of_center_eq_bot (binary_center_eq_bot (by decide : 0 < 3))
  obtain ⟨a, ha, ha1⟩ := (Subgroup.nontrivial_iff_exists_ne_one A).mp
    ((Subgroup.nontrivial_iff_ne_bot A).mpr hA.1)
  obtain ⟨x, rfl⟩ := hi ha
  have hx1 : x ≠ 1 := fun he => ha1 (he ▸ MulAut.conj.map_one)
  have hx : x ^ 2 = 1 := hinj (by
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ ha)
  have hr := elementary_rank_le_two A hA.2
  have hp := hA.rank_pos
  by_cases hr1 : rank A = 1
  · left
    refine ⟨hr1, ?_⟩
    obtain ⟨g, hg⟩ := involution_conjugate x hx hx1
    apply three_conjugates A (MulAut.conj g)
    have he : (MulAut.conj g).symm t01 = x :=
      (MulAut.conj g).symm_apply_eq.mpr hg.symm
    simpa only [he] using ha
  · right
    have hr2 : rank A = 2 := by omega
    refine ⟨hr2, ?_⟩
    have hc : Nat.card A = 4 := by
      rw [hA.card_eq_two_pow_rank, hr2]
      decide
    have hother : ∃ b : A, b ≠ 1 ∧ b ≠ ⟨MulAut.conj x, ha⟩ := by
      by_contra! hn
      have hc2 : Nat.card A = 2 := (Nat.card_eq_two_iff' (1 : A)).mpr
        ⟨⟨MulAut.conj x, ha⟩, fun he => ha1 (congrArg Subtype.val he), hn⟩
      omega
    obtain ⟨⟨b, hb⟩, hb1, hba⟩ := hother
    obtain ⟨y, rfl⟩ := hi hb
    have hy1 : y ≠ 1 := by
      intro he
      apply hb1
      apply Subtype.ext
      exact he ▸ MulAut.conj.map_one
    have hyx : y ≠ x := by
      intro he
      apply hba
      exact Subtype.ext (congrArg MulAut.conj he)
    have hy : y ^ 2 = 1 := hinj (by
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian _ hb)
    have hcomm : y * x = x * y := hinj (by
      simpa only [map_mul, Subgroup.coe_mul] using congrArg Subtype.val
        (mul_comm (⟨MulAut.conj y, hb⟩ : A) ⟨MulAut.conj x, ha⟩))
    obtain ⟨α, hαx, hαy⟩ := normalize_pair x y hx hy hx1 hy1 hyx hcomm
    apply two_conjugates A α
    · have he : α.symm t01 = x := α.symm_apply_eq.mpr hαx.symm
      simpa only [he] using ha
    · have he : α.symm t02 = y := α.symm_apply_eq.mpr hαy.symm
      simpa only [he] using hb

end CFSG.Quasithin.ChapterC.BinaryMS.AutomorphismNoFF
