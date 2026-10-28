module

public import Theory.SpecificGroups.PSL3.SmallSylowFixed
public import Theory.GroupAction.SylowFixedRankOneOddCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Odd cores of small PSL₃ Sylow-fixing involution centralizers

The full pointwise Sylow fixer is highest-root conjugation. At field order
two or four its fixed group is the actual unitriangular two-group, because
the centralizing torus is scalar. Conjugacy transports this calculation to
every Sylow subgroup. The faithful overgroup transfer then eliminates the
odd core in the original acting group's involution centralizer.

Source: the PSL₃(2), PSL₃(4) inspection in Aschbacher–Smith E.6.19,
printed p.252; the root centralizer calculation is that of 16.4.8, p.1188.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.EvenInnerCentralizers
open Matrix.PSL3Even.UnipotentGeometry
variable (F : Type*) [Field F] [Finite F]

/-- The fixed subgroup of every nonidentity small-field Sylow fixer is a two-group. -/
theorem small_sylow_fixed_isTwoGroup {n : ℕ} (hn : 0 < n) (hn2 : n ≤ 2)
    (hF : Nat.card F = 2 ^ n) (S : Sylow 2 PSL(3,F))
    (a : MulAut PSL(3,F)) (ha : a ≠ 1) (hfix : ∀ x ∈ S, a x = x) :
    IsPGroup 2 a.fixedSubgroup := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hs : Nat.card F = 2 ∨ Nat.card F = 4 := by
    have : n = 1 ∨ n = 2 := by omega
    rcases this with rfl | rfl
    · exact Or.inl (by simpa only [pow_one] using hF)
    · exact Or.inr (by simpa only [show 2 ^ 2 = 4 by decide] using hF)
  let P := LinearThree.unipotentSylow F hn hF
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) P S
  let e := MulAut.conj g
  have hm : (P : Subgroup PSL(3,F)).map e.toMonoidHom = S :=
    congrArg Sylow.toSubgroup hg
  let b := MulAut.congr e.symm a
  have hb : b ≠ 1 := fun h => ha ((MulAut.congr e.symm).injective
    (h.trans (map_one _).symm))
  have hbfix : ∀ x ∈ LinearThree.unipotent F, b x = x := by
    intro x hx
    change e.symm (a (e x)) = x
    have hxS : e x ∈ (S : Subgroup PSL(3,F)) := by
      rw [← hm]
      exact mem_map_of_mem e.toMonoidHom hx
    rw [hfix _ hxS, e.symm_apply_apply]
  obtain ⟨z,hz,he⟩ := LinearThree.exists_projectiveCenter_of_fixes_unipotent F hn hF b hbfix
  obtain ⟨c,rfl⟩ := (mem_projectiveCenter F z).mp hz
  have hu : (⟨0,0,c⟩ : U F) ≠ 1 := by
    intro h
    rw [h, map_one, map_one] at he
    exact hb he
  have hu2 : (⟨0,0,c⟩ : U F) ^ 2 = 1 :=
    (square_eq_one_iff F _).mpr (Or.inl rfl)
  have hconj : IsConj (projective F ⟨0,0,c⟩) (root F) :=
    (projection F).map_isConj (specialLinear_isConj_root F _ hu hu2)
  obtain ⟨k,hk⟩ := isConj_iff.mp hconj
  have hfixed : (MulAut.congr (MulAut.conj k) b).fixedSubgroup = centralizer F := by
    rw [he, MulAut.congr_conj,
      show MulAut.conj k (projective F ⟨0,0,c⟩) = root F from hk,
      MulAut.fixedSubgroup_conj]
    rfl
  let f := (MulAut.fixedSubgroupCongr e.symm a).trans
    ((MulAut.fixedSubgroupCongr (MulAut.conj k) b).trans
      (MulEquiv.subgroupCongr hfixed))
  exact (small_centralizer_isTwoGroup F hs).of_injective f.toMonoidHom f.injective

/-- The original automorphism-overgroup centralizer has trivial odd core. -/
theorem small_sylowFixedInvolution_oddCore_eq_bot
    {H : Type*} [Group H] [Finite H] {φ : H →* MulAut PSL(3,F)} {E : Subgroup H}
    {n : ℕ} (hn : 0 < n) (hn2 : n ≤ 2) (hF : Nat.card F = 2 ^ n)
    (d : Theory.GroupAction.SylowFixedInvolution φ E) :
    pPrimeCore 2 (Subgroup.centralizer (E : Set H)) = ⊥ := by
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  have hc : center PSL(3,F) = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)
  apply d.oddCore_eq_bot_of_inner hc
  · intro S a hfix
    obtain ⟨z,⟨w,_,rfl⟩,he⟩ := LinearThree.exists_sylow_center_conj_of_equiv
      F hn hF (MulEquiv.refl _) S a hfix
    exact ⟨w,w.property,he⟩
  · intro S z hz hfix
    have hne : MulAut.conj z ≠ 1 := by
      intro he
      have hz1 := MulAut.conj_injective_of_center_eq_bot hc (he.trans (map_one _).symm)
      simp [hz1] at hz
    have hp := small_sylow_fixed_isTwoGroup F hn hn2 hF S (MulAut.conj z) hne hfix
    rw [MulAut.fixedSubgroup_conj] at hp
    exact Theory.GroupAction.pPrimeCore_eq_bot_of_isPGroup hp
end Matrix.PSL3.EvenInnerCentralizers
