module

public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.Models
public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.ActionCatalogue.CubicPartners
import Mathlib.Tactic

/-!
# The three seven-point actions of A₄

Every subgroup of the literal seven-point alternating group isomorphic to A₄
is conjugate in S₇ to `naturalFour`, `diagonalFour`, or `pairedFour`.

Choose the standard cubic and involutory generators through the given group
isomorphism. An even nonidentity involution on seven letters has cycle type
`{2, 2}`, so a relabelling makes it `fourFlip`. The checked cubic-partner
catalogue then normalizes the other generator. Mapping the generated subgroup
under the composite conjugation gives the asserted equality of subgroups.

This is the intrinsic action catalogue for the A₇ calculation in
Aschbacher–Smith 15.3.43, printed p.1140, with 1.1.5(3)(d), printed pp.501–502
(combined manuscript, 1 March 2004). The normalizer and residual calculations
are separate from this conjugacy theorem.
-/

public section

open Equiv Subgroup
namespace AlternatingSeven.ThreeResidualLocals

-- Standard A₄ generators; the finite word check below proves generation.
private def x : alternatingGroup (Fin 4) :=
  ⟨swap 0 1 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩
private def y : alternatingGroup (Fin 4) :=
  ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩
private theorem xy_relations : x ^ 3 = 1 ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧ (x * y) ^ 3 = 1 := by
  decide +kernel
private theorem xy_generate : closure ({x, y} : Set (alternatingGroup (Fin 4))) = ⊤ := by
  let H := closure ({x, y} : Set (alternatingGroup (Fin 4)))
  have hx : x ∈ H := subset_closure (by simp)
  have hy : y ∈ H := subset_closure (by simp)
  have hwords : ∀ z : alternatingGroup (Fin 4),
      ∃ i : Fin 3, ∃ j : Fin 2, ∃ k : Fin 2,
        z = x ^ i.val * y ^ j.val * (x * y * x⁻¹) ^ k.val := by decide +kernel
  apply eq_top_iff.mpr
  intro z _
  obtain ⟨i, j, k, rfl⟩ := hwords z
  exact H.mul_mem (H.mul_mem (H.pow_mem hx _) (H.pow_mem hy _))
    (H.pow_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) _)
private theorem involution_conjugacy (b : Perm7)
    (hb : b ∈ alternatingGroup (Fin 7)) (h2 : b ^ 2 = 1) (h1 : b ≠ 1) :
    ∃ g : Perm7, g * b * g⁻¹ = fourFlip := by
  have ho : orderOf b = 2 := orderOf_eq_prime h2 h1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hn
  have hs := b.sum_cycleType_le
  rw [hn, Multiset.sum_replicate] at hs
  have hnle : n ≤ 2 := by simp only [Fintype.card_fin, smul_eq_mul] at hs; omega
  have he : Perm.sign b = 1 := hb
  rw [Perm.sign_of_cycleType, hn] at he
  have hn1 : n = 1 := by
    interval_cases n <;> norm_num at he
    rfl
  subst n
  apply isConj_iff.mp
  apply Perm.isConj_iff_cycleType_eq.mpr
  rw [hn]
  decide
private theorem actual_generators (Y : Subgroup Perm7) (e : Y ≃* alternatingGroup (Fin 4)) :
    ∃ a b : Perm7, closure ({a, b} : Set Perm7) = Y ∧
      a ^ 3 = 1 ∧ b ^ 2 = 1 ∧ b ≠ 1 ∧ (a * b) ^ 3 = 1 := by
  let f : alternatingGroup (Fin 4) →* Perm7 := Y.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  obtain ⟨hx, hy, hy1, hxy⟩ := xy_relations
  refine ⟨f x, f y, ?_, by rw [← map_pow, hx, map_one],
    by rw [← map_pow, hy, map_one], ?_, ?_⟩
  · rw [← Set.image_pair, ← MonoidHom.map_closure, xy_generate]
    apply le_antisymm
    · rintro z ⟨w, _, rfl⟩
      exact (e.symm w).property
    · intro z hz
      exact ⟨e ⟨z, hz⟩, trivial, by simp [f]⟩
  · exact fun h => hy1 (hf (h.trans (map_one f).symm))
  · rw [← map_mul, ← map_pow, hxy, map_one]
private theorem map_pair (a b g : Perm7) :
    (closure ({a, b} : Set Perm7)).map (MulAut.conj g).toMonoidHom =
      closure ({g * a * g⁻¹, g * b * g⁻¹} : Set Perm7) := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

/-- An actual A₄ subgroup of A₇ is conjugate in S₇ to the natural,
diagonal, or paired model, with its given seven-point embedding preserved. -/
theorem a4_subgroup_conjugate_model
    (Y : Subgroup Perm7) (hY : Y ≤ alternatingGroup (Fin 7))
    (e : Y ≃* alternatingGroup (Fin 4)) :
    ∃ g : Perm7, Y.map (MulAut.conj g).toMonoidHom = naturalFour ∨
      Y.map (MulAut.conj g).toMonoidHom = diagonalFour ∨
      Y.map (MulAut.conj g).toMonoidHom = pairedFour := by
  obtain ⟨a, b, hgen, ha, hb, hb1, hab⟩ := actual_generators Y e
  have hbY : b ∈ Y := hgen ▸ subset_closure (by simp)
  obtain ⟨g, hg⟩ := involution_conjugacy b (hY hbY) hb hb1
  let a' := (MulAut.conj g) a
  have ha' : a' ^ 3 = 1 := by
    change ((MulAut.conj g) a) ^ 3 = 1
    rw [← map_pow, ha, map_one]
  have hab' : (a' * fourFlip) ^ 3 = 1 := by
    have hb' : (MulAut.conj g) b = fourFlip := hg
    change ((MulAut.conj g) a * fourFlip) ^ 3 = 1
    rw [← hb', ← map_mul, ← map_pow, hab, map_one]
  obtain ⟨c, hc, hcases⟩ := ActionCatalogue.cubic_partner_conjugacy a' ha' hab'
  have hmap : Y.map (MulAut.conj (c * g)).toMonoidHom =
      closure ({c * a' * c⁻¹, fourFlip} : Set Perm7) := by
    rw [← hgen, map_pair]
    have hcgb : c * g * b * (c * g)⁻¹ = fourFlip := by
      calc
        _ = c * (g * b * g⁻¹) * c⁻¹ := by group
        _ = fourFlip := by rw [hg, hc]
    have hcga : c * g * a * (c * g)⁻¹ = c * a' * c⁻¹ := by
      simp only [a', MulAut.conj_apply, mul_inv_rev, mul_assoc]
    rw [hcgb, hcga]
  refine ⟨c * g, ?_⟩
  rcases hcases with hn | hd | hp
  · exact Or.inl (hmap.trans (by rw [hn]; rfl))
  · exact Or.inr (Or.inl (hmap.trans (by rw [hd]; rfl)))
  · exact Or.inr (Or.inr (hmap.trans (by rw [hp]; rfl)))

end AlternatingSeven.ThreeResidualLocals
