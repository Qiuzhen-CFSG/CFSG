module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Transport
public import Theory.GroupTheory.SemidihedralSixteenInvolutions
public import Mathlib.GroupTheory.IndexNormal

/-!
# Faithfulness for an index-two A₆ subgroup with semidihedral Sylow

The kernel of conjugation meets A₆ trivially. Index two makes each kernel
element have square one, so the kernel is a normal two-subgroup and lies in
the supplied Sylow. It centralizes the square of the SD16 rotation. The
normal forms give the identity or the central involution, which is already in A₆.

Source: the extension step of Aschbacher–Smith, J.2.7, printed p.435.
-/

public section
open Subgroup
namespace AlternatingSix.M10.SylowRecognition
open ShadowLocal

private theorem involution_commuting_square {G : Type*} [Group G]
    (a b x : G) (ha : orderOf a = 8) (hb : b ^ 2 = 1)
    (hc : b * a * b⁻¹ = a ^ 3) (hg : closure ({a, b} : Set G) = ⊤)
    (hx : x ^ 2 = 1) (hxcomm : Commute x (a ^ 2)) : x = 1 ∨ x = a ^ 4 := by
  obtain ⟨i, hi, rfl | rfl⟩ := Semidihedral.normal_form a b 8 3 (by decide) ha hb hc hg x
  · have hd := orderOf_dvd_of_pow_eq_one (show a ^ (i * 2) = 1 by rw [pow_mul]; exact hx)
    rw [ha] at hd
    have he : i = 0 ∨ i = 4 := by omega
    rcases he with rfl | rfl
    · exact Or.inl (pow_zero _)
    · exact Or.inr rfl
  · have he : (a ^ i * b) * a ^ 2 * (a ^ i * b)⁻¹ = a ^ 6 := by
      calc
        _ = a ^ i * (b * a ^ 2 * b⁻¹) * (a ^ i)⁻¹ := by group
        _ = a ^ 6 := by rw [← conj_pow, hc, ← pow_mul]; group
    rw [hxcomm.mul_inv_cancel] at he
    have hd := pow_inj_mod.mp he
    rw [ha] at hd
    norm_num at hd

/-- An index-two A₆ subgroup with an SD16 Sylow has faithful conjugation action. -/
theorem conjugation_injective {W : Type*} [Group W] [Finite W]
    (N : Subgroup W) [N.Normal] (hi : N.index = 2) (e : N ≃* A6)
    (S : Sylow 2 W) (s : S ≃* Semidihedral.StandardModel 4 (by decide)) :
    Function.Injective (conjugationAction N e) := by
  let f := conjugationAction N e
  have hN : ∀ x ∈ N, f x = 1 → x = 1 := by
    intro x hx hfx
    have he : MulAut.conj (e ⟨x, hx⟩) = MulAut.conj 1 := by
      rw [← conjugationAction_on_inner N e, map_one]
      exact hfx
    have he' : e ⟨x, hx⟩ = e 1 := by simpa only [map_one] using inner_injective he
    exact congrArg Subtype.val (e.injective he')
  have hsq : ∀ x ∈ f.ker, x ^ 2 = 1 := by
    intro x hx
    apply hN _ (N.sq_mem_of_index_two hi x)
    rw [map_pow, show f x = 1 from hx, one_pow]
  have hp : IsPGroup 2 f.ker := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro x
    exact ⟨1, Subtype.ext (hsq x x.property)⟩
  have hKS : f.ker ≤ (S : Subgroup W) := hp.le_sylow_of_normal S
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  let xS : S := ⟨x, hKS hx⟩
  let a := Semidihedral.standardRotation 4 (by decide)
  let b := Semidihedral.standardReflection 4 (by decide)
  have hb : b ^ 2 = 1 := by
    have hbo : orderOf b = 2 := Semidihedral.standardReflection_order 4 (by decide)
    simpa only [hbo] using pow_orderOf_eq_one b
  have hcomm : Commute (s xS) (a ^ 2) := by
    have hxC : x ∈ centralizer (N : Set W) := (conjugationAction_ker N e) ▸ hx
    have hNmem : ((s.symm a : S) : W) ^ 2 ∈ N := N.sq_mem_of_index_two hi _
    have he := (mem_centralizer_iff.mp hxC) _ hNmem
    have heS : Commute xS (s.symm a ^ 2) := by
      exact (show Commute (s.symm a ^ 2) xS from Subtype.ext he).symm
    simpa only [map_pow, MulEquiv.coe_toMonoidHom, s.apply_symm_apply] using heS.map s.toMonoidHom
  have hx2 : (s xS) ^ 2 = 1 := by
    rw [← map_pow, show xS ^ 2 = 1 from Subtype.ext (hsq x hx), map_one]
  obtain he | he := involution_commuting_square a b (s xS)
    (Semidihedral.standardRotation_order 4 (by decide)) hb
    (Semidihedral.standard_conjugation 4 (by decide))
    (Semidihedral.standard_generators 4 (by decide)) hx2 hcomm
  · exact (mem_bot).mpr (congrArg Subtype.val (s.injective (he.trans (map_one s).symm)))
  · have heS : xS = (s.symm a) ^ 4 := by
      apply s.injective
      simpa only [map_pow, s.apply_symm_apply] using he
    have hxN : x ∈ N := by
      have heW := congrArg Subtype.val heS
      change x = ((s.symm a : S) : W) ^ 4 at heW
      rw [heW]
      rw [pow_mul ((s.symm a : S) : W) 2 2]
      exact N.sq_mem_of_index_two hi _
    exact (mem_bot).mpr (hN x hxN hx)
end AlternatingSix.M10.SylowRecognition
