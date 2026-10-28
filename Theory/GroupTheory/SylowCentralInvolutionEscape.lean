module

public import Glauberman.ZStar
public import Theory.GroupTheory.SylowCentralizerNonfusion
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Escaping a Sylow subgroup whose inner involutions are central

Let G=NT with N normal, and let T be a self-normalizing
Sylow two-subgroup. A Sylow-central involution a in a subgroup S of T has
an N-conjugate in T outside S if the odd core of G is trivial, a is not
central in G, and all involutions of S∩N are Sylow-central.

If every returning conjugate remained in S, its product with a would be
an inner involution, so the conjugate would also be Sylow-central.
Burnside fusion would then make a weakly closed; Z-star gives the
contradiction. The conjugator is retained in N using the actual supplement.

This supplies the rank-one elementary step in the quadratic semilinear
fusion argument of Aschbacher--Smith 6.1.4, printed p.666.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory

/-- Z-star forces an actual normal-subgroup conjugator moving a central
Sylow involution out of S when all involutions in S∩N are Sylow-central. -/
theorem sylow_central_involution_escape
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (T : Sylow 2 G) (S : Subgroup G)
    (hgen : N ⊔ (T : Subgroup G) = ⊤)
    (hNT : normalizer (T : Set G) = (T : Subgroup G))
    (hcore : pPrimeCore 2 G = ⊥) (hST : S ≤ (T : Subgroup G))
    (hinner : ∀ z ∈ S ⊓ N, z ^ 2 = 1 → z ∈ centralizer (T : Set G))
    (a : G) (haS : a ∈ S) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1)
    (haC : a ∈ centralizer (T : Set G)) (haG : a ∉ center G) :
    ∃ g ∈ N, g * a * g⁻¹ ∈ (T : Subgroup G) ∧ g * a * g⁻¹ ∉ S := by
  classical
  let q := QuotientGroup.mk' N
  have hTa (t : G) (ht : t ∈ T) : t * a * t⁻¹ = a :=
    mul_inv_eq_iff_eq_mul.mpr (haC t ht)
  by_contra! hfail
  have hweak : Glauberman.ZStar.IsWeaklyClosedInSylow a (T : Subgroup G) := by
    refine ⟨hST haS, ?_⟩
    intro g hg
    obtain ⟨k, hk, t, ht, rfl⟩ := mem_sup_of_normal_left.mp
      (show g ∈ N ⊔ (T : Subgroup G) from hgen ▸ mem_top g)
    have he : (k * t) * a * (k * t)⁻¹ = k * a * k⁻¹ := by
      calc
        _ = k * (t * a * t⁻¹) * k⁻¹ := by group
        _ = k * a * k⁻¹ := by rw [hTa t ht]
    rw [he] at hg ⊢
    let b := k * a * k⁻¹
    have hbS : b ∈ S := hfail k hk hg
    have hb2 : b ^ 2 = 1 := by
      change (MulAut.conj k a) ^ 2 = 1
      rw [← map_pow, ha2, map_one]
    have hab : Commute a b := (haC b hg).symm
    have habN : a * b ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (a * (k * a * k⁻¹)) = 1
      have hkq : q k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
      simp only [map_mul, map_inv, hkq, inv_one, one_mul, mul_one]
      rw [← map_mul, ← pow_two, ha2, map_one]
    have hab2 : (a * b) ^ 2 = 1 := by rw [hab.mul_pow, ha2, hb2, one_mul]
    have habC := hinner (a * b) ⟨S.mul_mem haS hbS, habN⟩ hab2
    have hbC : b ∈ centralizer (T : Set G) := by
      simpa only [inv_mul_cancel_left] using (centralizer (T : Set G)).mul_mem
        ((centralizer (T : Set G)).inv_mem haC) habC
    apply T.eq_of_isConj_of_normalizer_le_centralizer a b haC hbC
    · rw [hNT]
      intro t ht
      exact mem_centralizer_singleton_iff.mpr (haC t ht)
    · exact isConj_iff.mpr ⟨k, rfl⟩
  exact haG (Glauberman.ZStar.glauberman_zstar_corefree hcore T a
    ⟨ha1, ha2⟩ (hST haS) (fun t ht => haC t ht) hweak)

end Theory.GroupTheory
