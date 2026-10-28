module

public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Field restriction from an involution centralizer of order eight

An involution centralizer in PSL2 over an odd finite field is a cyclic torus
extended by an external inverting involution. Its order is twice the torus
order. If it has order eight, the torus has order four; the exact torus orders
(q-1)/2 and (q+1)/2 force q = 9 or q = 7. The final lemma transports the
centralizer through an actual group equivalence, across arbitrary universes.

This is the field restriction in Held, Illinois J. Math. 13 (1969), Lemma 4.2,
printed p.234, DOI 10.1215/ijm/1256053756.
-/

open Subgroup GorensteinWalter
noncomputable section
namespace Theory.GroupTheory.DihedralEightRecognition
universe u v
private def centralizerEquiv {H : Type u} {K : Type v} [Group H] [Group K]
    (e : H ≃* K) (t : H) : centralizer ({t} : Set H) ≃* centralizer ({e t} : Set K) where
  toFun x := ⟨e x, by
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp x.property)⟩
  invFun y := ⟨e.symm y, by
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (e.map_mul x y)

/-- An involution centralizer of order eight forces field order seven or nine. -/
public theorem field_card_of_centralizer_eight
    {F : Type u} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (t : PSL2 F) (ht : orderOf t = 2)
    (hC : Nat.card (centralizer ({t} : Set (PSL2 F))) = 8) :
    Nat.card F = 7 ∨ Nat.card F = 9 := by
  have htI : IsInvolution t := by
    refine ⟨?_, by simpa only [ht] using pow_orderOf_eq_one t⟩
    intro h
    simp [h] at ht
  obtain ⟨T, s, _hTcyc, _htT, hsI, hsT, hinv, hcent, _heven, hcard⟩ :=
    psl2_reflected_torus_card hF htI
  have hsN : s ∈ normalizer T := by
    rw [mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      change s * y * s⁻¹ ∈ T
      rw [hinv y hy]
      exact T.inv_mem hy
    · intro x hx
      refine ⟨x⁻¹, T.inv_mem hx, ?_⟩
      change s * x⁻¹ * s⁻¹ = x
      rw [hinv x⁻¹ (T.inv_mem hx), inv_inv]
  have hdouble := card_sup_zpowers_of_normalizing_involution T s hsI.2 hsT hsN
  rw [← hcent, hC] at hdouble
  have hfour : Nat.card T = 4 := by omega
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, n, _, hp, _, he⟩ := hF
    rw [he]
    exact hp.pow
  rcases hodd with ⟨k, hk⟩
  rcases hcard with hm | hp
  · right; omega
  · left; omega

/-- The field restriction transported through a specified PSL2 model. -/
public theorem field_card_of_model
    {H : Type u} [Group H] {F : Type v} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (e : H ≃* PSL2 F)
    (t : H) (ht : orderOf t = 2)
    (hC : Nat.card (centralizer ({t} : Set H)) = 8) :
    Nat.card F = 7 ∨ Nat.card F = 9 := by
  apply field_card_of_centralizer_eight hF (e t)
  · exact (e.orderOf_eq t).trans ht
  · rw [← Nat.card_congr (centralizerEquiv e t).toEquiv]
    exact hC
end Theory.GroupTheory.DihedralEightRecognition
