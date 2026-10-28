module

public import Theory.GroupTheory.DoubleCoverCentralizer.Basic
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage

/-!+# Involutory squares in the actual HS carrier

The product-class representative cannot be a square: it is central in its
centralizer C₂ × Aut(A₆), the automorphism factor is centerless, and squares
have trivial C₂ coordinate. The exhaustive two-class calculation therefore
puts every involutory square in the class of `e0`. The checked Sylow subgroup
of order 512 centralizes `e0`, as verified on its three generators.
Conjugating this genuine Sylow subgroup proves the required two-central mark.

This supplies the model calculation used with Aschbacher–Smith I.2.2(5a),
printed pp.409–412, and the HS product row of 16.1.5(10), printed p.1172.
The generator calculation is also used downstream in `CoverFusion.HSMarked`;
this module uses only the earlier inner-class and Sylow developments.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers.ProductMark
open Subgroup Theory.GroupTheory DoubleCoverCentralizer
open OtherPreliminaries.JankoTwoHigmanSims
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates

set_option maxRecDepth 100000

private theorem aut_center (a : MulAut A6) (ha : a ∈ center (MulAut A6)) : a = 1 := by
  apply MulEquiv.ext
  intro x
  apply AlternatingSix.ShadowLocal.inner_injective
  have hx := mem_center_iff.mp ha (MulAut.conj x)
  calc
    MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by ext y; simp
    _ = MulAut.conj x := by rw [← hx]; simp [mul_assoc]

private theorem t_not_square (y : Carrier) : y ^ 2 ≠ HSInner.ClassCoverage.t := by
  intro hy
  let C := centralizer ({HSInner.ClassCoverage.t} : Set Carrier)
  let tC : C := ⟨HSInner.ClassCoverage.t, mem_centralizer_singleton_iff.mpr rfl⟩
  have htC : tC ∈ center C := by
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (mem_centralizer_singleton_iff.mp c.property)
  obtain ⟨e⟩ := HSInner.ClassCoverage.product_centralizer_equiv
  have hec : (e tC).2 ∈ center (MulAut A6) := by
    apply mem_center_iff.mpr
    intro a
    have h := congrArg e (mem_center_iff.mp htC (e.symm (1, a)))
    simpa only [map_mul, e.apply_symm_apply, Prod.snd_mul] using congrArg Prod.snd h
  have he2 : (e tC).2 = 1 := aut_center _ hec
  have hyC : y ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hy]
    group
  have he1 : (e tC).1 = 1 := by
    have h : (⟨y, hyC⟩ : C) ^ 2 = tC := Subtype.ext hy
    have hp := congrArg (fun z : C => (e z).1) h
    have hc : Nat.card C2 = 2 := by simp [C2]
    simpa only [map_pow, Prod.pow_fst, ← hc, pow_card_eq_one'] using hp.symm
  have ht1 : tC = 1 := e.injective (by simpa only [map_one] using Prod.ext he1 he2)
  have ht := congrArg (fun z : C => (z : Carrier)) ht1
  exact (orderOf_eq_prime_iff.mp HSInner.ClassCoverage.t_order).2 ht

private theorem central_commutes : ∀ j : Fin 3, ∀ x : Fin 100,
    (inclusion (sylowGenerator j) * inclusion e0) x =
      (inclusion e0 * inclusion (sylowGenerator j)) x := by
  apply HSInner.ClassCoverage.Certificate.allFin
  decide +kernel

private theorem central_twoCentral : TwoCentral e0 := by
  have hm : e0 ∈ subgroup := by
    rw [e0_eq_word]
    exact subgroup.pow_mem (subgroup.inv_mem (subset_closure ⟨2, rfl⟩)) 2
  have hc : subgroup ≤ centralizer ({e0} : Set Carrier) := by
    apply (closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (Equiv.ext (central_commutes j))
  refine ⟨HSInner.ClassCoverage.Certificate.sylow, hm, ?_⟩
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp (hc x.property)

/-- Every involution that is a square in the exact HS carrier lies in the
center of a genuine Sylow two-subgroup. -/
theorem involution_twoCentral_of_square (x : Carrier) (hx : orderOf x = 2)
    (y : Carrier) (hy : y ^ 2 = x) : TwoCentral x := by
  rcases HSInner.ClassCoverage.involution_classes x hx with h | h
  · obtain ⟨g, hg⟩ := isConj_iff.mp h
    exact hg ▸ central_twoCentral.map (MulAut.conj g)
  · obtain ⟨g, hg⟩ := isConj_iff.mp h.symm
    exact (t_not_square (MulAut.conj g y) (by rw [← map_pow, hy]; exact hg)).elim

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers.ProductMark
