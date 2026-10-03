module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Stellmacher.Recognition.NormalEightExoticThickCriticalInvolutions
public import Theory.GroupTheory.PGroup.NormalFourThickCriticalBase
public import Theory.GroupTheory.PGroup.NormalEightCentralizerFusion

/-!
# The thick-candidate reduction for a normal abelian base

Fusion of the unique normal four supplies transitivity on its centralizer.
For a maximal characteristic homocyclic abelian candidate of exponent at
least four, the remaining structural input is containment of involutions of
the critical subgroup with that center. The critical-involution theorem gives
that containment, so the critical subgroup reduction makes the candidate
self-centralizing. Its image in the Sylow subgroup is normal, abelian, and
has transitive involutions.
Source: Janko–Thompson, Math. Z. 113 (1970), 1.4, printed p.386 and §6,
printed p.395, citing the MacWilliams structure theorem.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightExoticThickCandidateBase

/-- The thick candidate gives the desired normal abelian base. -/
public theorem exists_base_of_critical_involutions
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (A : Subgroup (centralizer (W : Set S))) [A.Characteristic] [IsMulCommutative A]
    (hWA : W ≤ A.map (centralizer (W : Set S)).subtype)
    (hmax : ∀ A' : Subgroup (centralizer (W : Set S)), A'.Characteristic →
      IsMulCommutative A' → A ≤ A' → A' = A)
    (n : ℕ) (hn : 2 ≤ n)
    (e : A.map (centralizer (W : Set S)).subtype ≃*
      (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^n)))) :
    ∃ D : Subgroup S, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set S) ≤ D ∧
      (∀ x y : D, orderOf x = 2 → orderOf y = 2 → ∃ a : MulAut D, a x = y) := by
  let C := centralizer (W : Set S)
  let D := A.map C.subtype
  let : D.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsMulCommutative D := Subgroup.map_isMulCommutative (H := A) C.subtype
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := omega₁ (center S) (p := 2))
    2 (by rw [hZ])
  have htrans := S.centralizer_four_automorphism_transitive_of_no_normal_eight
    hno hZ W hW hunique ((z : center S) : S)
    (by simpa only [orderOf_coe] using hz) (z : center S).property (by
      intro x y hx hy
      exact hfused x y x.property y.property
        ((orderOf_coe x).trans (orderOf_eq_prime
          (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ x.property)) hx))
        ((orderOf_coe y).trans (orderOf_eq_prime
          (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ y.property)) hy)))
  have hcard : Nat.card A = 2 ^ n * 2 ^ n := by
    calc
      Nat.card A = Nat.card D := (card_map_of_injective C.subtype_injective).symm
      _ = 2 ^ n * 2 ^ n := by
        rw [Nat.card_congr e.toEquiv, Nat.card_prod]
        simp
  have hlarge : 4 < Nat.card A := by
    have hp : 4 ≤ 2 ^ n := (show 2 ^ 2 ≤ 2 ^ n from Nat.pow_le_pow_right (by omega) hn)
    rw [hcard]
    nlinarith
  have hinv : ∀ K : Subgroup (centralizer (W : Set S)), IsCriticalPSubgroup 2 K →
      (center K).map K.subtype = A → ∀ x : K, x ^ 2 = 1 →
      (x : centralizer (W : Set S)) ∈ A := by
    intro K hK hKA x hx
    exact NormalEightExoticThickCriticalInvolutions.critical_involution_mem_candidate
      S hno W hW A hWA hmax n hn e K hK hKA x hx
  have hself := candidate_selfCentralizing_of_critical_involutions S.isPGroup'
    hno W hW htrans A hWA hmax hlarge hinv
  have hDC : centralizer (D : Set S) ≤ D := by
    intro x hx
    have hxC : x ∈ C := centralizer_le hWA hx
    refine ⟨⟨x, hxC⟩, hself ?_, rfl⟩
    intro a ha
    exact Subtype.ext (hx a (mem_map_of_mem C.subtype ha))
  have hO := omega_one_eq_normal_four_of_no_normal_eight hno W D hW hWA
  have hmem (d : D) (hd : orderOf d = 2) : (d : S) ∈ W := by
    apply hO.le
    refine ⟨d, subset_closure ?_, rfl⟩
    change d ^ (2 ^ 1) = 1
    simpa only [pow_one, hd] using pow_orderOf_eq_one d
  refine ⟨D, hWA, inferInstance, inferInstance, hDC, ?_⟩
  let f : A ≃* D := A.equivMapOfInjective C.subtype C.subtype_injective
  intro x y hx hy
  obtain ⟨x, rfl⟩ := f.surjective x
  obtain ⟨y, rfl⟩ := f.surjective y
  have hxC : orderOf (x : C) = 2 :=
    (orderOf_coe x).trans ((f.orderOf_eq x).symm.trans hx)
  have hyC : orderOf (y : C) = 2 :=
    (orderOf_coe y).trans ((f.orderOf_eq y).symm.trans hy)
  obtain ⟨a, ha⟩ := htrans x y (hmem (f x) hx) (hmem (f y) hy) hxC hyC
  refine ⟨f.symm.trans ((MulAut.characteristic A a).trans f), ?_⟩
  change f (MulAut.characteristic A a (f.symm (f x))) = f y
  rw [f.symm_apply_apply]
  exact congrArg f (Subtype.ext ha)

end Stellmacher.Recognition.NormalEightExoticThickCandidateBase
