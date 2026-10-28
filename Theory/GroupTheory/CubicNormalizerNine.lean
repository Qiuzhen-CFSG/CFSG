module
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.OddCyclicThreeNormalizer
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# An external cubic extends a cyclic Sylow three-subgroup

Suppose every Sylow three-subgroup of N has order three. An order-three
normalizer element x outside N lies in a Sylow three-subgroup of N⟨x⟩.
Its intersection with N is a normal subgroup of order three, hence is
centralized by that Sylow subgroup. A generator y of the intersection
therefore commutes with x and ⟨y,x⟩ is elementary abelian of order nine.

Source application: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
with N the constructed plane-action group and x the actual lifted cubic.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {D : Type*} [Group D] [Finite D]

private theorem normal_cubic (N : Subgroup D) [N.Normal]
    (hN : ∀ S : Sylow 3 N, Nat.card S = 3)
    (x : D) (hx3 : orderOf x = 3) (hxN : x ∉ N) :
    ∃ y ∈ N, orderOf y = 3 ∧ Commute x y ∧
      IsElementaryAbelian 3 (zpowers y ⊔ zpowers x : Subgroup D) ∧
      Nat.card (zpowers y ⊔ zpowers x : Subgroup D) = 9 := by
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hx3,pow_one])
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal N
  let B := (R : Subgroup N).map N.subtype
  have hB : B = (S : Subgroup D) ⊓ N := by
    dsimp only [B]
    rw [hR,subgroupOf_map_subtype]
  have hc : Nat.card B = 3 := by
    dsimp only [B]
    rw [card_map_of_injective N.subtype_injective]
    exact hN R
  have hn : (S : Subgroup D) ≤ normalizer (B : Set D) := by
    rw [hB]
    exact (le_inf (S : Subgroup D).le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have ho : Nat.Coprime 2 (Nat.card S) := by
    obtain ⟨n,he⟩ := S.isPGroup'.exists_card_eq
    rw [he]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  have hcent := commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_odd_normalizes_card_three B (S : Subgroup D) hc ho hn)
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 (hc ▸ dvd_rfl)
  have hy3 : orderOf (y : D) = 3 := (B.orderOf_coe y).trans hy
  have hyN : (y : D) ∈ N := map_subtype_le _ y.property
  have hxy : Commute x (y : D) := hcent y.property x (hS (mem_zpowers x))
  let E := zpowers (y : D)
  let : IsElementaryAbelian 3 E :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hy3 ▸ pow_orderOf_eq_one (y : D))
  have hE : E ≤ N := zpowers_le.mpr hyN
  have hfix : E ≤ centralizer ({x} : Set D) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxy.symm)
  obtain ⟨hElt,hcard⟩ := IsElementaryAbelian.fixed_join_card E x hx3
    ((N.disjoint_zpowers_of_prime_order_not_mem x hx3 hxN).mono_left hE)
    hfix (by rw [Nat.card_zpowers,hy3]; rfl : Nat.card E = 3^1)
  exact ⟨y,hyN,hy3,hxy,hElt,hcard⟩

/-- A cubic outside a subgroup whose Sylow three-subgroups have order three
extends a cubic in that subgroup to an actual elementary nine-group. -/
theorem exists_elementary_nine_of_normalizing_cubic (N : Subgroup D)
    (hN : ∀ S : Sylow 3 N, Nat.card S = 3)
    (x : D) (hx3 : orderOf x = 3) (hxN : x ∉ N)
    (hn : x ∈ normalizer (N : Set D)) :
    ∃ y ∈ N, orderOf y = 3 ∧ Commute x y ∧
      IsElementaryAbelian 3 (zpowers y ⊔ zpowers x : Subgroup D) ∧
      Nat.card (zpowers y ⊔ zpowers x : Subgroup D) = 9 := by
  let A := N ⊔ zpowers x
  let B := N.subgroupOf A
  have hNA : N ≤ A := le_sup_left
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le N.le_normalizer (zpowers_le.mpr hn))
  let e : B ≃* N := subgroupOfEquivOfLe hNA
  have hB (S : Sylow 3 B) : Nat.card S = 3 := by
    have hc := hN (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    change Nat.card ((S : Subgroup B).map e.toMonoidHom) = 3 at hc
    rwa [card_map_of_injective e.injective] at hc
  let xA : A := ⟨x,mem_sup_right (mem_zpowers x)⟩
  obtain ⟨y,hy,hy3,hxy,hE,hcard⟩ := normal_cubic B hB xA
    ((A.orderOf_coe xA).symm.trans hx3) hxN
  have hy3' : orderOf (y : D) = 3 := (A.orderOf_coe y).trans hy3
  have hxy' : Commute x (y : D) := congrArg Subtype.val hxy
  let E := zpowers (y : D) ⊔ zpowers x
  have hm : (zpowers y ⊔ zpowers xA).map A.subtype = E := by
    rw [map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    rfl
  let := hE
  have hE' : IsElementaryAbelian 3 E := hm ▸ IsElementaryAbelian.map A.subtype
  have hc : Nat.card E = 9 := by
    rw [←hm,card_map_of_injective A.subtype_injective]
    exact hcard
  exact ⟨y,hy,hy3',hxy',hE',hc⟩
/-- A two-core quotient of order six supplies the Sylow-cardinality premise. -/
theorem exists_elementary_nine_of_normalizing_cubic_of_quotient_six
    (N : Subgroup D) (hc : Nat.card (N ⧸ pCore 2 N) = 6)
    (x : D) (hx3 : orderOf x = 3) (hxN : x ∉ N)
    (hn : x ∈ normalizer (N : Set D)) :
    ∃ y ∈ N, orderOf y = 3 ∧ Commute x y ∧
      IsElementaryAbelian 3 (zpowers y ⊔ zpowers x : Subgroup D) ∧
      Nat.card (zpowers y ⊔ zpowers x : Subgroup D) = 9 := by
  apply exists_elementary_nine_of_normalizing_cubic N _ x hx3 hxN hn
  intro S
  let q := QuotientGroup.mk' (pCore 2 N)
  have hk : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,he⟩ := (pCore_isPGroup (p := 2) (G := N)).exists_card_eq
    rw [he]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  let R : Sylow 3 (N ⧸ pCore 2 N) := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  rw [Nat.card_congr (Sylow.equivOfSurjectiveCoprime q
    (QuotientGroup.mk'_surjective _) hk S R).toEquiv,
    R.card_eq_multiplicity,hc]
  decide +kernel

end Subgroup
