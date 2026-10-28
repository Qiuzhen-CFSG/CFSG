module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Normalization.Selection
/-!
# Relative normality and the local centralizer kernel

The marked A₈ contains a concrete element of order four. If a conjugate of
K inside C_G(t) were a different component, component commutation would put
such an element in C_{G_t}(K). The supplied Sylow subgroup ⟨t⟩ has order two,
so this is impossible. Thus K is normal in C_G(t).

For any local Sylow P containing t, Sylow maximality also gives C_P(K)=⟨t⟩.
These are inputs to the action and direct-product calculation; they do not
assume an automorphism group identification or a model of P.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 16.3.11
and the proof of Theorem 16.3.7, printed pp.1181–1182 / PDF pp.1198–1199.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction
variable {G : Type*} [Group G]
variable {z t : G} {L : Subgroup G}

private def fourCycleEven : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 1 * (Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5)

private theorem fourCycleEven_mem : fourCycleEven ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem fourCycleEven_order : orderOf fourCycleEven = 4 := by
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by decide +kernel) (by decide +kernel)

/-- A concrete element of order four in the actual A₈ enlargement. -/
theorem MarkedEnlargement.exists_order_four (d : MarkedEnlargement z t L) :
    ∃ x : G, x ∈ enlargement t L ∧ orderOf x = 4 := by
  have hm : fourCycleEven ∈ ((enlargement t L).subgroupOf
      (enlargement t L ⊔ zpowers z)).map d.equiv.toMonoidHom := by
    rw [d.enlargement_image]
    exact fourCycleEven_mem
  obtain ⟨x, hx, he⟩ := hm
  change d.equiv x = fourCycleEven at he
  refine ⟨x, hx, ?_⟩
  calc
    orderOf (x : G) = orderOf x := orderOf_coe x
    _ = orderOf (d.equiv x) := (d.equiv.orderOf_eq x).symm
    _ = 4 := by rw [he]; exact fourCycleEven_order

private theorem no_order_four [Finite G] {H : Subgroup G} (ht : orderOf t = 2)
    (hs : ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = zpowers t)
    (x : G) (hx : x ∈ H) : orderOf x ≠ 4 := by
  intro hx4
  obtain ⟨S, hS⟩ := hs
  have hcS : Nat.card S = 2 := by
    calc
      Nat.card S = Nat.card ((S : Subgroup H).map H.subtype) :=
        Nat.card_congr ((S : Subgroup H).equivMapOfInjective H.subtype
          H.subtype_injective).toEquiv
      _ = 2 := by rw [hS, Nat.card_zpowers, ht]
  let a : H := ⟨x, hx⟩
  have ha : orderOf a = 4 := (orderOf_coe a).symm.trans hx4
  have hp : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 2) (by
    norm_num [Nat.card_zpowers, ha])
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  have hcR : Nat.card R = 2 := by
    rw [R.card_eq_multiplicity, ← S.card_eq_multiplicity, hcS]
  have hd := card_dvd_of_le hR
  rw [Nat.card_zpowers, ha, hcR] at hd
  norm_num at hd

/-- A conjugate component distinct from K would commute with K and carry an
order-four element into its centralizer. The supplied order-two centralizer
Sylow excludes this, so K is normal in C_G(t), with no ambient-normality claim. -/
theorem MarkedEnlargement.enlargement_normal [Finite G]
    (d : MarkedEnlargement z t L) (ht : orderOf t = 2) :
    ((enlargement t L).subgroupOf (involutionCentralizer t)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer d.component.1).mpr
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  let e : G ≃* G := MulAut.conj g
  have hfix : e t = t :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg)
  have hcomp : Theory.GroupTheory.IsComponentIn (enlargement t L)
      (involutionCentralizer t) := d.component
  have hc := hcomp.map e
  rw [involutionCentralizer, map_centralizer_equiv, Set.image_singleton, hfix] at hc
  by_contra hne
  have hcomm := hc.commutator_eq_bot_of_ne hcomp hne
  have hle := commutator_eq_bot_iff_le_centralizer.mp hcomm
  obtain ⟨x, hx, hx4⟩ := d.exists_order_four
  have hy : e x ∈ (enlargement t L).map e.toMonoidHom := mem_map_of_mem _ hx
  exact no_order_four ht d.centralizer_enlargement_sylow (e x)
    ⟨hc.1 hy, hle hy⟩ ((e.orderOf_eq x).trans hx4)

/-- The supplied Sylow centralizer determines the kernel on every local Sylow
containing t: C_P(K) is exactly ⟨t⟩. -/
theorem MarkedEnlargement.localSylow_centralizer_eq [Finite G]
    (d : MarkedEnlargement z t L) (P : Sylow 2 (involutionCentralizer t))
    (htP : t ∈ localSylow P) :
    localSylow P ⊓ centralizer (enlargement t L : Set G) = zpowers t := by
  let H := involutionCentralizer t ⊓ centralizer (enlargement t L : Set G)
  let U := localSylow P ⊓ centralizer (enlargement t L : Set G)
  have hUH : U ≤ H := fun _ hx => ⟨map_subtype_le _ hx.1, hx.2⟩
  have hpP : IsPGroup 2 (localSylow P) := P.isPGroup'.map _
  have hp : IsPGroup 2 U := hpP.of_injective
    (inclusion (inf_le_left : U ≤ localSylow P)) (inclusion_injective _)
  have htU : t ∈ U := ⟨htP, fun x hx =>
    mem_centralizer_singleton_iff.mp (d.component.1 hx)⟩
  obtain ⟨S, hS⟩ := d.centralizer_enlargement_sylow
  have he : U.subgroupOf H = (S : Subgroup H) := S.is_maximal' hp.comap_subtype (by
    intro x hx
    apply (zpowers_le.mpr htU : zpowers t ≤ U)
    rw [← hS]
    exact mem_map_of_mem H.subtype hx)
  have hm := congrArg (fun A : Subgroup H => A.map H.subtype) he
  rwa [map_subgroupOf_eq_of_le hUH, hS] at hm

end CFSG.Quasithin.Chapter16.ThompsonObstruction
