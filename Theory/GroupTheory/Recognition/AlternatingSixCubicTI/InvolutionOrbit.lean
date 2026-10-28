module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.CubicCentralizers
public import Theory.GroupAction.ElementConjugacyOrbit

/-!
# The nine involutions in an order-eighteen local orbit

Cubic centralizers of order nine exclude a cubic in any involution centralizer. An involution in a subgroup of order eighteen therefore has nine conjugates there; such a subgroup cannot normalize a subgroup of order six.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2(2), printed p.249.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
variable {G:Type*} [Group G] [Finite G]
variable (hc:∀x:G,orderOf x=3→Nat.card (centralizer ({x}:Set G))=9)
include hc in
theorem involution_centralizer_three_free (t:G) (ht:orderOf t=2):
    ¬3∣Nat.card (centralizer ({t}:Set G)) := by
  intro hd
  let : Fact (Nat.Prime 3):=⟨by decide⟩
  obtain ⟨x,hx⟩:=exists_prime_orderOf_dvd_card' (G:=centralizer ({t}:Set G)) 3 hd
  have hxG:orderOf (x:G)=3 :=
    (orderOf_injective (centralizer ({t}:Set G)).subtype Subtype.val_injective x).trans hx
  have htC:t∈centralizer ({(x:G)}:Set G) :=
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_singleton_iff.mp x.property).symm)
  have he:orderOf (⟨t,htC⟩:centralizer ({(x:G)}:Set G))=2 :=
    (orderOf_injective (centralizer ({(x:G)}:Set G)).subtype Subtype.val_injective _).symm.trans ht
  have hh:=orderOf_dvd_natCard (⟨t,htC⟩:centralizer ({(x:G)}:Set G))
  rw [he,hc _ hxG] at hh
  norm_num at hh

include hc in
theorem involution_orbit_nine (N:Subgroup G) (hN:Nat.card N=18)
    (t:G) (htN:t∈N) (ht:orderOf t=2):Nat.card (N.elementOrbit t)=9 := by
  let C:=N⊓centralizer ({t}:Set G)
  have h3:¬3∣Nat.card C := fun hh=>involution_centralizer_three_free hc t ht
    (hh.trans (card_dvd_of_le (show C≤centralizer ({t}:Set G) from inf_le_right)))
  have h2:2∣Nat.card C := by
    have htC:t∈C:=⟨htN,mem_centralizer_singleton_iff.mpr rfl⟩
    have he:orderOf (⟨t,htC⟩:C)=2 :=
      (orderOf_injective C.subtype Subtype.val_injective _).symm.trans ht
    exact he ▸ orderOf_dvd_natCard (⟨t,htC⟩:C)
  have hd:Nat.card C∣18 := hN ▸ card_dvd_of_le (show C≤N from inf_le_left)
  have hC:Nat.card C=2 := by
    have hm:=Nat.mem_divisors.mpr ⟨hd,(by decide : 18≠0)⟩
    rw [show Nat.divisors 18={1,2,3,6,9,18} by decide] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with h|h|h|h|h|h <;> simp_all
  have hh:=elementOrbit_card N t htN
  change Nat.card (N.elementOrbit t)*Nat.card C=Nat.card N at hh
  rw [hC,hN] at hh
  omega

include hc in
theorem eighteen_not_normalizes_six (N K:Subgroup G) (hN:Nat.card N=18)
    (hK:Nat.card K=6) (hKN:K≤N):¬N≤normalizer (K:Set G) := by
  intro hNK
  let : Fact (Nat.Prime 2):=⟨by decide⟩
  obtain ⟨t,ht⟩:=exists_prime_orderOf_dvd_card' (G:=K) 2 (by rw [hK]; decide)
  have htG:orderOf (t:G)=2 := (orderOf_injective K.subtype K.subtype_injective t).trans ht
  have ho:=involution_orbit_nine hc N hN t (hKN t.property) htG
  have hh:Nat.card (N.elementOrbit (t:G))≤Nat.card K :=
    Nat.card_le_card_of_injective (fun x=>⟨x.val,elementOrbit_subset hNK t.property x.property⟩:N.elementOrbit (t:G)→K)
      (fun x y he=>Subtype.ext (congrArg (fun k:K=>(k:G)) he))
  rw [ho,hK] at hh
  omega
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
