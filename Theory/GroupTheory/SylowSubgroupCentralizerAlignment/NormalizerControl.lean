module

public import Theory.GroupTheory.CharacteristicCentralizerSylow
/-!
# Cardinal control from a local Sylow normalizer

A two-subgroup maximal in C∩M is Sylow in C when its ambient normalizer
lies in M. The normalizer condition promotes maximality; Sylow conjugacy
then bounds the order of every two-subgroup of C by its order.

Source: the normalizer-escape step of Aschbacher--Smith 13.5.6, p.917.
-/

@[expose] public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem card_le_of_local_sylow_normalizer_control
    (Q C M:Subgroup G)(hq:IsPGroup 2 Q)(hQC:Q≤C)
    (hN:normalizer (Q:Set G)≤M)
    (hmax:∀U:Subgroup G,IsPGroup 2 U→Q≤U→U≤C→U≤M→U=Q)
    (R:Subgroup G)(hr:IsPGroup 2 R)(hRC:R≤C) : Nat.card R≤Nat.card Q := by
  obtain ⟨P,hQP⟩:=(hq.comap_subtype (K:=C)).exists_le_sylow
  have hQP':Q≤(P:Subgroup C).map C.subtype:=by
    rw [←map_subgroupOf_eq_of_le hQC];exact map_mono hQP
  have he:(P:Subgroup C).map C.subtype=Q:=
    prime_overgroup_eq_of_normalizer_control Q C M hN hmax _
      (P.isPGroup'.map C.subtype) hQP' (map_subtype_le _)
  obtain ⟨S,hRS⟩:=(hr.comap_subtype (K:=C)).exists_le_sylow
  have hcard:Nat.card R≤Nat.card S:=by
    have hh:=card_le_of_le hRS
    change Nat.card (R.subgroupOf C)≤Nat.card S at hh
    rwa [Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv] at hh
  have hSP:Nat.card S=Nat.card P:=by rw [S.card_eq_multiplicity,P.card_eq_multiplicity]
  have hPQ:Nat.card P=Nat.card Q:=by
    rw [←he,card_map_of_injective C.subtype_injective]
  exact hcard.trans_eq (hSP.trans hPQ)
end Subgroup
