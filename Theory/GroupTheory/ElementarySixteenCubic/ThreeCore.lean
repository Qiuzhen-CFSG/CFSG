module
public import Theory.GroupTheory.ElementarySixteenCubic.Quotient

/-!
# Cubic local ThreeCore

The normal cubic is the entire three-core: every normal three-subgroup centralizes the normal four, and its image modulo the cubic lies in a two-group.
Source: Aschbacher (1994), 45.7(3).
-/

public section
open Subgroup
namespace ElementarySixteenCubic
variable {N:Type*} [Group N] [Finite N]

/-- The actual normal cubic is the full three-core of the local normalizer. -/
theorem threeCore_eq_cubic
    (S U:Subgroup N) [S.Normal] [U.Normal] [IsElementaryAbelian 2 S]
    (hS:Nat.card S=4) (hU:Nat.card U=3)
    (hC:centralizer (S:Set N)=S⊔U) : pCore 3 N=U := by
  have hUp:IsPGroup 3 U:=IsPGroup.of_card (n:=1) (by simpa using hU)
  have hcop:Nat.Coprime (Nat.card (pCore 3 N)) (Nat.card S):=by
    obtain ⟨n,hn⟩:=(pCore_isPGroup (p:=3) (G:=N)).exists_card_eq
    rw [hn,hS]
    exact (by decide:Nat.Coprime 3 4).pow_left n
  have hdis:=disjoint_of_coprime_natCard (H:=pCore 3 N) (K:=S) hcop
  have hle:pCore 3 N≤S⊔U:=hC ▸
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hdis)
  let q:=QuotientGroup.mk' U
  have hm:(pCore 3 N).map q≤S.map q:=by
    have hh:=map_mono hle (f:=q)
    simpa only [q,Subgroup.map_sup,QuotientGroup.map_mk'_self,sup_bot_eq] using hh
  have hSp:IsPGroup 2 (S.map q):=(IsElementaryAbelian.isPGroup 2 S).map q
  have hDp:IsPGroup 3 ((pCore 3 N).map q):=pCore_isPGroup.map q
  have hcd:Nat.Coprime (Nat.card ((pCore 3 N).map q)) (Nat.card (S.map q)):=by
    obtain ⟨a,ha⟩:=hDp.exists_card_eq
    obtain ⟨b,hb⟩:=hSp.exists_card_eq
    rw [ha,hb]
    exact ((by decide:Nat.Coprime 3 2).pow_left a).pow_right b
  have hdb:=disjoint_of_coprime_natCard (H:=(pCore 3 N).map q) (K:=S.map q) hcd
  have hb:(pCore 3 N).map q=⊥:=by
    apply bot_unique
    exact fun x hx=>hdb.le_bot ⟨hx,hm hx⟩
  have hUle:U≤pCore 3 N:=le_sSup ⟨inferInstance,hUp⟩
  apply le_antisymm ?_ hUle
  have hh:=(map_eq_bot_iff (pCore 3 N)).mp hb
  rwa [QuotientGroup.ker_mk'] at hh
end ElementarySixteenCubic
