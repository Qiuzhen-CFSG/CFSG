module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Definitions

/-!
# Transport of the intrinsic Held local pair

An ambient equivalence transports maximality, orders, solvability and both
Sylow containments. Its restriction to the first subgroup transports the
intrinsic two-core; the induced quotient equivalence transports the normal
PSL₃(2) subgroup and the second quotient's two-group property.

These lemmas do not construct either local subgroup. They are the transport
step for Aschbacher--Smith E.1.14(4), printed p.214.
-/

@[expose] public section

namespace Held.RankOneLocalPair
open Subgroup

/-- Transport both successive quotients, the normal subgroup, and its actual model equivalence. -/
theorem HasPSL3TwoCoreQuotient.of_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : HasPSL3TwoCoreQuotient G) : HasPSL3TwoCoreQuotient H := by
  obtain ⟨J, hJ, ⟨d⟩, htwo⟩ := h
  let := hJ
  let q : (G ⧸ pCore 2 G) ≃* (H ⧸ pCore 2 H) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let K := J.map q.toMonoidHom
  have hK : K.Normal := hJ.map q.toMonoidHom q.surjective
  let := hK
  refine ⟨K, hK, ⟨(q.subgroupMap J).symm.trans d⟩, ?_⟩
  exact htwo.of_equiv (QuotientGroup.congr J K q rfl)

/-- An ambient group equivalence preserves every clause of the local-pair contract. -/
theorem IsLocalPair.map {G H : Type*} [Group G] [Group H]
    {T P B : Subgroup G} (h : IsLocalPair T P B) (e : G ≃* H) :
    IsLocalPair (T.map e.toMonoidHom) (P.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  have hcardP : Nat.card (P.map e.toMonoidHom) = Nat.card P :=
    card_map_of_injective e.injective
  have hcardB : Nat.card (B.map e.toMonoidHom) = Nat.card B :=
    card_map_of_injective e.injective
  let := h.solvable
  refine ⟨(e.mapSubgroup.isCoatom_iff P).mpr h.maximal,
    hcardP ▸ h.card, map_mono h.sylow_le_first, map_mono h.sylow_le_second,
    hcardB ▸ h.nine_dvd, ?_, h.quotient.of_equiv (e.subgroupMap P)⟩
  exact Group.isSolvable_of_surjective (f := (e.subgroupMap B).toMonoidHom)
    (e.subgroupMap B).surjective

end Held.RankOneLocalPair
