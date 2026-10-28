module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Transport
public import Theory.SpecificGroups.Held.RankOneLocalPair.Ambient
public import Theory.SpecificGroups.Held.LocalGeneration

/-!
# Conditional assembly of the Held rank-one local pair

Embed the original finite group faithfully into Aut(He) by conjugation on
its genuine generalized Fitting subgroup. The image contains Inn(He) and
retains G = F*(G)T. Independent maximal and solvable overgroup constructions
in that image then transport back to the specified Sylow group in G.

The two concrete construction contracts remain explicit. In particular,
this module does not yet prove the local-pair existence needed to complete
Aschbacher--Smith E.1.14(4), printed p.214. No generation premise is hidden
in either contract. Once the pair exists, its orders imply generation.
-/

@[expose] public section

namespace Held.RankOneLocalPair
open Subgroup

open Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- Conditional assembly from the two independent concrete local constructions.
The faithful action and all transports are proved here; both construction
contracts must still be discharged before this is the requested Held local pair. -/
theorem exists_of_automorphism_overgroups [IsSimpleGroup (generalizedFitting G)]
    (hmax : MaximalOvergroups) (hsol : SolvableOvergroups)
    (e : generalizedFitting G ≃* He) (T : Sylow 2 G)
    (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤) :
    ∃ P B : Subgroup G, IsLocalPair (T : Subgroup G) P B := by
  let d := ambientEquiv e
  let A := (ambientAction e).range
  let S : Sylow 2 A := T.mapSurjective (f := d.toMonoidHom) d.surjective
  have hA := inner_le_ambientAction_range e
  have hS := ambientEquiv_sylow_join e T hgen
  obtain ⟨P, hP, hc, hSP, hQ⟩ := hmax A hA S hS
  obtain ⟨B, hSB, hB, hsolB⟩ := hsol A hA S hS
  have hp : IsLocalPair (S : Subgroup A) P B := ⟨hP, hc, hSP, hSB, hB, hsolB, hQ⟩
  refine ⟨P.map d.symm.toMonoidHom, B.map d.symm.toMonoidHom, ?_⟩
  have hm := hp.map d.symm
  change IsLocalPair (((T : Subgroup G).map d.toMonoidHom).map d.symm.toMonoidHom)
    (P.map d.symm.toMonoidHom) (B.map d.symm.toMonoidHom) at hm
  have hid : d.symm.toMonoidHom.comp d.toMonoidHom = MonoidHom.id G := by
    ext x
    exact d.symm_apply_apply x
  simpa only [Subgroup.map_map, hid, Subgroup.map_id] using hm

omit [Finite G] in
/-- The certified local-pair conditions imply actual ambient generation. -/
theorem IsLocalPair.sup_eq_top {T P B : Subgroup G} (h : IsLocalPair T P B) :
    P ⊔ B = ⊤ :=
  Held.local_pair_sup_eq_top P B h.maximal h.card h.nine_dvd

end Held.RankOneLocalPair
