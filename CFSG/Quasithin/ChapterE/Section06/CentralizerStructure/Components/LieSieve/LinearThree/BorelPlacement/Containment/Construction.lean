module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement.Transport
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure
public import Theory.GroupTheory.ComponentLocalOrbitSolvable

/-!
# The solvable characteristic-two Borel overgroup in E.6.8

The marked Sylow normalizer is transported to the actual PSL₃ Borel.
Its two-core is self-centralizing and it is solvable. The same assertions
lift through a two-group central kernel, including a trivial kernel.
Component-orbit inheritance gives both properties for the join with Q,
using only N_Q(L) to stabilize the Borel. The full E.6.7 input then gives
its three-clause decomposition. No Borel containment is assumed here.

These completed construction results are shared by containment and the
remaining A₃-block exclusion. Source: Aschbacher–Smith E.6.7–8, printed
pp.246–248 (combined manuscript, 1 March 2004).
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment
open Matrix.PSL3.LinearThree.BorelStructure
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

private theorem markedBorel_properties_of_surjective {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (f : L →* PSL(3,F)) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 L) :
    HasCharacteristicTwo (markedBorel L S) ∧ Group.IsSolvable (markedBorel L S) := by
  let e := (normalizer (S : Set L)).equivMapOfInjective L.subtype L.subtype_injective
  have hc : HasCharacteristicTwo (normalizer (S : Set L)) :=
    sylowNormalizer_core_selfCentralizing_of_surjective F hn hF f hf hk S
  let := sylowNormalizer_isSolvable_of_surjective F hn hF f hf hk S
  exact ⟨hc.of_equiv e, Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective⟩

/-- The actual ordinary model supplies both intrinsic Borel premises. -/
theorem ordinary_markedBorel_properties {n : ℕ} (hn : 1 ≤ n)
    (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) (S : Sylow 2 L) :
    HasCharacteristicTwo (markedBorel L S) ∧ Group.IsSolvable (markedBorel L S) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
  apply markedBorel_properties_of_surjective hn hF e.toMonoidHom e.surjective _ S
  rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
  exact IsPGroup.of_bot

/-- Covering centers may be nontrivial or trivial; only their two-group property is used. -/
theorem cover_markedBorel_properties (hz : IsPGroup 2 (center L))
    (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) (S : Sylow 2 L) :
    HasCharacteristicTwo (markedBorel L S) ∧ Group.IsSolvable (markedBorel L S) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  apply markedBorel_properties_of_surjective (n := 2) (by decide) hF f
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) _ S
  have hk : f.ker = center L := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact hz.of_equiv (MulEquiv.subgroupCongr hk.symm)

/-- Solvability persists when Q permutes the components. -/
theorem markedBorel_adjoin_solvable (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hs : Group.IsSolvable (markedBorel L S)) :
    Group.IsSolvable (markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hL.2.relative_local_adjoin_isSolvable hL.1 (map_subtype_le _)
    (inf_le_right.trans (Subgroup.centralizer_le hU.1))
    (T.isPGroup'.to_le inf_le_left) (markedBorel_stable S hS) hs

/-- The constructed ordinary overgroup satisfies all intrinsic premises of E.6.7. -/
theorem ordinary_construction
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    {n : ℕ} (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) :
    HasCharacteristicTwo (markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G) ∧
    Group.IsSolvable (markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G) ∧
    Nonempty (InvariantSubspaces.BlockSelection.E67Decomposition
      (sylowCentralizer (T : Subgroup G) V) M V U
      (markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V)) := by
  obtain ⟨hc, hs⟩ := ordinary_markedBorel_properties hn iso S
  exact ⟨markedBorel_adjoin_characteristicTwo hU hL S hS hc,
    markedBorel_adjoin_solvable hU hL S hS hs,
    markedBorel_adjoin_decomposition h67 hU hL S hS hc⟩

/-- The same construction uses the literal central quotient in the covering branch. -/
theorem cover_construction
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hz : IsPGroup 2 (center L)) (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) :
    HasCharacteristicTwo (markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G) ∧
    Group.IsSolvable (markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G) ∧
    Nonempty (InvariantSubspaces.BlockSelection.E67Decomposition
      (sylowCentralizer (T : Subgroup G) V) M V U
      (markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V)) := by
  obtain ⟨hc, hs⟩ := cover_markedBorel_properties hz iso S
  exact ⟨markedBorel_adjoin_characteristicTwo hU hL S hS hc,
    markedBorel_adjoin_solvable hU hL S hS hs,
    markedBorel_adjoin_decomposition h67 hU hL S hS hc⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment
