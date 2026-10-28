module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.Obstruction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.ModelInputs
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups

/-!
# The centralizer route for outer eight-group actors

An order-eight actor contains a Sylow-central involution in the simple
socle. If this involution centralizer has rank-one E-generation for the
restricted original family, literal E-member inheritance puts the entire
centralizer in the obstruction overgroup. Its Sylow subgroup is the original
ambient Sylow, so no saturation or Sylow-intersection assumption is needed.

The family-specific centralizer generation and the remaining unitary generation
geometry are still required. In particular this module does not yet prove
the unconditional eight-actor exclusion. The source actor has not been
replaced by its inner four-group or by any subgroup outside the given family.
The unrestricted centralizer generation statement is deliberately not a
required model input: at p = 5 its rank-one section can be PSL₂(5), outside
the q > 5 scope of E.1.14(6).

Source: Aschbacher--Smith E.1.8, E.1.11 and E.1.14(7), pp.210--214.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
variable {G : Type*} [Group G] [Finite G]

/-- The restricted family has the same ambient weak closure. Generation for
this particular family traps a Sylow overgroup, with literal local taus.
Unrestricted rank-one generation of H is not needed. -/
theorem family_generated_sylow_overgroup_le {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hgen : eFamilySubgroup 1 ((T : Subgroup G).subgroupOf H)
        (ChiefOrbit.restrictedFamily H d.family) ⊔
      normalizer (weakClosure ((T : Subgroup G).subgroupOf H)
        (ChiefOrbit.restrictedFamily H d.family) : Set H) = ⊤) :
    H ≤ d.overgroup := by
  have he := congrArg (Subgroup.map H.subtype) hgen
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at he
  rw [← he]
  apply sup_le
  · apply (ChiefOrbit.map_eFamilySubgroup_restrictedFamily_le 1 T H hTH d.elementary).trans
    apply iSup_le
    intro A
    exact sSup_le fun K hK => d.members_le A.val A.property.1 A.property.2 K hK
  · have hn := le_normalizer_map H.subtype
      (H := weakClosure ((T : Subgroup G).subgroupOf H)
        (ChiefOrbit.restrictedFamily H d.family))
    rw [ChiefOrbit.map_weakClosure_restrictedFamily (T : Subgroup G) H hTH d.family] at hn
    exact hn.trans d.normalizer_le

/-- Actual application to the eight-actor branch. The only extra input is
rank-one generation for the actual restricted family in the specified centralizers; the
chosen central involution and all family/Sylow transports are constructed.
The producer of that local generation remains a prerequisite. -/
theorem exists_trapped_centralizer_of_generation
    [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    {A : Subgroup G} (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    (hcard : Nat.card A = 8)
    (hinner : Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 4)
    (hlocal : ∀ z : G, orderOf z = 2 → z ∈ generalizedFitting G →
      (T : Subgroup G) ≤ centralizer ({z} : Set G) →
      let C := centralizer ({z} : Set G)
      eFamilySubgroup 1 ((T : Subgroup G).subgroupOf C)
          (ChiefOrbit.restrictedFamily C d.family) ⊔
        normalizer (weakClosure ((T : Subgroup G).subgroupOf C)
          (ChiefOrbit.restrictedFamily C d.family) : Set C) = ⊤) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ generalizedFitting G ∧ z ∈ A ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      centralizer ({z} : Set G) ≤ d.overgroup := by
  obtain ⟨z, hz2, hzL, _, hTz, hall⟩ :=
    exists_common_central_involution hp ho hmodel d hinner
  exact ⟨z, hz2, hzL, hall A hA hAT hcard, hTz,
    family_generated_sylow_overgroup_le d _ hTz (hlocal z hz2 hzL hTz)⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
