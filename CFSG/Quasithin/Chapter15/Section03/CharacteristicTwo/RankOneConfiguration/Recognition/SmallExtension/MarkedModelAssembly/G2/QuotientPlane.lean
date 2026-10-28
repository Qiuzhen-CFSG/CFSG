module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.BlockModels.Planes

/-!
# The original V₂ in the block's central quotient

Map the ambient plane through the literal center quotient, retaining its
central kernel. A trivial intersection with the Y₊-centralizer makes this
map injective whenever Y₊ lies in L. Equivariance then places the image of
the original normalizer in the stabilizer of this same plane.

These transports prepare the G₂ branch of Aschbacher–Smith 15.3.31,
printed p.1132 (PDF p.1149), using the moving-plane assertion of 15.3.29.
No canonical-plane placement is assumed here.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedModelAssembly.G2Coordinates
open CentralCover CentralCover.BlockModels
variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  {L E Y P : Subgroup G} {ρ : Representation (ZMod 2) A V}

/-- The original subgroup mapped through the full central quotient. -/
def planeMap (m : CenterModel L ρ) (hE : E ≤ coreCenter L) : E →* Multiplicative V :=
  m.coordinates.comp (inclusion hE)

/-- The binary subspace of actual quotient coordinates of the original plane. -/
noncomputable def quotientPlane (m : CenterModel L ρ) (E : Subgroup G) :
    Submodule (ZMod 2) V :=
  AddSubgroup.toZModSubmodule 2
    (((E.subgroupOf (coreCenter L)).map m.coordinates).toAddSubgroup')

theorem mem_quotientPlane (m : CenterModel L ρ) (hE : E ≤ coreCenter L) (v : V) :
    v ∈ quotientPlane m E ↔ ∃ e : E, planeMap m hE e = Multiplicative.ofAdd v := by
  constructor
  · rintro ⟨z, hz, he⟩
    exact ⟨⟨z, hz⟩, he⟩
  · rintro ⟨e, he⟩
    exact ⟨⟨e, hE e.property⟩, e.property, he⟩

theorem planeMap_injective (m : CenterModel L ρ) (hE : E ≤ coreCenter L)
    (hYL : Y ≤ L) (hfix : E ⊓ centralizer (Y : Set G) = ⊥) :
    Function.Injective (planeMap m hE) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro e he
  have hc : (e : G) ∈ centralizer (L : Set G) :=
    (m.coordinates_eq_one_iff ⟨e, hE e.property⟩).mp he
  apply Subtype.ext
  exact mem_bot.mp (hfix ▸ And.intro e.property ((centralizer_le hYL) hc))

theorem quotientPlane_card (m : CenterModel L ρ) (hE : E ≤ coreCenter L)
    (hi : Function.Injective (planeMap m hE)) :
    Nat.card (quotientPlane m E) = Nat.card E := by
  let f : E → quotientPlane m E := fun e =>
    ⟨(planeMap m hE e).toAdd, (mem_quotientPlane m hE _).mpr ⟨e, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      apply hi
      exact congrArg (fun v : quotientPlane m E => Multiplicative.ofAdd v.val) he
    · intro v
      obtain ⟨e, he⟩ := (mem_quotientPlane m hE v).mp v.property
      exact ⟨e, Subtype.ext (congrArg Multiplicative.toAdd he)⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem quotientPlane_stabilized (m : CenterModel L ρ) (hE : E ≤ coreCenter L)
    (hP : P ≤ normalizer (E : Set G)) :
    (P.subgroupOf L).map m.actorMap ≤ BlockModels.planeStabilizer ρ (quotientPlane m E) := by
  apply le_subspaceStabilizer
  rintro _ ⟨l, hl, rfl⟩ v hv
  obtain ⟨e, he⟩ := (mem_quotientPlane m hE v).mp hv
  let z : coreCenter L := ⟨e, hE e.property⟩
  let e' : E := ⟨l * (e : G) * (l : G)⁻¹, (hP hl (e : G)).mp e.property⟩
  apply (mem_quotientPlane m hE _).mpr
  refine ⟨e', ?_⟩
  have hc := m.coordinates_conjugate l z
  change planeMap m hE e' = Multiplicative.ofAdd
    (ρ (m.actorMap l) (planeMap m hE e).toAdd) at hc
  rwa [he] at hc


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedModelAssembly.G2Coordinates

end
