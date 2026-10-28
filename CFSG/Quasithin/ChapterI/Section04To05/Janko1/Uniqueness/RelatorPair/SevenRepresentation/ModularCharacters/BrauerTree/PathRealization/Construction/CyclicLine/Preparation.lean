module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.Inputs
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.LocalIndex
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.Tree
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.Roots

/-!
# Preparation of the genuine principal eleven-block line

The specified congruence block has eleven ordinary rows, all real. Integral
roots and a reduction map are constructed at its actual prime, over the
literal `ElevenClosure`. For a module-valued tree, the principal character's
degree one forces exactly one incident edge.

The tree existence theorem (Feit VII.2.11--15, VII.6.8) and real-valency
theorem (VII.2.24, VII.9.2) remain separate obligations. These preparations
do not assert existence of simple or projective edge modules. Final ordering
and assembly of `RealLine` belong here once those obligations are proved.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open scoped Classical
open Representation.CyclicDefect.PrimeOrderRealLine
open ModularBlock.PrincipalBlockConstruction

variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- The given identification is an exhaustive identification of eleven rows. -/
public theorem principalBlock_card (b : PrincipalBlockIdentification d) :
    b.data.block.card = 11 := by
  classical
  have heq : b.data.block =
      (Finset.univ.filter fun i => ¬ 11 ∣ ordinaryDegree i).map b.rows.toEmbedding := by
    ext j
    obtain ⟨i, rfl⟩ := b.rows.surjective j
    simp [b.membership]
  rw [heq, Finset.card_map]
  decide

/-- Realness is transported to the actual block's ordinary character family. -/
public theorem principalBlock_characters_real (b : PrincipalBlockIdentification d)
    (i : b.data.I) (c : ConjClasses G) :
    star (b.data.chi i c) = b.data.chi i c := by
  obtain ⟨j, rfl⟩ := b.rows.surjective i
  rw [b.characters]
  exact ordinaryCharacters_real d j c

/-- The root correspondence can use the very same prime as the given block. -/
public theorem exists_principalBlock_compatibleRoots (b : PrincipalBlockIdentification d)
    (horder : Nat.card G = 175560) :
    Nonempty (CompatibleRoots b.data ElevenClosure 15960) := by
  exact exists_compatibleRoots b.data 15960 (by rw [horder]; decide)

/-- The actual lift used for the tree can be obtained from these compatible
integral roots, since 15960 is prime to eleven. -/
@[expose] public noncomputable def principalBlock_rootLift (b : PrincipalBlockIdentification d)
    (r : CompatibleRoots b.data ElevenClosure 15960) :
    Representation.CyclicRootLift ElevenClosure 15960 := by
  let : NeZero (15960 : ElevenClosure) := ⟨by
    exact (CharP.cast_eq_zero_iff ElevenClosure 11 15960).not.mpr (by decide)⟩
  exact r.lift

/-- In any genuine module-valued tree for this block, the principal row is an
endpoint. No endpoint assumption is added to the cyclic-defect construction. -/
public theorem principalBlock_principal_endpoint (b : PrincipalBlockIdentification d)
    {L : Representation.CyclicRootLift ElevenClosure 15960}
    (t : Tree b.data.chi b.data.block 11 10 L) :
    (t.incident ⟨b.data.principal, b.data.principal_mem⟩).card = 1 := by
  apply t.incident_card_eq_one (by decide)
  rw [b.data.principal_eq, ordinaryPrincipalCharacter_apply]

/-- The endpoint statement in the literal simple graph of ordinary block rows. -/
public theorem principalBlock_principal_graph_degree (b : PrincipalBlockIdentification d)
    {L : Representation.CyclicRootLift ElevenClosure 15960}
    (t : Tree b.data.chi b.data.block 11 10 L) :
    (endpointGraph t.left t.right).degree ⟨b.data.principal, b.data.principal_mem⟩ = 1 := by
  rw [t.graph_degree_eq_incident_card]
  exact principalBlock_principal_endpoint b t

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
