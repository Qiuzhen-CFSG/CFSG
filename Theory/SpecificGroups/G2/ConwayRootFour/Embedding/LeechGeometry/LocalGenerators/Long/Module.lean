module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Setup
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Module.Model
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Module.Faithfulness
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Module.Natural

/-!
# Long Leech coordinates from the local embedding

An additive copy of the natural SL₃(4) module supplies all six coordinates:
add it to its translate by the literal graph involution, correcting the
permutation of the dual coordinates. Three elementary-root displacement
products prove injectivity; the existing fixed-space dimension bound proves
surjectivity. This constructs every field of `LongFrame`, including its exact
block and graph tests. Explicit additive maps also handle a field twist or a
dual initial submodule.

For any `LocalEmbedding`, the restricted-action kernel bound and the actual
SL₃(4)-with-graph structure prove faithfulness. The small binary representation
catalogue then supplies the required additive natural submodule. Combining
these proofs yields `nonempty_longFrame_of_localEmbedding`, with no remaining
representation premise. The unconditional long-frame construction still needs
the separate construction of the local embedding.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
-/

open Matrix Atlas.Conway Atlas.Lattices
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
open OctonionLocals ModuleModel
open PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
@[expose] public noncomputable section

/-- One additive natural submodule gives the entire literal long frame.
The separate representation argument must construct this submodule. -/
def longFrameOfNatural (E : LocalEmbedding) (n : Three F →+ fixedSpace)
    (hninj : Function.Injective n)
    (hn : ∀ A u, E.action (blockIn A) (n u) = n (A.val *ᵥ u)) : LongFrame where
  long := E.hom.comp blockIn
  swap := E.hom graphIn
  long_mem A := E.mem_centralizer (blockIn A)
  swap_mem := E.mem_centralizer graphIn
  coordinates := fixedSpace.subtype.toAddMonoidHom.comp (graphCoordinates E.action n)
  coordinates_injective :=
    Subtype.val_injective.comp (graphCoordinates_injective E.action n hninj hn)
  coordinates_range := coordinates_range_of_single _
    (Subtype.val_injective.comp (graphCoordinates_injective E.action n hninj hn))
    (fun j a => (graphCoordinates E.action n (Pi.single j a)).property)
  on_long A j a :=
    congrArg Subtype.val (graphCoordinates_block E.action n hn A (Pi.single j a))
  on_swap j a :=
    congrArg Subtype.val (graphCoordinates_graph E.action n (Pi.single j a))

/-- Remove a proved coefficient-field twist by the actual additive coordinate map. -/
def longFrameOfTwistedNatural (E : LocalEmbedding) (σ : F ≃+* F)
    (n : Three F →+ fixedSpace) (hninj : Function.Injective n)
    (hn : ∀ A u, E.action (blockIn A) (n u) = n (A.val.map σ *ᵥ u)) : LongFrame :=
  longFrameOfNatural E (untwistNatural σ n) (untwistNatural_injective σ n hninj)
    (untwistNatural_equivariant E.action σ n hn)

/-- A dual initial submodule becomes natural under the corrected graph translate. -/
def longFrameOfDual (E : LocalEmbedding) (n : Three F →+ fixedSpace)
    (hninj : Function.Injective n)
    (hn : ∀ A u, E.action (blockIn A) (n u) =
      n (BlockRealization.cofactor A.val *ᵥ u)) : LongFrame :=
  longFrameOfNatural E (graphNatural E.action n)
    (graphNatural_injective E.action n hninj) (graphNatural_equivariant E.action n hn)

/-- The actual local embedding supplies the full long frame, including the
injective, surjective coordinates and the literal block and graph action tests.
Faithfulness and natural-submodule existence are discharged internally. -/
theorem nonempty_longFrame_of_localEmbedding (E : LocalEmbedding) : Nonempty LongFrame := by
  obtain ⟨n, hninj, hn⟩ := exists_naturalInjection_of_faithful E E.action_injective
  exact ⟨longFrameOfNatural E n hninj hn⟩

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
