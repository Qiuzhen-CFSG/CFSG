module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Held.Reduction
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Held.LocalBlocks

/-!
# The Held branch of the local block exclusion

Source: Aschbacher–Smith, 2.3.9(7), printed p.526; GLS3 Table 5.3p.

For the image T of the supplied component Sylow subgroup in the actual
degree-2058 Held carrier, use C_He(Z(T)) and N_He(E(T)), where E(T) joins
all normal elementary subgroups of order 64 in T. Pull both locals back
through L → L/O₂(L) ≃ Held.He and adjoin the entire supplied S.
`Held.LocalGeometry` proves generation, containment in L ∨ S, and the
nontrivial self-centralizing two-cores, allowing S to permute components.

`Held.LocalBlocks` places the first local in C_G(z) and excludes all allowed
blocks in the second using its actual subnormal coordinate images. Combining
these proofs constructs the required block cover without extra geometry or
block premises. The central two-kernel is retained throughout. The parent
sporadic exclusion can apply `LocalSetup.false_of_centralizerBlockCover`;
the seven-case exclusion assembly remains there.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The actual Held local pair with its proved block obstructions. -/
@[expose] noncomputable def heldCentralizerBlockCover (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z :=
  (heldLocalGeometry h d).toCentralizerBlockCover
    (heldLocalGeometry_blockObstruction h d)

/-- The cover uses the two specified quotient preimages adjoined with S. -/
theorem heldCentralizerBlockCover_locals (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    (heldCentralizerBlockCover h d).locals = {heldLocal h d false, heldLocal h d true} :=
  heldLocalGeometry_locals h d

/-- The Held calculation required by the sporadic refinement in 2.3.9(7),
with exactly the source local setup and its actual quotient/action input. -/
theorem nonempty_centralizerBlockCover (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .he) :
    Nonempty (CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z) :=
  ⟨heldCentralizerBlockCover h d⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase

end
