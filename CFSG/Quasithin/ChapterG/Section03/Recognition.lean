module

public import CFSG.Quasithin.ChapterG.Section03.Source
public import CFSG.Quasithin.ChapterG.Section03.Recognition.PlaneSeed
public import CFSG.Quasithin.ChapterG.Section03.Recognition.Boundary
public import CFSG.Quasithin.ChapterG.Section03.Recognition.FixedVectorObstruction
public import CFSG.Quasithin.ChapterG.Section03.Recognition.Reduced.Blocks
public import CFSG.Quasithin.ChapterG.Section03.Recognition.Reduced.Irreducible
public import CFSG.Quasithin.ChapterG.Section03.Recognition.Reduced.Irreducible.Enlargement
public import CFSG.Quasithin.ChapterG.Section03.Recognition.Reduced.TwoCore

/-!
# Full-action recognition with trivial two-core

The root geometry, finite-dimensional block bounds, plane seeds, and moving
configuration boundaries are proved. The actual restriction to every plane
seed is surjective. The finite maximality lemma makes the remaining
configuration-enlargement obligation explicit.

For the separate specialization with trivial intrinsic two-core, `Reduced`
proves that each canonical block has a faithful root-generated spanning orbit
with trivial two-core and at least four roots at each center. Its quotient by
the common fixed space is faithful and irreducible and retains these root
inputs. `Recognition.Reduced.Irreducible` proves that an irreducible action with
these root inputs is the full linear group. It constructs a root-form seed and
envelope and uses global irreducibility to remove the invariant annihilator.
The whole orbit is then a full configuration that strictly enlarges each proper
configuration. `Reduced.TwoCore` combines this with fixed-space quotient lifting
to identify every block action image with its full linear group. The theorem
`fullAction_of_hypotheses_of_twoCore_eq_bot` below consequently proves the exact
`FullAction` conclusion for the canonical blocks, with the extra two-core
hypothesis imposed on the original faithful acting group.

The unconditional `fullAction_of_hypotheses` is not asserted: the point
stabilizer in `GL₄(2)` supplies a source obstruction. Its failure of `FullAction`
is proved in `PointStabilizerObstruction.not_fullAction`, while the accompanying
GAP diagnostic verifies the quotient-rank premise and identifies the failed
source step. Formal certification of that example's rank premise remains open.
The trivial-two-core specialization does not assert unrestricted G.3.1.

Source: Aschbacher--Smith, G.3.1, printed pp.337--338.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section03

open BinaryLinear BinaryTransvectionGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The source-use specialization of full-action recognition with trivial
two-core in the actual faithful acting group. The block action images inherit
this guard through the proved normality and faithful restriction reductions. -/
theorem fullAction_of_hypotheses_of_twoCore_eq_bot
    {G : Subgroup (BinaryLinear.GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) (hcore : pCore 2 G = ⊥) : FullAction G Δ := by
  refine ⟨?_, h.block_dimension_ge_two⟩
  intro i
  let ρ := spanAction G i.val
  let : Finite ρ.range := Finite.of_surjective ρ.rangeRestrict
    ρ.rangeRestrict_surjective
  exact MonoidHom.range_eq_top.mp
    ((Reduced.block_rootGeneratedOrbit h hcore i).eq_top_of_twoCore_eq_bot
      (Reduced.blockImage_twoCore_eq_bot h hcore i))

end CFSG.Quasithin.ChapterG.Section03
