module

public import CFSG.Quasithin.ChapterI.Section02.ModuleCovers.G2
public import Theory.Representation.G2OrthogonalCover.SylowFlag

/-!
# I.2.3(1)(a),(c): the Sylow flag in the G₂′ orthogonal model

Every Sylow subgroup of the actual derived split G₂ group is conjugate to the
intersection of the positive-root group with that derived group. The natural
module has a unique invariant line and plane for this Sylow. Consequently the
source-selected subspaces are the transported marked flag, with no alignment
premise. Their literal preimages in the trace-zero cover have the asserted
singular point and central long-root commutator-plane complements to the fixed
radical. This includes the genuine G₂(2)′ model.

The universal-cover comparison and the original ambient G = LT action are
assembled by the parent modules. Here the assertion concerns the concrete
orthogonal model and its original projection, and supplies precisely its
Sylow-dependent clauses.

Source: Aschbacher–Smith, Lemma I.2.3(1)(a),(c), printed p.413 / PDF p.424,
combined manuscript of 1 March 2004.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterI.ModuleCovers.G2
open Representation Representation.OneCohomology
open Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open Atlas.G2.Natural.OrthogonalCover.SylowFlag
variable (F : Type*) [Field F] [CharP F 2] [Finite F]

/-- The genuine (a),(c) geometry on every source-selected natural flag. The
point and root group are transported by the same actual element of G₂′, and
the radical is the fixed space of the original seven-dimensional action. -/
theorem sylow_fixed_point_and_long_root_plane
    (Q : Sylow 2 (commutator (Atlas.G2.Model F)))
    (V1 V2 : Submodule F (Space F))
    (h1 : ∀ t : (Q : Subgroup (commutator (Atlas.G2.Model F))),
      V1 ≤ V1.comap (derivedAction F t.val))
    (d1 : Module.finrank F V1 = 1)
    (h2 : ∀ t : (Q : Subgroup (commutator (Atlas.G2.Model F))),
      V2 ≤ V2.comap (derivedAction F t.val))
    (d2 : Module.finrank F V2 = 2) :
    ∃ g : commutator (Atlas.G2.Model F),
      (Q : Subgroup (commutator (Atlas.G2.Model F))) = movedSylow F g ∧
      V1 = movedLine F g ∧ V2 = movedPlane F g ∧
      movedRoot F g ≤ (Subgroup.center (Q : Subgroup (commutator (Atlas.G2.Model F)))).map
        (Q : Subgroup (commutator (Atlas.G2.Model F))).subtype ∧
      V1.comap (mk F) = fixed ((OrthogonalCover.action F).comp
        (Q : Subgroup (commutator (Atlas.G2.Model F))).subtype) ∧
      V1.comap (mk F) = movedPoint F g ⊔ fixed (OrthogonalCover.action F) ∧
      Disjoint (movedPoint F g) (fixed (OrthogonalCover.action F)) ∧
      Module.finrank F (movedPoint F g) = 1 ∧
      (∀ x ∈ movedPoint F g, form F x = 0) ∧
      (∀ R : Submodule F (TraceZero F), R ≤ V1.comap (mk F) →
        Module.finrank F R = 1 → (∀ x ∈ R, form F x = 0) → R = movedPoint F g) ∧
      Module.finrank F (Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype)) = 2 ∧
      (∀ x ∈ Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype), form F x = 0) ∧
      Disjoint (Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype))
        (fixed (OrthogonalCover.action F)) ∧
      V2.comap (mk F) =
        Coinvariants.ker ((OrthogonalCover.action F).comp (movedRoot F g).subtype) ⊔
          fixed (OrthogonalCover.action F) := by
  simpa only [fixed_eq_scalarLine] using selected_flag_geometry F Q V1 V2 h1 d1 h2 d2

end CFSG.Quasithin.ChapterI.ModuleCovers.G2
