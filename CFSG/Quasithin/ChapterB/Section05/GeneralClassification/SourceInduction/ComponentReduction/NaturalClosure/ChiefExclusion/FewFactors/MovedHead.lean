module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FewFactors.Head
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.Symmetry

/-!
# The two component actions on the moved space and its head

Both representations here restrict the original action to W = [V,L].
The second restriction exists because distinct components commute, and the
supplied cross commutator proves that restriction nontrivial. The canonical
head construction then gives the second component's action on the L-head
of this same W, with no replacement of the component or the vector space.

This supplies the common interface for independently proving the head
multiplicity bound and lifting triviality from the head. No head detection
or multiplicity statement is asserted here.

Source: Aschbacher–Smith, B.5.9, printed p.108, the c = 2 centralizer
argument (1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The original L-action on W = [V,L]. -/
noncomputable def componentMoved (L : Subgroup G) : Subrepresentation (ρ.comp L.subtype) :=
  invariantSubspace ρ L (moved ρ L) (subspaceCommutator_invariant ρ ⊤ L)

/-- Distinct components commute, so the second component preserves this same W. -/
noncomputable def secondMoved {A L : Subgroup G} (hL : IsComponent G L)
    (d : SecondComponent ρ A L) : Subrepresentation (ρ.comp d.second.subtype) :=
  invariantSubspace ρ d.second (moved ρ L)
    (subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by simp))
      ((le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp
          (hL.commutator_eq_bot_of_ne d.isComponent d.distinct))).trans
        (centralizer_le_normalizer _)))

/-- The first action with its literal moved-space carrier displayed. -/
noncomputable def componentAction (L : Subgroup G) :
    Representation (ZMod 2) L (moved ρ L) := (componentMoved ρ L).toRepresentation

/-- The second action with the identical carrier, retaining its subgroup inclusion. -/
noncomputable def secondAction {A L : Subgroup G} (hL : IsComponent G L)
    (d : SecondComponent ρ A L) : Representation (ZMod 2) d.second (moved ρ L) :=
  (secondMoved ρ hL d).toRepresentation

/-- The restrictions commute because the two original component embeddings commute. -/
theorem moved_commute {A L : Subgroup G} (hL : IsComponent G L)
    (d : SecondComponent ρ A L) (l : L) (m : d.second) :
    componentAction ρ L l * secondAction ρ hL d m =
      secondAction ρ hL d m * componentAction ρ L l := by
  ext v
  change ρ l (ρ m v) = ρ m (ρ l v)
  simp only [← Module.End.mul_apply, ← map_mul]
  rw [(commutator_eq_bot_iff_le_centralizer.mp
    (hL.commutator_eq_bot_of_ne d.isComponent d.distinct)) l.property m m.property]

/-- The given cross commutator detects nontriviality of this actual restricted action. -/
theorem movedAction_ne_one {A L : Subgroup G} (hL : IsComponent G L)
    (d : SecondComponent ρ A L) : secondAction ρ hL d ≠ 1 := by
  intro he
  apply d.cross_action
  apply (subspaceCommutator_eq_bot_iff ρ (moved ρ L) d.second).mpr
  intro v hv m
  exact congrArg Subtype.val
    (DFunLike.congr_fun (DFunLike.congr_fun he m) (⟨v, hv⟩ : moved ρ L))

/-- The actual second component acting on the L-head of W. -/
noncomputable def secondHead {A L : Subgroup G} (hL : IsComponent G L)
    (d : SecondComponent ρ A L) :=
  Head.action (componentAction ρ L) (secondAction ρ hL d)
    (moved_commute ρ hL d)

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors
