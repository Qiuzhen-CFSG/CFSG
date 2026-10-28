module
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.Basic
public import Theory.GroupTheory.PerfectNormalizerInner

/-!
# The precise Theorem B outer input and perfect actor transport

The full B-only outer catalogue remains a genuine earlier model input.
Once supplied, central quotient descent proves inner placement for the
actual perfect normalizing actor, with the original central covering kernel.
The separate `Basic` module proves the shared C, alternating and odd PSL₂ rows;
this file does not assert the remaining catalogue.
Source: Aschbacher–Smith 4.4.3, the component argument on printed p.621.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents.TheoremBOuter
open Subgroup Theory.GroupTheory
universe u

/-- The exact full B-model theorem required by the selected-component argument.
This is an input definition, not an asserted Schreier theorem. -/
def SourceInput : Prop :=
  ∀ (S : Type u) [Group S] [Finite S], IsSimpleGroup S → ¬ IsMulCommutative S →
    Section02.IsTheoremBModel S → Group.IsSolvable (MulAut.Outer S)

/-- The source model acts on the literal central quotient of the perfect cover. -/
theorem quasisimple_outer (hOuter : SourceInput.{u})
    {K : Type u} [Group K] [Finite K] [IsQuasisimple K]
    (hK : Section02.IsTheoremBModel (K ⧸ center K)) :
    Group.IsSolvable (MulAut.Outer K) := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    hOuter _ inferInstance (Group.IsPerfect.not_isMulCommutative _) hK
  exact Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))

/-- A perfect subgroup normalizing an actual B-model cover acts by inner
conjugation. The product and centralizer are in its original ambient group. -/
theorem perfect_actor_inner (hOuter : SourceInput.{u})
    {G : Type u} [Group G] [Finite G] (K F : Subgroup G)
    [IsQuasisimple K] [Group.IsPerfect F]
    (hK : Section02.IsTheoremBModel (K ⧸ center K))
    (hF : F ≤ normalizer (K : Set G)) : F ≤ K ⊔ centralizer (K : Set G) := by
  let : Group.IsSolvable (MulAut.Outer K) := quasisimple_outer hOuter hK
  exact Subgroup.perfect_le_sup_centralizer_of_solvable_outer K F hF
end CFSG.Quasithin.ChapterA.Section03.SourceComponents.TheoremBOuter
