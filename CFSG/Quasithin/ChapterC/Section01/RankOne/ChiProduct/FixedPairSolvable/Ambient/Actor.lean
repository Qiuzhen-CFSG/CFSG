module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ComponentSource.Selection
/-!
# Cubic seed selection in a solvable faithful action

The original local best-offender commutator identity invokes B.1.10 and the
B.1.13 selection step. Solvability excludes every component, so the actual
seed has order three and lies in the center of the Fitting subgroup. It is
therefore subnormal, without an additional classification assumption.

Source: Aschbacher--Smith B.1.13 and C.1.27, printed pp.73,132--133.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Ambient
variable {G V : Type*} [Group G] [Finite G] [Group.IsSolvable G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem solvable_seed_subnormal
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hc : pCore 2 G = ⊥) (K T : Subgroup G)
    (hk : IsQuasisimple K ∨ Nat.card K = 3)
    (hs : (K.subgroupOf (K ⊔ T)).IsSubnormal)
    (hm : K = ⁅K,generatedBy {A | IsBestOffender ρ A} T⁆) :
    Nat.card K = 3 ∧ K.IsSubnormal := by
  rcases ComponentSource.central_fitting_or_moved_component ρ hf hc K T hk hs hm
      with hz | ⟨L,hL,_⟩
  · exact ⟨hz.1,ComponentSource.subnormal_of_le_fitting_center K hz.2⟩
  · let : IsQuasisimple L := hL.2
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    exact (Group.IsPerfect.not_isSolvable L inferInstance).elim
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Ambient
