module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.TransferIndex
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.FixedLift.Centralizers

/-!
# The same U-action in the source's two conjugation conventions

Both the orthogonal actor and the intrinsic automorphism action on V have
the literal centralizer as their kernel. The first isomorphism theorem
therefore transports the order-four image assertion without any choice
of an automorphism-group model.

Source: Aschbacher–Smith, 15.3.51(2a), 15.3.59, printed pp.1145,1149.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open Core.ResidualGeneration
variable {G : Type*} [Group G] {M V : Subgroup G}

theorem conjugation_range_card_eq (a : NaturalOrthogonalAction M V)
    (U : Subgroup G) (hUM : U ≤ M) (hUV : U ≤ normalizer (V : Set G)) :
    Nat.card (conjugationOnV U V hUV).range = Nat.card (a.image U) := by
  let f := a.actor.comp (inclusion hUM)
  have hk : f.ker = (conjugationOnV U V hUV).ker := by
    rw [conjugationOnV_ker, ← MonoidHom.comap_ker, a.ker_actor]
    rfl
  have hr : f.range = a.image U := by
    rw [MonoidHom.range_comp,inclusion_range]
    rfl
  rw [← index_ker,← hk,index_ker,hr]

theorem conjugation_subgroup_image_card_eq (a : NaturalOrthogonalAction M V)
    (T U : Subgroup G) (hTM : T ≤ M) (hUT : U ≤ T)
    (hTV : T ≤ normalizer (V : Set G)) :
    Nat.card ((U.subgroupOf T).map (conjugationOnV T V hTV)) =
      Nat.card (a.image U) := by
  let f := (conjugationOnV T V hTV).comp (inclusion hUT)
  have hr : f.range = (U.subgroupOf T).map (conjugationOnV T V hTV) := by
    rw [MonoidHom.range_comp,inclusion_range]
  have he : f = conjugationOnV U V (hUT.trans hTV) := by
    ext u v
    rfl
  rw [← hr,he]
  exact conjugation_range_card_eq a U (hUT.trans hTM) (hUT.trans hTV)

theorem fixedLift_action_card_eq (a : NaturalOrthogonalAction M V)
    (Z ZS : Subgroup G) (hUM : closureU Z ZS ≤ M)
    (hUV : closureU Z ZS ≤ normalizer (V : Set G)) :
    Nat.card (ResidualOrbits.Extraspecial.FixedLift.actionOnV hUV).range =
      Nat.card (a.image (closureU Z ZS)) :=
  conjugation_range_card_eq a (closureU Z ZS) hUM hUV

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
