module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
/-!
# Natural local-class models from literal quotient coordinates

An isomorphism of the actual centralizer quotient with SL₂, together with
an equivariant surjection from the actual moved group with its fixed kernel,
gives the marked C.1.17 natural module. Both actor and module equivalences
are the canonical quotient equivalences; the intertwining formula retains
the original lift and conjugation.

Source: Aschbacher–Smith C.1.17, printed p.126.
-/
public section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open GlaubermanNiles
variable {B H : Type*} [Group B] [Group H] [Finite H]

theorem naturalModel_of_star_coordinates (b : B →* H)
    (F : Type) [Field F] [CharP F 2] [IsQuasisimple SL(2,F)]
    (c : LocalStar b ≃* SL(2,F))
    (f : moved b →* Multiplicative (Fin 2 → F)) (hf : Function.Surjective f)
    (hk : f.ker = movedFixed b)
    (he : ∀ (a : actorLift b) (w : moved b),
      Multiplicative.toAdd (f (movedConjugate b a w)) =
        specialLinearNatural 2 (c (QuotientGroup.mk' (localKernel b) a))
          (Multiplicative.toAdd (f w))) : Nonempty (NaturalModel b F) := by
  let : IsQuasisimple (LocalStar b) := IsQuasisimple.of_mulEquiv c.symm
  have ht : generalizedFitting (LocalStar b) = ⊤ := generalizedFitting_eq_top_of_quasisimple
  let s := Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)
  let : Group.IsPerfect PSL(2,F) := Group.IsPerfect.ofSurjective (f := s.toMonoidHom) s.surjective
  let ca := ((MulEquiv.subgroupCongr ht).trans topEquiv).trans c
  let aiso := (ca.trans s).trans (topEquiv.symm.trans
    (MulEquiv.subgroupCongr (Group.IsPerfect.commutator_eq_top (G := PSL(2,F))).symm))
  let m := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨{ actorIso := aiso, moduleIso := m, intertwining := ?_ }⟩
  intro a w
  have hc : s.symm (aiso (actorProjection b a) : PSL(2,F)) =
      c (QuotientGroup.mk' (localKernel b) a) := by
    exact s.symm_apply_apply _
  change Multiplicative.toAdd (f (movedConjugate b a w)) = _
  rw [hc]
  exact he a w
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
