module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveMaximal
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveSaturation
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualImages
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.LocalIndex
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The original two componentwise Sylow extensions in E.2.3

On each of the original residual factors, the paired S₅ marking identifies
the original maximal intersection as its point stabilizer. The actual
Baumann image, kernel saturation and local cubic conjugates then construct
an index-two Sylow extension inside the prescribed conjugate span. The
source kernel is only two-closed; its order is never assumed to be a power
of two. Both factor choices use the same original marked quotient.

The internal Structure import is used only to identify the maximal core
with its normal core when deriving kernel containment in the maximal.
Source: Aschbacher--Smith B.6.10, C.1.24 and E.2.3(3).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction BinaryPermutation ChapterC.SymmetricFive
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem paired_component_index_two_sylow
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    ∀ K ∈ ({factorResidual q Y d.first, factorResidual q Y d.second} : Set (Subgroup G)),
      ∃ S : Subgroup G, IsSylowSubgroupIn S (K ⊔ baumann (T : Subgroup G)) ∧
        baumann (T : Subgroup G) ≤ S ∧
        ((baumann (T : Subgroup G)).subgroupOf S).index = 2 ∧
        S ≤ conjugateSpanBy (baumann (T : Subgroup G)) (K ⊓ minimalParabolicMax T hP) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let S := baumann (T : Subgroup G)
  let j := Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom
  have hj : Function.Injective j := Y.subtype_injective.comp c.action.groupEquiv.symm.injective
  have hS : IsPGroup 2 S := T.isPGroup'.to_le inf_le_left
  have hkerM : q.ker ≤ minimalParabolicMax T hP := by
    rw [hker]
    exact (RankOneBaumann.reduced_centralizer_le_core T hP U hU hJ).trans (normalCore_le _)
  obtain ⟨_,a,b,hab⟩ := paired_thompson_baumann_of_symmetric_model T hP U hU hJ q hq hker d c hexchange
  have hmax := source_paired_maximal_images T hP U hU hJ q hq hker d c hexchange a b hab
  have hsat := (paired_alpha_and_saturation_of_symmetric_model T hP U hU hJ q hq hker d c hexchange).2.2
  rw [←hker] at hsat
  have hgen := paired_residual_factors_generate T hP U hU hJ q hq hker d
  have hk (K : Subgroup G) (hK : K ≤ pResidual 2 G) :
      IsSylowSubgroupIn (S ⊓ q.ker) ((K ⊔ S) ⊓ q.ker) :=
    Paired.sylowIn_mono (hS.to_le inf_le_left) (inf_le_inf_right _ le_sup_right)
      (inf_le_inf_right _ (sup_le_sup_right hK _)) hsat
  dsimp only
  intro K hK
  rcases hK with rfl | hK
  · exact Paired.first_sylow_extension q j hj S _ (minimalParabolicMax T hP) hS hkerM a b hab
      (paired_symmetric_first_residual_image α q hq d c) hmax.1
      (hk _ (by rw [←hgen]; exact le_sup_left))
  · have he : K = factorResidual q Y d.second := hK
    subst K
    exact Paired.second_sylow_extension q j hj S _ (minimalParabolicMax T hP) hS hkerM a b hab
      (paired_symmetric_second_residual_image α q hq d c) hmax.2
      (hk _ (by rw [←hgen]; exact le_sup_right))
end CFSG.Quasithin.ChapterE.ThompsonAction
