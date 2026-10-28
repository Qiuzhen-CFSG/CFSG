module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SecondKernelAction
public import Theory.GroupTheory.Commutator.ReciprocalFixedPoints

/-!
# No fixed cosets in the actual second-kernel quotient

The natural neighboring center identifies C_Q(V) with Q ∩ G². The
common Sylows and center inclusion make [V,Q] central under the starred
endpoint. Apply three-subgroups rotation with [V,L] = V: any subgroup
of Q fixed by L modulo G² already centralizes V. Consequently the
literal Q/(Q ∩ G²) has no nonzero fixed coset.

These are the earlier (12.1) commutator and common-Sylow inputs and the
proved (12.3)(d) full movement. No Suzuki marking, irreducibility, or
order bound is assumed. This supplies the fixed-point step needed to
combine the geometric seed bounds in SuzukiSeedFixedIndex into the
q⁴ bound; the two-seed generation is a separate remaining source step.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1), (12.3)(d), (12.6), printed pp.178--183.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Every coset fixed by the actual starred action on Q/G² is the identity coset.
This is the group-theoretic fixed-preimage statement, before any dimension bound. -/
theorem source_second_kernel_fixed_preimage (h : HypothesisF11 L S) (i : Bool)
    (T : Sylow 2 (ReducedLayer.star L S (!i)))
    (hT : (T : Subgroup (ReducedLayer.star L S (!i))).map (ReducedLayer.star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (ReducedLayer.star L S i))
    (hR : (R : Subgroup (ReducedLayer.star L S i)).map (ReducedLayer.star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hnat : Noncommuting.HasNaturalCenter (ReducedLayer.star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) i) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1, ReducedLayer.star L S i⁆) :
    let F := reducedFamily L S
    let v := base F i
    commutatorPreimage (Q F v) (ReducedLayer.star L S i) (ballKernel F v 2) =
      Q F v ⊓ ballKernel F v 2 := by
  let F := reducedFamily L S
  let v := base F i
  have hplace : Q F v ≤ ReducedLayer.star L S (!i) :=
    (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  exact fixed_preimage_eq_of_reciprocal_centralizer
    (ReducedLayer.star L S i) (V F v 1) (Q F v) (ballKernel F v 2) (Z F v)
    ((ReducedLayer.star_le_stabilizer i).trans (CommutingTrivial.stabilizer_normalizes_Q F v))
    ((ReducedLayer.star_le_stabilizer i).trans (stabilizer_le_normalizer_ballKernel F v 2))
    ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
    (source_core_span_centralizer_eq_second_kernel h i hplace hnat).symm
    hcomm (ReducedLayer.source_center_centralizes_star_of_neighbor_inclusion h i hzy R hR)
    hfull.symm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
