module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Source
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Parameters
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Geometry

/-!
# The original L₃ parameter and symmetric plane at G,T

The proved hyperplane-centralizer bound and the actual normalizer action give
the strict globalS bound. The B.4.8 calculation then symmetrizes any literal
noncommuting conjugate supplied by 12.4.1. Neither step uses fusion.
Source: Aschbacher–Smith, B.4.8(2), 12.4.8–9, pp.91,815–816.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At
open Section02 SmallFusion ChapterE
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Both numerical inputs are proved from the same original source configuration. -/
theorem globalS_gt_one_of_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥) :
    letI := D.elementary
    1 < globalS V :=
  globalS_gt_one E hne (normalizer_action h structural E hne)
    (CentralizerBound.hyperplane_centralizers h structural E hne)

/-- The literal conjugation map preserves the nontrivial commutator plane. -/
theorem symmetric_plane_of_source_conjugate
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥)
    (g : G) (hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hbound : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    ∃ k : G,
      V.map (MulAut.conj k).toMonoidHom = V.map (MulAut.conj g).toMonoidHom ∧
      V.map (MulAut.conj k).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj k).toMonoidHom⁆ ∧
      (⁅V, V.map (MulAut.conj k).toMonoidHom⁆).map (MulAut.conj k).toMonoidHom =
        ⁅V, V.map (MulAut.conj k).toMonoidHom⁆ ∧
      ⁅V, V.map (MulAut.conj k).toMonoidHom⁆ ≠ ⊥ ∧
      Nat.card (⁅V, V.map (MulAut.conj k).toMonoidHom⁆ : Subgroup G) = 4 :=
  symmetric_plane_of_noncommuting_conjugate E hne
    (normalizer_action h structural E hne) g hcomm hbound

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At
