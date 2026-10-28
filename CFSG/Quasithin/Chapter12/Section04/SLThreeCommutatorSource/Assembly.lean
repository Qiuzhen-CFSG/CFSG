module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Contracts
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Setup
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Parameters
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Geometry

/-!
# Assembly of the original L₃ commutator branch

The proved known-simple uniqueness theorem and the marked fixed line give
the centralizer hypothesis of 12.4.1. The hyperplane-centralizer input to
12.4.8 and the B.4.8 involution calculation give s(G,V)>1. Apply 12.4.1,
then construct and symmetrize the actual commutator plane.

The three independent source inputs are named in Contracts. Their proofs,
and the two earlier 12.2 implications, remain obligations of the final
source assembly. This theorem is conditional and does not discharge them.
The independent fusion branch is not used.

Source: Aschbacher–Smith, 12.4.1, 12.4.3, 12.4.8–9 and the final proof of
12.4.2, printed pp.812–816.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
open Section02 SmallFusion
universe u

/-- The original conjugate and invariant commutator plane, conditional
on the explicitly named independent earlier source implications. -/
theorem source_commutator_plane
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (normalizerAction : NormalizerAction.{u})
    (centralizers : HyperplaneCentralizers1248.{u})
    (conjugate : NoncommutingConjugate1241.{u})
    {G : Type u} [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  let _ := D.elementary
  obtain ⟨E⟩ := marked G T L V h D hmodel hne
  obtain ⟨z, _, _, _, _, _, hZ⟩ := fixed_involution_setup_of_card_two h D structural
    (E.fixed_card_eq_two hne)
  have hN := normalizerAction G T L V h D hmodel hne
  have hs := globalS_gt_one E hne hN (centralizers G T L V h D hmodel hne)
  obtain ⟨g, hg, hbound⟩ := conjugate G T L V h D hmodel hne hZ hs
  obtain ⟨k, _, hnorm, hfixed, hsym, hne', _⟩ :=
    symmetric_plane_of_noncommuting_conjugate E hne hN g hg hbound
  exact ⟨k, hnorm, hfixed, hsym, hne'⟩

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
