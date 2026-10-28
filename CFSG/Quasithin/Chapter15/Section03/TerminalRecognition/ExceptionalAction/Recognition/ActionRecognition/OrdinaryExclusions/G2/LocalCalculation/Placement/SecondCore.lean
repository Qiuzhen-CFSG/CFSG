module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.LongCore
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The strict residual-core inequality on the other binary G₂ parabolic

The short-root involution lies in the second parabolic's two-core but outside
the derived group. Its two-residual, and hence the core of that residual, lies
inside the derived group. Subnormal core monotonicity makes the inclusion
strict. In particular, the strict inequality on printed p.1155 cannot by
itself select the first parabolic in the full G₂(2) quotient.

This is a diagnostic for the subgroup-recognition step in Aschbacher–Smith,
final proof of 15.3.1, printed p.1155; it is not a counterexample to the source
configuration with all of its additional hypotheses. Root conventions and
license are inherited from the imported ATLAS model.
-/

public section

open Subgroup Atlas.G2 Atlas.G2.BinaryParabolicPair

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement
private theorem residual_le_derived (P : Subgroup (Model (ZMod 2))) :
    (pResidual 2 P).map P.subtype ≤ DerivedModel := by
  apply (map_pResidual_le 2 P.subtype).trans
  apply sInf_le
  refine ⟨inferInstance, ?_⟩
  apply IsPGroup.of_card (n := 1)
  rw [← Subgroup.index_eq_card, DerivedModel, commutator_eq_longRootClosure,
    BinaryException.index_H]
  rfl

/-- The second parabolic also satisfies the strict core inequality. Thus this
inequality alone does not distinguish the first source parabolic. -/
theorem second_residual_core_strict :
    ((pResidual 2 BinaryCore.secondParabolic).map
      BinaryCore.secondParabolic.subtype).pCoreIn 2 <
      BinaryCore.secondParabolic.pCoreIn 2 := by
  let P := BinaryCore.secondParabolic
  let R := (pResidual 2 P).map P.subtype
  have hn : (R.subgroupOf P).Normal := by
    change ((pResidual 2 P).map P.subtype |>.comap P.subtype).Normal
    rw [comap_map_eq_self_of_injective P.subtype_injective]
    infer_instance
  apply lt_of_le_of_ne (pCoreAmbient_mono_of_isSubnormalIn R P 2
    (map_subtype_le _) hn.isSubnormal)
  intro he
  have hs : shortRoot ∈ P.pCoreIn 2 := by
    change shortRoot ∈ (LieParabolicSetup.parabolic₂ (F := ZMod 2)).pCoreIn 2
    rw [EvenLocal.parabolic₂_pCoreIn]
    exact ⟨![0,0,0,0,0,1], rfl, by simp [shortRoot, unipotentProduct]⟩
  have hd : R.pCoreIn 2 ≤ DerivedModel := (pCoreIn_le 2 R).trans (residual_le_derived P)
  change R.pCoreIn 2 = P.pCoreIn 2 at he
  rw [← he] at hs
  exact shortRoot_not_mem_derived (hd hs)

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement
