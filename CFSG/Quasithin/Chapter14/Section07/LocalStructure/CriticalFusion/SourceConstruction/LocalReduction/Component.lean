module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.Assembly
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The relative component in the two residual alternatives

Both concrete alternatives in 14.7.52 have a quasisimple quotient by
their two-core. The embedded residual K is intrinsically O²(H), hence
is two-perfect and normal in H. The prime-core component criterion
therefore proves K ∈ C(H), with normality relative to H throughout.

This implication removes the separate component premise from the literal
source-data construction once the residual alternatives have been proved.
It does not assume the source datum or assert those alternatives.

Source: Aschbacher–Smith, 14.7.48 and 14.7.52, printed pp.1064–1065.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem quasisimple_of_simple_perfect (A : Type*) [Group A]
    [IsSimpleGroup A] [Group.IsPerfect A] : IsQuasisimple A := by
  have hz : center A = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center A) inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp h))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩

omit [Finite G] in
/-- Both concrete residual alternatives are quasisimple. -/
theorem residual_quasisimple (h52 : AlternatingResidual F ∨ G2Residual F) :
    IsQuasisimple ((K F) ⧸ pCore 2 (K F)) := by
  rcases h52 with he | he
  · obtain ⟨e⟩ := he
    let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    let := quasisimple_of_simple_perfect (alternatingGroup (Fin 5))
    exact IsQuasisimple.of_mulEquiv e.symm
  · obtain ⟨e⟩ := he
    let := Atlas.G2.isSimple_commutator_binary
    let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) := by
      rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
      exact Atlas.G2.BinaryException.H_isPerfect
    let := quasisimple_of_simple_perfect (commutator (Atlas.G2.Model (ZMod 2)))
    exact IsQuasisimple.of_mulEquiv e.symm

omit [Finite G] in
/-- The relative subgroup in H is exactly its intrinsic two-residual. -/
theorem residual_subgroupOf (F : InvariantFlag T V 3) :
    (K F).subgroupOf F.H = pResidual 2 F.H := by
  exact comap_map_eq_self_of_injective F.H.subtype_injective _

/-- The actual two-residual is a C-component once the two source alternatives hold. -/
theorem component_of_residual_alternatives
    (h52 : AlternatingResidual F ∨ G2Residual F) :
    ((K F).subgroupOf F.H).IsCComponent := by
  let e : (K F).subgroupOf F.H ≃* K F := subgroupOfEquivOfLe (map_subtype_le _)
  let q : (((K F).subgroupOf F.H) ⧸ pCore 2 ((K F).subgroupOf F.H)) ≃*
      ((K F) ⧸ pCore 2 (K F)) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let := residual_quasisimple h52
  let := IsQuasisimple.of_mulEquiv q.symm
  apply isCComponent_of_isPPerfect_of_quasisimple_core_quotient (p := 2)
  · rw [residual_subgroupOf]
    exact (inferInstance : (pResidual 2 F.H).Normal).isSubnormal
  · rw [residual_subgroupOf]
    exact isPPerfect_pResidual 2

/-- The conditional source construction no longer needs an independent
component premise. The residual alternatives supply it on the actual H. -/
theorem exists_data_of_residual_branches
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hunique : F.Hz L (normalizer (L : Set G)) = {F.H})
    (h52 : AlternatingResidual F ∨ G2Residual F)
    (h53 : ¬ G2Residual F)
    (h40 : AlternatingResidual F → NaturalRecognition F) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) :=
  exists_data_of_source_branches d h hab hunique
    (component_of_residual_alternatives h52) h52 h53 h40

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
