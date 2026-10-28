module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.RadicalStructure
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.QuotientActions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.QuotientReduction

/-!
# The central J₂ involution centralizer

The actual five-point action on the representative centralizer is surjective
onto A₅. Its kernel equals the checked radical, whose embedded quaternion and
dihedral factors commute, generate, and meet in their common involution.
Transporting those factors to the intrinsic two-core proves the exact source
extension A₅/(Q₈ * D₈), without imposing a splitting.

This assembles the existing independent radical and quotient-action proofs;
no permutation calculation is repeated. Source: Aschbacher–Smith, combined
manuscript of 1 March 2004, 16.1.5(8), printed p.1172. The noncentral class
and the kernel-centralizer exclusion are separate obligations.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2CentralClass

open Subgroup Theory.GroupTheory

private theorem shape_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : IsQuaternionDihedralProduct G) : IsQuaternionDihedralProduct H := by
  obtain ⟨B, D, hB, hD, hBD, hcomm, hsup⟩ := h
  refine ⟨B.map e.toMonoidHom, D.map e.toMonoidHom,
    hB.map (fun f => (e.subgroupMap B).symm.trans f),
    hD.map (fun f => (e.subgroupMap D).symm.trans f), ?_, ?_, ?_⟩
  · rw [← Subgroup.map_inf B D e.toMonoidHom e.injective,
      Subgroup.card_map_of_injective e.injective]
    exact hBD
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩
    exact (e.map_mul b d).symm.trans ((congrArg e (hcomm b hb d hd)).trans (e.map_mul d b))
  · rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ e.surjective]

open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
open Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.QuotientActions
open Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed

/-- The central involution has the exact Q₈ * D₈ kernel and actual A₅ quotient. -/
theorem t_core_shape : IsJ2CoreExtension (Subgroup.centralizer ({FirstFusion.t} : Set Carrier)) := by
  change IsJ2CoreExtension l₁
  refine ⟨pCore 2 l₁, inferInstance, ?_, ?_⟩
  · exact shape_transport
      (radicalCoreEquiv_of_action card_radical innerAction innerAction_surjective
        (innerAction_ker card_radical)) radical_structure.2
  · exact l₁_quotient_of_radical_action card_radical innerAction innerAction_surjective
      (innerAction_ker card_radical)

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2CentralClass
