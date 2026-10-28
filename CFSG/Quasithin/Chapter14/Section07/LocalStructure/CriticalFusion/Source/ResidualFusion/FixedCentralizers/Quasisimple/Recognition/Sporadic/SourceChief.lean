module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction.TwoFactorsSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.ChiefBounds

/-!
# The original chief-factor exclusion of J₂ and HS

The two noncentral intervals constructed from the original commutators of K
supply the lower-bound witness for the existing native J₂/HS chief bounds.
The literal component quotient marking and the source involution action are
preserved. No series or chief-count premise remains in the source export.

Source: Aschbacher–Smith 14.7.68(2), printed p.1071; the independent
original13.3.2 and12.2.2 inputs supply [U,O₂(H)]=V₁.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- The actual commutators discharge the earlier lower-chief-count witness. -/
theorem fixedSporadic_not_j2_hs_of_point_commutator
    (u : F.U) {Lu : Subgroup G}
    (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))) {name : SporadicName}
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier)
    (h : SporadicSieve.Case d u Lu α name)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) : name ≠ .j2 ∧ name ≠ .hs := by
  obtain ⟨s,hs0,hs1,hs⟩ := d.exists_K_two_chief_of_point_commutator hcomm
  exact d.fixedSporadic_not_j2_hs_of_two_le u α e h s hs0 hs1 hs

/-- Original earlier source inputs supply the commutator before the native comparison. -/
theorem fixedSporadic_not_j2_hs_of_source
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (u : F.U) {Lu : Subgroup G}
    (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))) {name : SporadicName}
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier)
    (h : SporadicSieve.Case d u Lu α name) : name ≠ .j2 ∧ name ≠ .hs :=
  d.fixedSporadic_not_j2_hs_of_point_commutator u α e h
    (d.U_core_commutator_eq_point_of_source1332 modules structural uniqueness)
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
