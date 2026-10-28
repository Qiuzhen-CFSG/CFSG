module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source.Rank

/-!
# Solvable Thompson factorization on the original maximal local

B.2.16 is applied to M, with the actual Sylow subgroup T restricted to M.
Its omega-center closure is precisely the internal V(M), and 15.4.8 makes
its centralizer the two-core of M. Thus its literal star quotient is
identified with the fixed M/O₂(M) coordinates of the Y-family construction.
The exceptional factor count is one or two by quasithin three-rank.

The noncentrality hypothesis is exactly source 15.4.11(3), whose proof uses
14.1.4; it is not part of the original empty-family hypothesis. The full
B.2.16 theorem remains the universal earlier input. This module supplies
its actual-domain application for the opening paragraph of 15.4.12,
Aschbacher–Smith, printed pp.1160–1161.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonSource
open Chapter1.RadicalNormalizers.ThompsonSource ModuleStructure
universe u
variable {G : Type u} [Group G]

/-- The omega-center of the restricted Sylow has the original ambient seed. -/
theorem restricted_omega (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) :
    omegaOneCenterAmbient (T.subtype hTM : Subgroup M) =
      (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf M := by
  apply map_injective M.subtype_injective
  rw [← omegaOneCenterAmbient_map_injective M.subtype M.subtype_injective,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM]
  exact (map_subgroupOf_eq_of_le (show omegaOneCenterAmbient (T : Subgroup G) ≤ M from
    fun _ hz => hTM ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)).symm

/-- B.2.16 uses exactly the internal V(M), with no alternate source module. -/
theorem closure_eq_internalModule (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) :
    Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM) =
      internalModule T M := by
  unfold Chapter1.RadicalNormalizers.ThompsonSource.closure internalModule
  rw [restricted_omega]

/-- The source star kernel is the actual two-core of M. -/
theorem star_kernel (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T) :
    centralizer (Chapter1.RadicalNormalizers.ThompsonSource.closure
      (T.subtype hTM) : Set M) = pCore 2 M := by
  rw [closure_eq_internalModule]
  exact internal_centralizer T M hTM hC

/-- The actual B.2.16 quotient agrees with the fixed Y-construction quotient. -/
noncomputable def coreQuotientEquiv (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T) :
    CentralQuotient (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM)) ≃*
      CoreQuotient M :=
  QuotientGroup.quotientMulEquivOfEq (star_kernel T M hTM hC)

/-- The comparison preserves the original quotient homomorphisms pointwise. -/
@[simp] theorem coreQuotientEquiv_apply (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T) (m : M) :
    coreQuotientEquiv T M hTM hC
      (starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM)) m) =
        quotientMap M m := rfl

/-- Noncentrality of the actual local module supplies the source exceptional
family, including its complete actions and the sharp one-or-two factor bound. -/
theorem exceptional [Finite G] {κ : GroupClass} (hB : TheoremB216.{u})
    (hG : IsSimpleQTKE κ G)
    (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hsol : Group.IsSolvable M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hmoved : ⁅localV T M, elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥) :
    ∃ hE : IsElementaryAbelian 2
      (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM)),
      ∃ d : @Exceptional M _ (T.subtype hTM) hE, d.count = 1 ∨ d.count = 2 := by
  have hgf := generalizedFitting_eq_pCore_of_selfCentralizing 2
    (hG.evenCharacteristic T M hM hTM)
  have hc := hB M hsol hgf (T.subtype hTM)
  refine ⟨hc.elementary, ?_⟩
  let := hc.elementary
  have halt := hc.alternatives
  rcases halt with hcentral | hd
  · exfalso
    apply hmoved
    have hj := map_mono (f := M.subtype) hcentral.1
    rw [← elementaryAbelianMaxJ_map_injective _ M.subtype_injective,
      Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM,
      closure_eq_internalModule, map_centralizer_subtype] at hj
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hj.trans inf_le_right))
  · obtain ⟨d⟩ := hd
    refine ⟨d, d.count_eq_one_or_two ?_ ?_⟩
    · rw [star_kernel T M hTM hC]
      exact pCore_isPGroup
    · exact (hG.twoLocal_sqtk hM.1).stronglyQuasithin 3 Nat.prime_three (by decide)

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonSource
