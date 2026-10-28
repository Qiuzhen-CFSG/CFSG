module

public import CFSG.Quasithin.Chapter3.Section02.SourceThompson
public import CFSG.Quasithin.Chapter3.Section01.E23Input

/-!
# Applying E.2.3 to the original FSU contradiction branch

Nonzero C_{V_M}(X) and source uniqueness force the Sylow omega-center to
be noncentral in every H*. If J(T) centralizes the original V, the proved
intrinsic qrc argument supplies all E.2.3 hypotheses for that same H and
the same omega-orbit. Both original source actor alternatives remain.

This is the actual E.2.3 input in the proof of 3.2.2(6), through 3.1.7.
The factor and Sylow conclusions are supplied by the independent E.2.3 owner.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.575–579 and 216–217.
-/


public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  (T : Sylow 2 G) (X M : Subgroup G) (hXM : X ≤ M) (hTM : (T : Subgroup G) ≤ M)
  [(X.subgroupOf M).Normal]
  (hG : IsSimpleQTKE K G) (hM : IsMaximalTwoLocal M)
  (hX : pResidual 2 (X.subgroupOf M) = ⊤)
  (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
    le_normalizer_of_normal)
  (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G)))))
  (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
    (X.subgroupOf (X ⊔ (T : Subgroup G))) I)

local notation "V₀" => ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I
local notation "V_M" => componentOrbit V₀ M
local notation "V_T" => componentOrbit V₀ (T : Subgroup G)

include hXM hTM hG hM hX hc hI

open Stellmacher

theorem source_reduced_seed_e23_hypotheses
    (hfix : V_M ⊓ centralizer (X : Set G) ≠ ⊥)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V_T : Set G))
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M) :
    IsSQTK K Y ∧ generalizedFitting Y = pCore 2 Y ∧
      ChapterB.IsMinimalParabolicOver (T.subtype hY.1.1.2) ⊤ ∧
      IsPReduced 2 ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y).subgroupOf Y) ∧
      ¬ elementaryAbelianMaxJ
          ((T.subtype hY.1.1.2 : Sylow 2 Y) : Subgroup Y) ≤
        centralizer (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y).subgroupOf Y) : Set Y) := by
  have hq := source_reduced_seed_qrc_hypotheses T X M hXM hTM hG hM hX hc I hI hY
  exact hq.e23_hypotheses hG hM hu hJ
    (source_reduced_seed_omega_center_not_central T X M hXM hTM hG hM hX hc I hI hfix hu hY)

end CFSG.Quasithin.Chapter3.Section02
