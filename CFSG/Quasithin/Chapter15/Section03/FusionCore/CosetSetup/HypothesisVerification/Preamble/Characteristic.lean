module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.GroupTheory.PCoreOvergroup

/-!
# Characteristic two in the preamble to 15.3.48

Even characteristic gives self-centralizing two-cores in the maximal two-locals
M and Mc. This property passes to H because H contains the ambient Sylow
subgroup, and to the actual residual Y because Y is normal inside M.
A finite group with a self-centralizing prime core has no components:
inheritance would make the central prime core of a component self-centralizing.
Its prime-complement core is also trivial, so its generalized Fitting subgroup
is precisely its prime core.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the standing
hypotheses of Section 15.3, pp.1121–1122, and the preamble and clause (a) of
F.9.1, pp.317–318, used in 15.3.48, pp.1141–1142.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Preamble

private theorem generalizedFitting_eq_core {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G) :
    generalizedFitting G = pCore p G := by
  have he : componentLayer G = ⊥ := by
    apply sSup_eq_bot.mpr
    intro K hK
    let := hK.2
    have hk := subnormal_core_selfCentralizing hc K hK.1
    have hz := IsQuasisimple.pCore_le_center (G := K) p
    have ht : (⊤ : Subgroup K) ≤ center K := by
      calc
        ⊤ = centralizer (center K : Set K) := centralizer_center.symm
        _ ≤ centralizer (pCore p K : Set K) := centralizer_le hz
        _ ≤ center K := hk.trans hz
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp (top_unique ht))).elim
  rw [generalizedFitting, he, sup_bot_eq, Fitting_eq_pcore G p
    (pPrimeCore_eq_bot_of_centralizer_pCore_le p hc)]

variable {G : Type*} [Group G]

/-- Even characteristic passes from Mc to its Sylow overgroup H. -/
public theorem H_core_selfCentralizing (T : Sylow 2 G) (Mc H : Subgroup G)
    (heven : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K →
      centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hMc : IsMaximalTwoLocal Mc) (hTH : (T : Subgroup G) ≤ H) (hHMc : H ≤ Mc) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  have hTMc := hTH.trans hHMc
  have hTS : (T.subtype hTMc : Subgroup Mc) ≤ H.subgroupOf Mc := by
    intro t ht
    exact hTH ht
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hHMc)).mp
    (centralizer_pCore_le_of_sylow_le (T.subtype hTMc) (H.subgroupOf Mc) hTS
      (heven Mc hMc hTMc))

/-- The ambient formulation needed by the normal-core argument in 15.3.48. -/
public theorem H_inf_centralizer_core_le (T : Sylow 2 G) (Mc H : Subgroup G)
    (heven : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K →
      centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hMc : IsMaximalTwoLocal Mc) (hTH : (T : Subgroup G) ≤ H) (hHMc : H ≤ Mc) :
    H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2 := by
  rintro x ⟨hxH, hxC⟩
  refine ⟨⟨x, hxH⟩, H_core_selfCentralizing T Mc H heven hMc hTH hHMc ?_, rfl⟩
  intro q hq
  apply Subtype.ext
  exact hxC q (mem_map_of_mem H.subtype hq)

/-- The generalized Fitting equality in F.9.1(a), derived from even
characteristic rather than imposed on H. -/
public theorem H_generalizedFitting_eq_core [Finite G] (T : Sylow 2 G) (Mc H : Subgroup G)
    (heven : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K →
      centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hMc : IsMaximalTwoLocal Mc) (hTH : (T : Subgroup G) ≤ H) (hHMc : H ≤ Mc) :
    generalizedFitting H = pCore 2 H :=
  generalizedFitting_eq_core 2 (H_core_selfCentralizing T Mc H heven hMc hTH hHMc)

/-- Relative normality of the actual residual transfers characteristic two
from M to Y, giving the generalized Fitting equality in the F.9.1 preamble. -/
public theorem residualY_generalizedFitting_eq_core [Finite G] (T : Sylow 2 G) (M Mc : Subgroup G)
    (heven : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K →
      centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M) :
    generalizedFitting (residualY M Mc) = pCore 2 (residualY M Mc) := by
  let := residualY_normal M Mc
  have hY := normal_core_selfCentralizing (heven M hM hTM) ((residualY M Mc).subgroupOf M)
  have hY' := (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe (Chapter14.SourcePreliminaries.sourceResidual_le M Mc))).mp hY
  exact generalizedFitting_eq_core 2 hY'

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Preamble
