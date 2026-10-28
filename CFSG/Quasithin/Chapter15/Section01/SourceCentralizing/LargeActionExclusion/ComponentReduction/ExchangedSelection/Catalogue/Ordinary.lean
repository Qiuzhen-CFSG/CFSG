module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.ResidualControl
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.QuotientModels
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.OddCharacteristic
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Selection
public import CFSG.Quasithin.Chapter15.Section01.CaseI.OrdinarySource.InnerPlacement
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115.Transport

/-!
# The ordinary pre-exclusion source reduction

The original ordering and centralizing hypotheses supply J(S)=J(T) and
its normalizer control. Applied to the literal pre-exclusion component,
the residual-intersection argument excludes the Borel configurations in
15.1.21(i),(iii). The general marker application also proves escape of
O²(M ∩ G₁), for either source prime, without choosing an exchanged plane.
The 1.1.5 actions below are transported to L itself with their conjugation
formula intact, for use by the independent model branches.

The odd-characteristic marking reduces to the actual PSL₂(4) and PSL₃(2)
models via `Nonsporadic.OddCharacteristic`. The five-row 15.1.20(3)
exhaustion, remaining rank-one model geometry, and ordinary rows of
15.1.22 remain to be proved. Their precise conclusion
interfaces are in `Ordinary.Alternatives`; no catalogue is asserted here.
Source: Aschbacher--Smith, printed pp.1094--1100.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- Apply the Borel contradiction with both Thompson-control inputs
proved from the original ambient setup. Only model geometry remains. -/
theorem PreExclusionSource.no_thompson_borel
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    {B : Subgroup G} (hB : IsPPerfect 2 B) (hBZ : B ≤ d.MZ)
    (hBJ : B ≤ normalizer (elementaryAbelianMaxJ d.S : Set G))
    (hfix : d.S ⊓ centralizer (B : Set G) ≤ d.S ⊓ centralizer (d.L : Set G)) :
    False := by
  have he := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
  have hn := (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
  exact s.false_of_thompson_borel (h := h) hM.1.2 he hn hB hBZ hBJ hfix

/-- The complete marked 1.1.5 action on L itself, with every central cover
and actual ambient conjugation retained. This is the starting classification,
not the narrower 15.1.20 conclusion. -/
theorem PreExclusionSource.ordinary_marked_model
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {z : G} (hz : z ∈ centralInvolutions T) (hne : z ≠ 1) :
    ∃ α : MulAut d.L, (∀ x : d.L, (α x : G) = z * x * z⁻¹) ∧
      ModelAction115 d.L α := by
  obtain ⟨α,ha,hm⟩ := ((s.ordinary hL).actions z hz hne).2
  let e : d.L ≃* d.L.subgroupOf d.G1 :=
    (subgroupOfEquivOfLe d.L_component.1).symm
  refine ⟨MulAut.congr e.symm α, ?_, hm.of_mulEquiv e⟩
  intro x
  exact ha (e x)

end CaseIComponentData

/-- The original marker supplies a component whose actual two-residual
escapes M_Z. This is an application before any prime or row exclusion. -/
theorem PreparedChosenModule.source_preExclusion_twoResidual_escape
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ¬ (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype ≤ d.MZ := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,s.twoResidual_not_le_MZ (h := h)⟩

end CFSG.Quasithin.Chapter15.Section01
