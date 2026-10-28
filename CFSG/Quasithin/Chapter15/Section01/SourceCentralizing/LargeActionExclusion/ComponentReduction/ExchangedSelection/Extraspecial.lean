module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.Exclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.CubicLift.Obstruction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.SourceSelection.Original
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.ResidualExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Selection

/-!
# The extraspecial marker's component consumer

The finite-image marking constructs a complete row-seven marker and its
four/sixteen decomposition. The marking itself is now constructed from the original extraspecial
action. Its Thompson image selects a noncentral cubic whose fixed plane it fixes:
its generation, exact residual, Sylow intersection and relative normality
follow from the original action and Sylow maps. The original component theorem consumes that
same marker and the earlier 15.1.14 residual hypothesis. No component or
odd-core hypothesis is imposed.

The conditional central cubic lift uses the exact O²(⟨R^{X₀}⟩) and
preserves the marking and selected component. The new obstruction theorem
shows that this exact residual is trivial under earlier 15.1.14: X₀
normalizes V_E and hence lies in M ∩ Mc, where it normalizes R. Thus the
center-movement premise cannot be discharged along that intermediate route
without excluding the extraspecial row. The separate prime-to-three residual of X₀ supplies a replacement: it
moves the marked four-group and excludes all ordinary quotient models and
all constrained alternatives except the natural L₃(2) block. The original
source consumer retains these exclusions on the same component. The
remaining block and catalogue exhaustion still belong to final assembly.

Source: Aschbacher--Smith 15.1.16--20 and 15.1.24, pp.1092--1094,1101.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Apply the actual component theorem to the literal extraspecial marker.
The finite-image selection remains explicit; its existence is not asserted. -/
theorem PreparedChosenModule.extraspecial_component_of_imageMarking
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (c : letI := h.elementary; ExtraspecialMarker.ImageMarking T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    letI := h.elementary
    ∃ (m : CaseIPreExclusionMarker T M V h.normalized) (d : CaseIComponentData T M Mc V),
      m.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized c.X ∧
      m.row = .seven ∧ m.prime = 3 ∧ Nat.card m.Z1 = 4 ∧
      m.fixedPlane = m.Z1 ∧ Nat.card m.movingPlane = 16 ∧
      m.Z1 ⊔ m.movingPlane = V ∧ m.Z1 ⊓ m.movingPlane = ⊥ ∧
      d.Z1 = m.Z1 ∧ d.row = m.row ∧ d.PreExclusionSource h.normalized 3 := by
  let := h.elementary
  obtain ⟨m,hZ,hr,hp,hcard,hfixed,hmoving,hsup,hinf⟩ :=
    c.to_marker T hM.1.2 h.normalized hex
  obtain ⟨d,hdZ,hdr,hd⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨m,d,hZ,hr,hp,hcard,hfixed,hmoving,hsup,hinf,hdZ,hdr,hp ▸ hd⟩

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Apply the lift to the same selected row-seven component. ExchangedSelection
still owns existence of the image marking, center movement, and the later
catalogue exclusions; this theorem does not assume those exclusions. -/
theorem PreparedChosenModule.extraspecial_component_and_cubic_lift_of_center_moved
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (c : letI := h.elementary; ExtraspecialMarker.ImageMarking T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hmove : letI := h.elementary
      ¬ (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict ≤
        centralizer (((center (pResidual 2 (internalActionImage M V h.normalized))).map
          (pResidual 2 (internalActionImage M V h.normalized)).subtype) : Set
            (internalActionImage M V h.normalized))) :
    letI := h.elementary
    ∃ (m : CaseIPreExclusionMarker T M V h.normalized) (d : CaseIComponentData T M Mc V)
      (X₂ : Subgroup G),
      m.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized c.X ∧
      m.row = .seven ∧ m.prime = 3 ∧ Nat.card m.Z1 = 4 ∧
      m.fixedPlane = m.Z1 ∧ Nat.card m.movingPlane = 16 ∧
      m.Z1 ⊔ m.movingPlane = V ∧ m.Z1 ⊓ m.movingPlane = ⊥ ∧
      d.Z1 = m.Z1 ∧ d.row = m.row ∧ d.PreExclusionSource h.normalized 3 ∧
      Nat.card X₂ = 3 ∧ X₂ ≤ ExtraspecialMarker.sourceCentralLiftResidual M Mc V h.normalized ∧
      X₂ ≤ ExtraspecialMarker.centralLiftResidual M Mc V h.normalized ∧ ⁅d.Z1,X₂⁆ = d.Z1 := by
  let := h.elementary
  obtain ⟨m,d,hZ,hr,hp,hcard,hfixed,hmoving,hsup,hinf,hdZ,hdr,hd⟩ :=
    h.extraspecial_component_of_imageMarking hG T hempty hM hmany hJ hu hne hfull hex c hres
  obtain ⟨X₂,hX,hXY,hXb,hm⟩ := c.source_cubic_lift_of_center_moved T hM.1.2 hu h hex hmove
  refine ⟨m,d,X₂,hZ,hr,hp,hcard,hfixed,hmoving,hsup,hinf,hdZ,hdr,hd,hX,hXY,hXb,?_⟩
  rw [hdZ,hZ]
  exact hm

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The stabilizer construction supplies the image marking from the original
Thompson-fixed cubic. The same selected component retains the prime-three
pre-exclusion source, and the original four/sixteen planes. -/
theorem PreparedChosenModule.extraspecial_component_of_fixed_cubic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (X : Subgroup (pResidual 2 (internalActionImage M V h.normalized)))
    (hX : Nat.card X = 3)
    (hXZ : X ≠ center (pResidual 2 (internalActionImage M V h.normalized)))
    (hfixed : letI := h.elementary
      fixedSpace (imageRepresentation M V h.normalized)
        (X.map (pResidual 2 (internalActionImage M V h.normalized)).subtype) ≤
      fixedSpace (imageRepresentation M V h.normalized)
        (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    letI := h.elementary
    ∃ (m : CaseIPreExclusionMarker T M V h.normalized) (d : CaseIComponentData T M Mc V),
      m.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized X ∧
      m.row = .seven ∧ m.prime = 3 ∧ Nat.card m.Z1 = 4 ∧
      m.fixedPlane = m.Z1 ∧ Nat.card m.movingPlane = 16 ∧
      m.Z1 ⊔ m.movingPlane = V ∧ m.Z1 ⊓ m.movingPlane = ⊥ ∧
      d.Z1 = m.Z1 ∧ d.row = m.row ∧ d.PreExclusionSource h.normalized 3 := by
  let := h.elementary
  obtain ⟨c,hc⟩ := h.extraspecial_imageMarking_of_fixed_cubic hG T hempty hM hmany hJ
    hex X hX hXZ hfixed
  obtain ⟨m,d,hZ,hr,hp,hcard,hfix,hmoving,hsup,hinf,hdZ,hdr,hd⟩ :=
    h.extraspecial_component_of_imageMarking hG T hempty hM hmany hJ hu hne hfull hex c hres
  exact ⟨m,d,hc ▸ hZ,hr,hp,hcard,hfix,hmoving,hsup,hinf,hdZ,hdr,hd⟩

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original extraspecial action constructs its marker and selects the
same component, retaining the literal four/sixteen planes and prime three.
Only the permitted earlier 15.1.14 global residual remains explicit. -/
theorem PreparedChosenModule.source_extraspecial_preExclusion_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    letI := h.elementary
    ∃ (c : ExtraspecialMarker.ImageMarking T M V h.normalized) (m : CaseIPreExclusionMarker T M V h.normalized) (d : CaseIComponentData T M Mc V),
      m.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized c.X ∧
      m.row = .seven ∧ m.prime = 3 ∧ Nat.card m.Z1 = 4 ∧
      m.fixedPlane = m.Z1 ∧ Nat.card m.movingPlane = 16 ∧
      m.Z1 ⊔ m.movingPlane = V ∧ m.Z1 ⊓ m.movingPlane = ⊥ ∧
      d.Z1 = m.Z1 ∧ d.row = m.row ∧ d.PreExclusionSource h.normalized 3 := by
  let := h.elementary
  obtain ⟨c⟩ := h.extraspecial_imageMarking hG T hempty hM hmany hJ hfull hex
  obtain ⟨m,d,hZ,hr,hp,hcard,hfixed,hmoving,hsup,hinf,hdZ,hdr,hd⟩ :=
    h.extraspecial_component_of_imageMarking hG T hempty hM hmany hJ hu hne hfull hex c hres
  exact ⟨c,m,d,hZ,hr,hp,hcard,hfixed,hmoving,hsup,hinf,hdZ,hdr,hd⟩

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original extraspecial action constructs its marker and selects the
same component, retaining the literal four/sixteen planes and prime three.
The central-preimage prime-to-three residual excludes the concrete rank-two
models on this same component; the catalogue and remaining source rows are
still retained by the exchanged-selection assembly. -/
theorem PreparedChosenModule.source_extraspecial_preExclusion_component_exclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    letI := h.elementary
    ∃ (c : ExtraspecialMarker.ImageMarking T M V h.normalized) (m : CaseIPreExclusionMarker T M V h.normalized) (d : CaseIComponentData T M Mc V),
      m.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized c.X ∧
      m.row = .seven ∧ m.prime = 3 ∧ Nat.card m.Z1 = 4 ∧
      m.fixedPlane = m.Z1 ∧ Nat.card m.movingPlane = 16 ∧
      m.Z1 ⊔ m.movingPlane = V ∧ m.Z1 ⊓ m.movingPlane = ⊥ ∧
      d.Z1 = m.Z1 ∧ d.row = m.row ∧ d.PreExclusionSource h.normalized 3 ∧
      ¬ Theory.SpecificGroups.BinaryComponentResidual.Facts (d.L ⧸ pCore 2 d.L) ∧
      ¬ CaseIComponentData.SmallOrdinaryModel (d.L ⧸ pCore 2 d.L) ∧
      ¬ CaseIComponentData.SmallBinaryOrdinaryModel (d.L ⧸ pCore 2 d.L) ∧
      (d.ConstrainedAlternatives → d.ConstrainedL3Alternative) ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ¬ CaseIComponentData.OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) ∧
        ¬ d.Ordinary22Alternatives) := by
  let := h.elementary
  obtain ⟨c,m,d,hZ,hr,hp,hcard,hfixed,hmoving,hsup,hinf,hdZ,hdr,hd⟩ :=
    h.source_extraspecial_preExclusion_component hG T hempty hM hmany hJ hu hne hfull hex hres
  have hmark := hdZ.trans hZ
  have hnf := hd.no_extraspecial_component_facts hG h hex c hmark
  have he := hd.extraspecial_model_exclusions hG h hex c hmark
  exact ⟨c,m,d,hZ,hr,hp,hcard,hfixed,hmoving,hsup,hinf,hdZ,hdr,hd,hnf,he.1,he.2.1,
    hd.extraspecial_constrained_l3 hG h hM hJ hex c hmark,
    fun hL => ⟨hd.no_extraspecial_ordinary_postRankOne hG h hex c hmark hL,
      hd.no_extraspecial_ordinary22 hG h hex c hmark hL⟩⟩

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original extraspecial action selects the same marker and component,
retains its prime and four/sixteen planes, and excludes both ordinary
components and every constrained alternative. Only the independent
constrained catalogue must still supply exhaustiveness for row exclusion. -/
theorem PreparedChosenModule.source_extraspecial_catalogue_obstruction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    letI := h.elementary
    ∃ (c : ExtraspecialMarker.ImageMarking T M V h.normalized) (m : CaseIPreExclusionMarker T M V h.normalized) (d : CaseIComponentData T M Mc V),
      m.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized c.X ∧
      m.row = .seven ∧ m.prime = 3 ∧ Nat.card m.Z1 = 4 ∧
      m.fixedPlane = m.Z1 ∧ Nat.card m.movingPlane = 16 ∧
      m.Z1 ⊔ m.movingPlane = V ∧ m.Z1 ⊓ m.movingPlane = ⊥ ∧
      d.Z1 = m.Z1 ∧ d.row = m.row ∧ d.PreExclusionSource h.normalized 3 ∧
      ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) ∧
      ¬ d.ConstrainedAlternatives := by
  let := h.elementary
  obtain ⟨c,m,d,hZ,hr,hp,hcard,hfixed,hmoving,hsup,hinf,hdZ,hdr,hd⟩ :=
    h.source_extraspecial_preExclusion_component hG T hempty hM hmany hJ hu hne hfull hex hres
  have hmark := hdZ.trans hZ
  have hresid : d.nineResidual = m.residual := by
    unfold CaseIComponentData.nineResidual CaseIComponentData.G1 CaseIPreExclusionMarker.residual
    rw [hdZ]
  have hfix : d.nineFixedPlane = m.fixedPlane := by
    change V ⊓ centralizer (d.nineResidual : Set G) = _
    rw [hresid]
    rfl
  have hmove : d.nineMovingPlane = m.movingPlane := by
    change ⁅V,d.nineResidual⁆ = _
    rw [hresid]
    rfl
  have hplanes : d.nineFixedPlane ⊔ d.nineMovingPlane = V := by
    rw [hfix,hmove,hfixed]
    exact hsup
  refine ⟨c,m,d,hZ,hr,hp,hcard,hfixed,hmoving,hsup,hinf,hdZ,hdr,hd,?_,?_⟩
  · exact hd.extraspecial_not_ordinary_of_local_source hG h hempty hM hJ hu hne hmany
      hres hex c hmark
  · intro ha
    exact hd.no_extraspecial_l3 hG h hM.1.2 hex c hmark hplanes
      (hd.extraspecial_constrained_l3 hG h hM hJ hex c hmark ha)

end CFSG.Quasithin.Chapter15.Section01
