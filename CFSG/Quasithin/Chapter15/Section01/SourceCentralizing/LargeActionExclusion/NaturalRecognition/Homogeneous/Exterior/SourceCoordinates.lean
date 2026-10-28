module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.Exterior.Reduction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.Repeated
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.SeedSylow
public import Theory.Representation.BinaryOffender.FixedSummandCoordinates
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.IrreducibleTransport

/-!
# Full exterior coordinates for the original source module

The ten-dimensional branch admits a fixed direct complement by the proved
exterior cohomology calculation. Extend its actual moved-module coordinates
by that complement, using either the prescribed SL₅ marking or its graph twist.
The original seed remains Sylow-fixed and has nonzero projection.

The literal consumer removes the coordinate premise from the exterior
reduction. Only the concrete model seed-core exclusion remains explicit;
its discharge and final 15.1.28 assembly belong to this recognition family.

Source: Aschbacher--Smith 15.1.27(2)--28, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01
namespace ExteriorReduction
open Representation.SL5TenDimensional
/-- Extend the actual moved coordinates by the invariant summand. The actor
marking is retained up to the explicit inverse-transpose graph automorphism. -/
theorem seedCoordinates_of_moved
    {D U : Type*} [_root_.Group D] [Finite D] [AddCommGroup U]
    [Module (ZMod 2) U] {σ : Representation (ZMod 2) D U}
    {K : Subgroup D} (s : ChapterB.QuasisimpleSource.MovedSection σ K)
    (hK : K = ⊤) (hc : IsCompl s.space.toSubmodule (fixedSpace σ K))
    (hirr : IsIrreducible (s.space.toRepresentation.comp K.subtype))
    (mark : K ≃* Group) (hdim : Module.finrank (ZMod 2) s.space.toSubmodule = 10)
    (P : Submodule (ZMod 2) U) (R : Sylow 2 D)
    (hfixed : P ≤ fixedSpace σ R) (hmoving : ¬ P ≤ σ.invariants) :
    Nonempty (SeedCoordinates σ P) := by
  let := hirr
  obtain ⟨a,e,_ha,he⟩ := Representation.SL5ExteriorSquare.square_coordinates_of_finrank_ten
    (s.space.toRepresentation.comp K.subtype) mark hdim
  let f : D ≃* K := ((MulEquiv.subgroupCongr hK).trans Subgroup.topEquiv).symm
  have hc' : IsCompl s.space.toSubmodule σ.invariants := by
    simpa only [hK, ChapterB.QuasisimpleSource.ExtensionConsequences.fixedSpace_top] using hc
  let q := s.space.fixedSummandCoordinates hc'
  let coordinates := q.trans (e.prodCongr (LinearEquiv.refl (ZMod 2) σ.invariants))
  refine ⟨SeedCoordinates.of_split (f.trans a) coordinates ?_ R hfixed hmoving⟩
  intro g v
  have hq := s.space.fixedSummandCoordinates_intertwines hc' g v
  change (e (q (σ g v)).1, (q (σ g v)).2) = _
  rw [hq]
  apply Prod.ext
  · exact he (f g) (q v).1
  · rfl

end ExteriorReduction
open Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
open ChapterB.QuasisimpleSource.ExtensionConsequences
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Actual split coordinates and projected seed for the selected degree-ten
source branch, covering both exchanged-plane sizes and both exterior powers. -/
theorem HasExchangedLinearSource.original_exterior_seed_coordinates
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (_hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (_hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (_hne : M ≠ Mc) (_hfull : V = localModule T M)
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h
      (s.c27Input hG h) s.cubicFacts t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    let K := ((d.L.subgroupOf J).map q).subgroupOf B
    ∀ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K,
      BinaryActor.ActionCase (ρ.comp B.subtype) K c.sectionData 5 →
      IsIrreducible (c.sectionData.space.toRepresentation.comp K.subtype) →
      Module.finrank (ZMod 2) c.sectionData.space.toSubmodule = 10 →
      ∀ _mark : K ≃* Representation.SL5TenDimensional.Group,
        Nonempty (ExteriorReduction.SeedCoordinates
          (ρ.comp B.subtype) (d.exchangedSeedSpace t J)) := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B K c hc hirr hdim mark
  obtain ⟨R,hfixed,hmoving⟩ := s.seed_sylow_fixed_and_moving hG hM hu h t ht htS
  cases hc with
  | naturalDual hK hnat =>
    exact (d.exchanged_U_not_naturalPlusDual s.1 hG hM hu h
      (s.c27Input hG h) s.cubicFacts t ht htS c 5 (Or.inr rfl) hK hnat).elim
  | repeatedNatural r hp hb hK hnat =>
    obtain ⟨_,⟨e⟩⟩ := s.repeated_natural_multiplicity_one hG hM hu h t ht htS
      c 5 r (Or.inr rfl) hK hp hb hnat
    have hd : Module.finrank (ZMod 2) c.sectionData.space.toSubmodule = 5 := by
      exact e.linearEquiv.finrank_eq.trans
        (show Module.finrank (ZMod 2) (Fin 5 → ZMod 2) = 5 by simp)
    omega
  | irreducible hi hf hir hs he =>
    cases hs with
    | natural hg e hratio =>
      have hsplit := binaryLinear_isCompl c.sectionData hi (by decide : 4 ≤ 5) e
      have hd := (ChapterB.SourceB513.splitQuotientEquiv c.sectionData hsplit).linearEquiv.finrank_eq
      have hd' : Module.finrank (ZMod 2)
          (c.sectionData.space.toSubmodule ⧸ c.sectionData.central.toSubmodule) = 5 := by
        exact e.linearEquiv.finrank_eq.trans
          (show Module.finrank (ZMod 2) (Fin 5 → ZMod 2) = 5 by simp)
      omega
    | orthogonal hd _ _ _ _ _ => omega
    | symmetricEight hd _ _ _ => omega
    | exterior hd hg hK em hdq ho hratio =>
      have hsplit := exteriorFive_isCompl c.sectionData
        ⟨hi,hf,hir,.exteriorFive hg hK em hdq ho hratio,he⟩ em hdq
      exact ExteriorReduction.seedCoordinates_of_moved c.sectionData hK hsplit hirr
        mark hdim _ R hfixed hmoving

/-- The exterior branch now has only the concrete seed-core exclusion left
explicit. The split coordinates and projected Sylow-fixed seed are constructed
from the original source hypotheses. Final discharge of `hmodel` remains with
this natural-recognition family. -/
theorem HasExchangedLinearSource.original_exterior_false_of_model_core
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hfull : V = localModule T M)
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h
      (s.c27Input hG h) s.cubicFacts t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    let K := ((d.L.subgroupOf J).map q).subgroupOf B
    ∀ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K,
      BinaryActor.ActionCase (ρ.comp B.subtype) K c.sectionData 5 →
      IsIrreducible (c.sectionData.space.toRepresentation.comp K.subtype) →
      Module.finrank (ZMod 2) c.sectionData.space.toSubmodule = 10 →
      (K ≃* Representation.SL5TenDimensional.Group) →
      ExteriorReduction.ModelSeedCoreExclusion → False := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B K c hc hirr hdim mark hmodel
  obtain ⟨e⟩ := s.original_exterior_seed_coordinates hG hempty hM hmany hJ hu
    hne hfull h t ht htS c hc hirr hdim mark
  exact s.exterior_false_of_seed_coordinates_and_model_core hG hempty hM hmany hJ hu
    hne hfull h t ht htS c hc hirr hdim e hmodel

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
