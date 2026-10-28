module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.BinaryModels
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.Selection
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SourceCore
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
/-!
# Genuine C.2.7 input for the constrained Nine component

The original Q1 controls supply the pushing-up setup. The rank-two quotient
identifies L with the cubic residual, hence gives its required normality.
Centerlessness makes the actual coreToStar comparison an isomorphism.

Source: Aschbacher--Smith 15.1.27--28, printed pp.1102--1103.
-/
public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.BinaryComponentResidual
open Chapter1.RadicalExclusions Chapter1.RadicalExclusions.ModelReduction
open FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
theorem constrained_input (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    (hq : IsQuasisimple (d.L ⧸ pCore 2 d.L))
    (hQne : d.Q1 ≠ ⊥)
    (hc : d.Q1.characteristicNormalizerClosure ≤ Mc)
    (hn : d.G1 ⊓ normalizer (d.Q1 : Set G) = d.MZ)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L := by
  let := h.elementary
  let := hq
  have hQM : d.Q1 ≤ d.MZ := d.Q1_le_MZ
  have hQG : d.Q1 ≤ d.G1 := hQM.trans inf_le_left
  have hMnorm : d.MZ ≤ normalizer (d.Q1 : Set G) :=
    d.MZ.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.MZ (pCore 2 d.MZ))
  let : (d.Q1.subgroupOf d.MZ).Normal := normal_subgroupOf_of_le_normalizer hMnorm
  have hclosure : (normalClosure (d.Q1.subgroupOf d.MZ : Set d.MZ)).map d.MZ.subtype = d.Q1 := by
    rw [normalClosure_eq_self, map_subgroupOf_eq_of_le hQM]
  have hsy : Chapter1.IsSylowIn 2 d.Q1
      ((normalClosure (d.Q1.subgroupOf d.MZ : Set d.MZ)).map d.MZ.subtype) := by
    rw [hclosure]
    exact Chapter1.isSylowIn_iff.mpr ⟨isPGroup_pCoreIn 2 d.MZ,le_rfl,
      fun U _ hQU hUQ => le_antisymm hUQ hQU⟩
  have hLc := (d.source_cubic_component hG h hf).1
  have hGn : d.G1 ≤ normalizer (d.L : Set G) := by
    have hh := d.G1.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.G1 (primeToResidual 3 d.G1))
    rw [←hLc] at hh
    exact hh
  exact ⟨⟨caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
      ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left)),
    hQG,inf_le_left,caseI_intrinsic_core_radical d.G1 d.MZ inf_le_left hQne hn,
    caseI_intrinsic_characteristic_control d.G1 Mc d.Q1 hQG hc,hsy⟩,
    d.L_component,hq,hfit,d.L_not_le_MZ,hQG.trans hGn⟩

/-- The same Nine marker supplies the genuine C.2.7 input in the constrained row. -/
theorem NineSource.c27Input {d : CaseIComponentData T M Mc V} (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L :=
  d.constrained_input hG h s.quasisimple s.core_nontrivial s.characteristic_control
    s.core_normalizer hf hfit

/-- The source's centerless quotient loses no element in the actual star map. -/
@[expose] noncomputable def constrained_coreStarEquiv (d : CaseIComponentData T M Mc V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L)) :
    (d.L ⧸ pCore 2 d.L) ≃* starImage d.L d.Q1 d.L :=
  MulEquiv.ofBijective (coreToStar hi.normalizes)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (bot_unique
      ((coreToStar_ker_central_from_source hi).trans hf.1.le)),
      coreToStar_surjective hi.normalizes⟩

@[simp] theorem constrained_coreStarEquiv_apply (d : CaseIComponentData T M Mc V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L)) (x : d.L ⧸ pCore 2 d.L) :
    d.constrained_coreStarEquiv hi hf x = coreToStar hi.normalizes x := rfl

/-- The original radical omega-center lies in C.2.7's actual star module. -/
theorem omega_Q1_le_starV (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L)) :
    omegaOneCenterAmbient d.Q1 ≤ (starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype := by
  let := hi.quasisimple
  have hLc := (d.source_cubic_component hG h hf).1
  have hGn : d.G1 ≤ normalizer (d.L : Set G) := by
    have hh := d.G1.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.G1 (primeToResidual 3 d.G1))
    rwa [←hLc] at hh
  let : (d.L.subgroupOf d.G1).Normal := normal_subgroupOf_of_le_normalizer hGn
  have hQR := source_joinCore_le_radical hi
  have hc : centralizer (pCore 2 d.L : Set d.L) ≤ pCore 2 d.L := by
    rw [←hi.fitting]
    exact centralizer_generalizedFitting_le d.L
  have hJc := centralizer_pCore_sup_le 2 d.L d.Q1 hc
    (isPGroup_pCoreIn 2 d.MZ) hi.normalizes
  let J := d.L ⊔ d.Q1
  intro x hx
  obtain ⟨hxR,hx2,hcent⟩ := (mem_omegaOneCenterAmbient_iff d.Q1 x).mp hx
  let xJ : J := ⟨x,mem_sup_right hxR⟩
  have hxC : xJ ∈ centralizer (pCore 2 J : Set J) := by
    intro a ha
    exact Subtype.ext (hcent a (hQR (mem_map_of_mem J.subtype ha)))
  refine ⟨xJ,?_,rfl⟩
  change xJ ∈ omegaOneCenterAmbient (pCore 2 J)
  exact (mem_omegaOneCenterAmbient_iff _ xJ).mpr
    ⟨hJc hxC,Subtype.ext hx2,fun a ha => hxC a ha⟩

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
