module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.SourceCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.NaturalDual
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Splitting
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ParabolicTransport
public import Theory.Representation.BinaryParabolicNatural.RepeatedOffender


/-!
# A single natural module in the repeated branch of 15.1.28

The original seed-centralizer normality puts the Q1 image in the two-core
of a Sylow fixed-space centralizer. Cohomological splitting preserves this
centralizer on the actual B.5 moved section. Under one actor marking for all
copies, a binary Sylow fixes a single natural line, so this core is the line
radical. Each natural copy costs the rank of the original offender in fixed
codimension. Its offender inequality therefore forces multiplicity one.

We use the seed-based core-containment theorem from `NaturalDual`, which is
independent of that module's natural-plus-dual exclusion. No projected line,
parabolic identification, radical equality, or extra multiplicity bound is
assumed. Both original exchanged-plane sizes and dimensions four and five
are retained in the literal source application.

Source: Aschbacher--Smith 15.1.27(4)--28, printed pp.1102--1103.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01.RepeatedNatural
open ChapterB.QuasisimpleSource
open ChapterB.QuasisimpleSource.ExtensionConsequences
open BinaryLinear.OuterCyclic
open Representation.BinaryParabolicNatural
variable {H X : Type*} [Group H] [Finite H]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
  {π : Representation (ZMod 2) H X} {K : Subgroup H}

/-- All copies use the original SL identification, followed by its literal linear action. -/
noncomputable def repeatedLinearCoordinates {n r : ℕ}
    (s : MovedSection π K) (hK : K = ⊤)
    (e : ActionEquiv (s.space.toRepresentation.comp K.subtype)
      (repeated (linearNatural BinaryField.two n) r)) :
    ActionEquiv s.space.toRepresentation
      (copies (Fin r) (natural (Fin n → ZMod 2))) := by
  let f : H ≃* K := ((MulEquiv.subgroupCongr hK).trans Subgroup.topEquiv).symm
  refine ⟨(f.trans e.groupEquiv).trans (slEquivLinear n), e.linearEquiv, ?_⟩
  intro g v
  have hg : (f g : H) = g := rfl
  have hh := e.intertwines (f g) v
  change e.linearEquiv (s.space.toRepresentation (f g : H) v) = _ at hh
  rw [hg] at hh
  refine hh.trans ?_
  funext i
  exact specialLinearNatural_apply n _ _

/-- The source fixed supplement transfers its original core offender to the
common-center radical, so the repeated-natural multiplicity is one. -/
theorem multiplicity_one (s : MovedSection π K) {n r : ℕ}
    (hn : 4 ≤ n) (hr : 0 < r) (hK : K = ⊤)
    (hnat : IsRepeatedLinearNatural (s.space.toRepresentation.comp K.subtype)
      BinaryField.two n r)
    (R : Sylow 2 H) (A : Subgroup H) (hA : IsOffender π A)
    (hcore : A ≤ (subspaceKernel π (fixedSpace π R) ⊤).pCoreIn 2) :
    r = 1 ∧ Nonempty (ActionEquiv (s.space.toRepresentation.comp K.subtype)
      (linearNatural BinaryField.two n)) := by
  have hsum := (repeated_binary_isCompl s hn hK hnat).sup_eq_top
  obtain ⟨e⟩ := hnat
  let a := repeatedLinearCoordinates s hK e
  have hsmall : IsOffender s.space.toRepresentation A :=
    ⟨hA.1,(fixedCodim_subrepresentation_le π s.space A).trans hA.2⟩
  have hmodel := hsmall.map_equivariant _ _ a.groupEquiv.toMonoidHom
    a.groupEquiv.injective a.linearEquiv a.intertwines
  rw [fixedCentralizer_eq_of_fixed_supplement π s.space hsum R ⊤] at hcore
  have hmap := Subgroup.map_mono (f := a.groupEquiv.toMonoidHom) hcore
  rw [map_pCoreIn_of_injective 2 _ _ a.groupEquiv.injective,
    a.fixedCentralizer_map, Subgroup.map_top_of_surjective _ a.groupEquiv.surjective] at hmap
  have hr1 : r = 1 := copies_eq_one_of_sylow_core_offender
    (V := Fin n → ZMod 2) (by simpa using (show 0 < n by omega))
    (R.mapSurjective (f := a.groupEquiv.toMonoidHom) a.groupEquiv.surjective)
    r hr _ hmodel hmap
  refine ⟨hr1,?_⟩
  subst r
  refine ⟨⟨e.groupEquiv,
    e.linearEquiv.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin n → ZMod 2)),?_⟩⟩
  intro g v
  exact congrFun (e.intertwines g v) (0 : Fin 1)
end CFSG.Quasithin.Chapter15.Section01.RepeatedNatural

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The repeated-natural branch of original 15.1.28 on its literal quotient
and arbitrary B.5 moved section. No natural-plus-dual exclusion is used. -/
theorem HasExchangedLinearSource.repeated_natural_multiplicity_one
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    let K := ((d.L.subgroupOf J).map q).subgroupOf B
    ∀ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K,
      ∀ n r : ℕ, (n = 4 ∨ n = 5) → K = ⊤ → 0 < r → r ≤ n-1 →
        IsRepeatedLinearNatural (c.sectionData.space.toRepresentation.comp K.subtype)
          BinaryField.two n r →
        r = 1 ∧ Nonempty (ActionEquiv (c.sectionData.space.toRepresentation.comp K.subtype)
          (linearNatural BinaryField.two n)) := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B K c n r hn hK hrpos _hrbound hnat
  obtain ⟨R,hR⟩ := d.exchanged_Q1_image_le_fixedCentralizer_core s.1 hG hM hu h
    (s.c27Input hG h) s.cubicFacts t ht htS hK
  obtain ⟨A,hAQ,_hA,hAB,_hcore⟩ := s.original_seed_core_offender hG hM hu h t ht htS
  exact RepeatedNatural.multiplicity_one c.sectionData (by omega) hrpos hK hnat
    R ((A.map q).subgroupOf B) (hAB.isOffender (ρ.comp B.subtype))
    ((comap_mono (map_mono hAQ.1)).trans hR)

/-- Literal source application retaining all original centralizing hypotheses,
for both exchanged-plane sizes and either binary natural dimension. -/
theorem HasExchangedLinearSource.original_repeated_natural
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
    let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    let K := ((d.L.subgroupOf J).map q).subgroupOf B
    ∀ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K,
      ∀ n r : ℕ, (n = 4 ∨ n = 5) → K = ⊤ → 0 < r → r ≤ n-1 →
        IsRepeatedLinearNatural (c.sectionData.space.toRepresentation.comp K.subtype)
          BinaryField.two n r →
        r = 1 ∧ Nonempty (ActionEquiv (c.sectionData.space.toRepresentation.comp K.subtype)
          (linearNatural BinaryField.two n)) :=
  s.repeated_natural_multiplicity_one hG hM hu h t ht htS

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
