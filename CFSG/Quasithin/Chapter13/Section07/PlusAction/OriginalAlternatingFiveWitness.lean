module
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerCatalogue
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.Thompson
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalOddRadical
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalKernelSylow
public import CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource.Classification
public import CFSG.Quasithin.Chapter12.Section02.ChosenModule.InsideReducedWitness

/-!
# A marked A5 constituent before point-residual centralization

The original primitive kernel component has a reduced detecting witness in
its join with the ambient Sylow subgroup. Homogeneous selection inside that
witness gives a literal ChosenModule in the original fixed layer, hence in
the point radical. The genuine earlier 13.3.2(3) module theorem marks it as
the alternating natural module. No centralization by the point residual or
Sylow-invariance of the chosen constituent is required here.

Source: Aschbacher–Smith 13.7.4(1), printed p.937, using A.1.19, A.1.42,
and the original 13.3.2(3) source input on p.885.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- An actual marked constituent in the original fixed layer, before imposing
any commutator bound on the component and point residual. -/
theorem source_primitive_alternatingFive_chosen_in_fixedLayer
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hp : IsPPerfect 2 (J.map H.subtype)) (hKne : J.map H.subtype ≠ ⊥)
    (ha : Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)))
    (modules : Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let K := J.map H.subtype
    ∃ I : Subgroup G, Nonempty (ChosenModule T K I) ∧
      I ≤ fixedLayer F ∧ I ≤ (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      Chapter6.Source.IsConjugationModel K I Chapter6.Source.a5Module := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let X := K ⊔ (T : Subgroup G)
  have hn := (source_primitive_kernel_normal_of_small_model d h hne J hJ hs hJC
    (Or.inl ha)).2
  let : Group.IsPerfect J := hJ.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (H.subtype.subgroupMap_surjective J)
  let : IsElementaryAbelian 2 V := NaturalAction.elementary d
  let : IsElementaryAbelian 2 V₃ := IsElementaryAbelian.of_le d.seed_le
  let : IsMulCommutative (conjugateSpanBy V₃ H) := hU
  have hE : IsElementaryAbelian 2 F.UH := conjugateSpanBy_elementary_of_commutative V₃ H
  have hXH : X ≤ H := sup_le (hJC.trans (kernel_le_H (D := F))) h.T_le_H
  obtain ⟨W,hW,hr,hc,hm⟩ := normal_kernel_reduced_witness h hE hJC hn hp hKne
    (show K ≤ X from le_sup_left) (show (T : Subgroup G) ≤ X from le_sup_right) hXH
  have hm' : ⁅W,K.subgroupOf X⁆ ≠ ⊥ := by
    intro he
    have he' := congrArg (map X.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le (show K ≤ X from le_sup_left),
      Subgroup.map_bot] at he'
    exact hm he'
  obtain ⟨I,⟨chosen⟩,hi⟩ := exists_chosen_le_reduced_witness
    (h.T_le_H.trans hn) W hr hm'
  have hi0 : I ≤ fixedLayer F := hi.trans (by
    rintro x ⟨w,hw,rfl⟩
    exact hW hw)
  let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hn
  have hmove := (subnormal_kernel_structure h hJC
    (inferInstance : (K.subgroupOf H).Normal).isSubnormal hp hKne).2.1
  have hf := component_faithful_of_fixedLayer_movement h hE J hJ hmove
  let eJ := J.equivMapOfInjective H.subtype H.subtype_injective
  have haK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨e⟩ := ha
    exact ⟨(QuotientGroup.congr _ _ eJ.symm (pCore_map_iso 2 eJ.symm)).trans e⟩
  exact ⟨I,⟨chosen⟩,hi0,hi0.trans (source_fixedLayer_le_point_radical h),
    modules G T L d.counterexample K hf haK I chosen⟩
end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
