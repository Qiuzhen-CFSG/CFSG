module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalFFRows
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalActorQuotients
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalOffenderMovement
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalComponentMinimal

/-!
# The original component kernel action

The selected minimal reduced subgroup in the source tilde-one layer is moved
by both the primitive kernel component and the point residual. Its exact
centralizer quotient has a known-simple SQTK cover and the B.2.10 offender
containment. Transporting the original A₅ or linear-three component shape to
that same quotient discharges those premises in B.5.6 and leaves only the
canonical marked A₅ central-quotient family from the earlier source.

The final theorem constructs the minimal subgroup from the actual ordinary
setup. The genuine Baumann normalizer bound and the earlier marked component
family are retained; cardinality alone does not distinguish the two binary
four-dimensional A₅ actions.

Source: Aschbacher--Smith, 13.7.4(1), printed pp.937--938.
-/

set_option backward.isDefEq.respectTransparency false

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open ChapterB.QuasisimpleSource ChapterB.SourceInduction ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem source_component_reduced_doubleThree
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hp : IsPPerfect 2 (J.map H.subtype))
    (hcomm : ⁅J.map H.subtype,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤
      (J.map H.subtype).pCoreIn 2)
    (hout : ¬ J.map H.subtype ≤ M)
    (hB : normalizer (baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (hmodels : Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 2)
    (U : Subgroup ↥(J.map H.subtype ⊔
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hred : IsPReduced 2 U) (hne : U ≠ ⊥)
    (hUK : ⁅U,(J.map H.subtype).subgroupOf (J.map H.subtype ⊔
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G)))⁆ = U)
    (hUL : ⁅U,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁.subgroupOf
      (J.map H.subtype ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)))⁆ = U)
    (hU0 : U ≤ (fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H)).subgroupOf
      (J.map H.subtype ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G))))
    (hUR : U ≤ (⁅commutatorPreimage
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁.pCoreIn 2)
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).V₁,J.map H.subtype⁆).subgroupOf
      (J.map H.subtype ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)))) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let P := F.L₁ ⊔ (T : Subgroup G)
    let K := J.map H.subtype
    let X := K ⊔ P
    letI := hred.normal
    letI := hred.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set X))
    let C := (K.subgroupOf X).map q
    let E := C ⊔ ((P.pCoreIn 2).subgroupOf X).map q
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    ∃ hn : C.Normal, letI := hn;
    (Nat.card C = 60 → Nonempty (ActionEquiv
      ((MovedSection.ofNormal (ρ.comp E.subtype) (C.subgroupOf E)).action.comp
        (C.subgroupOf E).subtype) (alternatingNatural 5))) →
    Nonempty (ActionEquiv (V := Additive U) (ρ.comp C.subtype)
      (repeated (linearNatural BinaryField.two 3) 2)) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let P := F.L₁ ⊔ (T : Subgroup G)
  let X := K ⊔ P
  let := hred.normal
  let := hred.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set X))
  let C := (K.subgroupOf X).map q
  let E := C ⊔ ((P.pCoreIn 2).subgroupOf X).map q
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hdata := source_kernel_reduced_actor_image h
    (hJC.trans (kernel_le_H (D := F))) hJn U hred
  refine ⟨hdata.2.1, ?_⟩
  let : C.Normal := hdata.2.1
  intro hA5
  obtain ⟨cover⟩ := source_kernel_reduced_actor_cover d h
    (hJC.trans (kernel_le_H (D := F))) U hred
  have hCN := source_component_kernel_le_restricted_offender h J hJ hs hJC hJn
    hcomm hout hB U hred hU0 hne hUK
  have hcases := source_primitive_reduced_actor_models h J hJC hJn U hred hne hUK hs
    (Or.inr hmodels)
  obtain ⟨hEn,hCn,hRp,hcore,hfaith,hn,hquot⟩ := hdata
  let := hn
  obtain ⟨_,_,hAE,z,hzA,hz3,hfix⟩ :=
    source_kernel_reduced_cubic_image d h eL hJC hJn hp hcomm U hred hne hUL hUR
  have hwhole : moved ρ C = ⊤ := by
    change subspaceCommutator ρ ⊤ C = ⊤
    rw [← NormalElementaryQuotient.commutatorSpace_eq U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (K.subgroupOf X)]
    change AddSubgroup.toZModSubmodule 2 ((⁅U,K.subgroupOf X⁆).subgroupOf U).toAddSubgroup = ⊤
    rw [hUK,subgroupOf_self]
    rfl
  exact OddFFRows.ambient_three_row_doubleThree_of_commuting_cubic ρ le_sup_left
    hfaith hcore cover hCN hquot hcases hwhole hA5 z
    (by rw [←hz3]; exact pow_orderOf_eq_one z)
    (fun x => (mem_centralizer_iff.mp (hAE hzA)) x x.property |>.symm) hfix

theorem source_primitive_component_minimal_doubleThree
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hp : IsPPerfect 2 (J.map H.subtype)) (hout : ¬ J.map H.subtype ≤ M)
    (hcomm : ⁅J.map H.subtype,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤
      (J.map H.subtype).pCoreIn 2)
    (hB : normalizer (baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (hmodels : Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 2) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let K := J.map H.subtype
    let P := F.L₁ ⊔ (T : Subgroup G)
    let X := K ⊔ P
    let W := commutatorPreimage F.UH (F.L₁.pCoreIn 2) F.V₁
    let R := ⁅W,K⁆
    let D := ⁅R,F.L₁⁆
    let U₂ := ⁅⁅fixedLayer F,F.L₁⁆,K⁆
    ∃ U : Subgroup X, U ≤ D.subgroupOf X ∧ U ≤ U₂.subgroupOf X ∧
      ∃ hred : IsPReduced 2 U, U ≠ ⊥ ∧ ⁅U,K.subgroupOf X⁆ = U ∧
      ⁅U,F.L₁.subgroupOf X⁆ = U ∧
      (∀ B : Subgroup X, B ≤ U → B.Normal → ⁅B,K.subgroupOf X⁆ ≠ ⊥ → B = U) ∧
      letI := hred.normal
      letI := hred.elementary
      let q := QuotientGroup.mk' (centralizer (U : Set X))
      let C := (K.subgroupOf X).map q
      let E := C ⊔ ((P.pCoreIn 2).subgroupOf X).map q
      let ρ := NormalElementaryQuotient.representation U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      ∃ hn : C.Normal, letI := hn;
      (Nat.card C = 60 → Nonempty (ActionEquiv
        ((MovedSection.ofNormal (ρ.comp E.subtype) (C.subgroupOf E)).action.comp
          (C.subgroupOf E).subtype) (alternatingNatural 5))) →
      Nonempty (ActionEquiv (V := Additive U) (ρ.comp C.subtype)
        (repeated (linearNatural BinaryField.two 3) 2)) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let X := K ⊔ (F.L₁ ⊔ (T : Subgroup G))
  obtain ⟨U,hUD,hUU₂,hr,hne,hUK,hUL,hmin⟩ :=
    source_primitive_component_minimal_tilde_module d h1221 h hU eL hm J hJC hJn hp hout
      hJ hs hcomm
  have hU0 : U ≤ (fixedLayer F).subgroupOf X :=
    hUU₂.trans (comap_mono (source_kernel_mixed_geometry d h hJC hJn hp hcomm).2.2.1)
  have hDR := (source_kernel_tilde_geometry d h hJC hJn hp hcomm).2.2.2.2.2.2.1
  exact ⟨U,hUD,hUU₂,hr,hne,hUK,hUL,hmin,
    source_component_reduced_doubleThree d h eL J hJ hs hJC hJn hp hcomm hout hB hmodels
      U hr hne hUK hUL hU0 (hUD.trans (subgroupOf_mono X hDR))⟩

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
