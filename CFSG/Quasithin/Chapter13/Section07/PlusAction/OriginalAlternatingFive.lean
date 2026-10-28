module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalComponentExclusion
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalComponents

/-!
# The remaining marked A₅ kernel branch

The actual primitive A₅ component is normal in H by cubic divisibility and
escapes M by the original ordinary local-escape theorem. The source minimal
reduced subgroup therefore exists on the literal corrected tilde-one layer.
Its actor image is the same A₅ quotient. A deleted-permutation mark on its
canonical moved central quotient would invoke B.5 and the proved Baumann/theta
contradiction. The source marking owner can thus apply its genuine earlier
module theorem directly to this selected subgroup.

The Baumann bound and centralization of the point residual modulo the
component core remain explicit earlier-source inputs. No dimension or order
criterion replaces the actual alternating module mark.

Source: Aschbacher--Smith, 13.3.2(3) and 13.7.4(1), printed pp.885,937--938.
-/

set_option backward.isDefEq.respectTransparency false
public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open Stellmacher ChapterB.QuasisimpleSource ChapterB.SourceInduction ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The remaining original A₅ branch supplies a literal minimal reduced
module on which the canonical alternating central-quotient mark is impossible.
The genuine source marking theorem therefore closes this branch. -/
theorem source_primitive_alternatingFive_mark_obstruction
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hp : IsPPerfect 2 (J.map H.subtype))
    (hnot : ¬ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ≤ J.map H.subtype)
    (hcomm : ⁅J.map H.subtype,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤
      (J.map H.subtype).pCoreIn 2)
    (hB : normalizer (baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (ha : Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))) :
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
      Nat.card C = 60 ∧ ¬ Nonempty (ActionEquiv
        ((MovedSection.ofNormal (ρ.comp E.subtype) (C.subgroupOf E)).action.comp
          (C.subgroupOf E).subtype) (alternatingNatural 5)) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let P := F.L₁ ⊔ (T : Subgroup G)
  let X := K ⊔ P
  have hJn := (source_primitive_kernel_normal_of_small_model d h hne J hJ hs hJC
    (Or.inl ha)).2
  have hd : 3 ∣ Nat.card (J ⧸ pCore 2 J) := by
    obtain ⟨e⟩ := ha
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hout := source_primitive_kernel_not_le_local_of_three_dvd d h1221 h eL hne
    J hJ hs hJC hd
  obtain ⟨U,hUD,hUU₂,hr,hUne,hUK,hUL,hmin,hn,hff⟩ :=
    source_primitive_component_minimal_doubleThree d h1221 h hU eL hm J hJ hs
      hJC hJn hp hout hcomm hB (Or.inl ha)
  let := hr.normal
  let := hr.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set X))
  let C := (K.subgroupOf X).map q
  let E := C ⊔ ((P.pCoreIn 2).subgroupOf X).map q
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let := hn
  have hc : Nat.card C = 60 := by
    obtain ⟨e⟩ := source_primitive_reduced_actor_equiv h J hJC hJn U hr hUne hUK hs
    obtain ⟨a⟩ := ha
    rw [←Nat.card_congr e.toEquiv,Nat.card_congr a.toEquiv,nat_card_alternatingGroup]
    norm_num
  refine ⟨U,hUD,hUU₂,hr,hUne,hUK,hUL,hmin,hn,hc,?_⟩
  intro hmark
  have hU0 : U ≤ (fixedLayer F).subgroupOf X :=
    hUU₂.trans (comap_mono (source_kernel_mixed_geometry d h hJC hJn hp hcomm).2.2.1)
  exact source_component_reduced_false d h1221 h eL J hJ hs hJC hJn hnot hcomm
    U hr hU0 hout hB hUne hUK (hff (fun _ => hmark))

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
