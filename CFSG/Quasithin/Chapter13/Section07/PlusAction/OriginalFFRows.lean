module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalActorImages
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalCubicImages
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# B.5.6 on the original odd kernel action

The source reduced actor and cubic-image theorems produce the literal
quotient of `K (L₁ T)` by the centralizer of the selected elementary subgroup.
Its image of `K` is normal, the quotient of its join with the radical image
is a two-group, and the cubic image centralizes that join and has no fixed
vectors. The commutator-coordinate theorem identifies full movement by `K`
with full movement in this quotient representation. The three-row B.5.6
extraction then gives two natural binary three-dimensional summands with
one identification of the original component image.

The source SQTK cover, offender containment, component list, and marked A₅
central-quotient family are supplied by their earlier-source owners. No
irreducibility of the whole selected subgroup is assumed. The normality
witness in the conclusion is constructed by `OriginalActorImages`; exposing
it keeps the exact quotient action available without repeating its proof
inside the statement's dependent module instances.

Source: Aschbacher--Smith 13.7.4(1), printed pp.937--938, using B.5.6.
-/

set_option backward.isDefEq.respectTransparency false

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- B.5.6 on the actual source quotient and its actual normal component image. -/
theorem source_reduced_odd_doubleThree
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    {K : Subgroup G}
    (hKC : K ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hKn : H ≤ normalizer (K : Set G)) (hp : IsPPerfect 2 K)
    (hcomm : ⁅K,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤ K.pCoreIn 2)
    (U : Subgroup ↥(K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hred : IsPReduced 2 U) (hne : U ≠ ⊥)
    (hUK : ⁅U,K.subgroupOf
      (K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G)))⁆ = U)
    (hUL : ⁅U,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁.subgroupOf
      (K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G)))⁆ = U)
    (hUR : U ≤ (⁅commutatorPreimage
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁.pCoreIn 2)
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).V₁,K⁆).subgroupOf
      (K ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G)))) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let P := F.L₁ ⊔ (T : Subgroup G)
    let X := K ⊔ P
    letI := hred.normal
    letI := hred.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set X))
    let C := (K.subgroupOf X).map q
    let E := C ⊔ ((P.pCoreIn 2).subgroupOf X).map q
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    ∃ hn : C.Normal, letI := hn;
    SQTKQuotient KnownSimple.IsKnownSimple E →
    C.subgroupOf E ≤ offenderSubgroup (ρ.comp E.subtype) →
    (Nat.card C = 3 ∨ Nonempty (C ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (C ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) →
    (Nat.card C = 60 → Nonempty (ActionEquiv
      ((MovedSection.ofNormal (ρ.comp E.subtype) (C.subgroupOf E)).action.comp
        (C.subgroupOf E).subtype) (alternatingNatural 5))) →
    Nonempty (ActionEquiv (V := Additive U) (ρ.comp C.subtype)
      (repeated (linearNatural BinaryField.two 3) 2)) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
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
    (hKC.trans (kernel_le_H (D := F))) hKn U hred
  refine ⟨hdata.2.1, ?_⟩
  let : C.Normal := hdata.2.1
  intro cover hCN hcases hA5
  obtain ⟨hEn,hCn,hRp,hcore,hfaith,hn,hquot⟩ := hdata
  let := hn
  obtain ⟨_,_,hAE,z,hzA,hz3,hfix⟩ :=
    source_kernel_reduced_cubic_image d h eL hKC hKn hp hcomm U hred hne hUL hUR
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
end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
