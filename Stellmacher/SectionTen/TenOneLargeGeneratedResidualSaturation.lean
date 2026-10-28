module
public import Stellmacher.SectionTen.TenOneLargeFirstResidualIndex

/-!
# The generated subgroup forces the terminal residual core

In the actual large Section Ten branch, every subgroup normalized by the
terminal stabilizer and containing the generated subgroup W contains the
terminal residual two-core U. No source-(17) bound or quotient cardinality
is assumed, and the containing subgroup need not be contained in U.

If U is not contained, the intrinsic chief-quotient construction above the
intersection supplies a noncentral irreducible elementary quotient U/D.
The middle coatom of U has its first-module commutator in the defining seed
of W, hence in D. Thus the selected actor fixes a coatom in this same chief
quotient. Actual actor survival rules out trivial displacement, and the
proved no-transvection transfer rules out order two. The coatom bound gives
the contradiction. All quotient actions retain their own supplied normality
and conjugation formula.

This is the source-(3) saturation used in Stellmacher (10.1)(18), printed
p.64 of `refs/files/stellmacher-n-group.pdf`. It is the structural input for
the elementary residual quotient and its later order-sixteen calculation.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_generated_residual_saturation
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (K : Subgroup G)
    (hPK : GAt ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer (K : Set G))
    (hWK : conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle) ≤ K) :
    twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') ≤ K := by
  classical
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let U := twoCoreIn E
  let A := VAt ctx.Γ ctx.criticalPath.firstStep
  let W := conjugateClosure (A ⊓ QAt ctx.Γ ctx.criticalPath.a') (GAt ctx.Γ middle)
  let C := U ⊓ QAt ctx.Γ middle
  have hE : E = twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hUP : U ≤ P := (twoCoreIn_le E).trans hEP
  have hPU : P ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPinter : P ≤ Subgroup.normalizer (U ⊓ K : Set G) :=
    (le_inf hPU hPK).trans Subgroup.inf_normalizer_le_normalizer_inf
  by_contra hnot
  have hproper : U ⊓ K < U := lt_of_le_of_ne inf_le_left (by
    intro heq
    exact hnot (heq.symm.le.trans inf_le_right))
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hperfect : BenderSuzuki.External.hktPResidual 2 E = ⊤ := by
    rw [hE]
    exact twoResidualAmbient_has_top_twoResidual P
  have hodd : Odd (Nat.card (E ⧸ pCore 2 E)) := by
    rw [hE]
    exact local_residual_core_quotient_odd ctx.sectionSeven ctx.Γ ctx.criticalPath.a' middle
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) P le_rfl
  have hfullU : ⁅U,E⁆ = U := by
    have hh := congrArg (Subgroup.map E.subtype)
      (twoCore_eq_commutator_of_residual_perfect hperfect hodd)
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hh
    exact hh.symm
  have hU : IsPGroup 2 U := (pCore_isPGroup (p:=2) (G:=E)).map E.subtype
  obtain ⟨D,hinterD,hDU,hPD,hDnormal,chief,hformulaChief,hWc,hne,hirr,_hfull,hres⟩ :=
    Subgroup.exists_noncentral_irreducible_quotient_above P U (U ⊓ K) E
      hUP hPU hPinter hproper hU hEP hfullU
  let _ := hDnormal
  let _ := hWc
  let _ := hne
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  obtain ⟨hN,hW,action,hformula,hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort ctx.criticalPath.a' ⟨alignment,halignment⟩
  let _ := hN
  let _ := hW
  obtain ⟨element,hactor,hout,hcases⟩ := ten_one_quotient_commutator_actor ctx middle hpath
  obtain ⟨hcard,hselected⟩ := hcases.resolve_left (hno element hactor hout)
  let actor : P := ⟨element,
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2 hactor⟩
  have hnotwo := ten_one_large_chief_displacement_ne_two ctx middle hpath actor hactor
    action hformula hkernel hout hcard hselected hno chief hirr hres
  have hnontrivial : chief actor ≠ 1 :=
    ten_one_first_actor_image_ne_one ctx middle hpath actor hactor hout chief hres
  have hnotone : Nat.card (commutatorAction (Subgroup.zpowers (chief actor))
      (U ⧸ D.subgroupOf U)) ≠ 1 := by
    intro hone
    have htriv := actsTrivially_of_commutatorAction_eq_bot (Subgroup.card_eq_one.mp hone)
    apply hnontrivial
    ext point
    exact htriv ⟨chief actor,Subgroup.mem_zpowers _⟩ point
  have hAP : A ≤ P := (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2
  have hQA : QAt ctx.Γ middle ≤ Subgroup.normalizer (A:Set G) :=
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2).trans
      (stabilizer_le_normalizer_v ctx.Γ _)
  have hUQ : U ≤ QAt ctx.Γ ctx.criticalPath.a' := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a') ≤ ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hCAU : ⁅C,A⁆ ≤ U :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hAP.trans hPU))
  have hCAW : ⁅C,A⁆ ≤ W := by
    intro x hx
    have hxA := Subgroup.le_normalizer_iff_commutator_le_right.mp
      (inf_le_right.trans hQA) hx
    exact Subgroup.subset_closure ⟨1,⟨x,hxA,hUQ (hCAU hx)⟩,by simp⟩
  have hCAD : ⁅C,A⁆ ≤ D := (le_inf hCAU (hCAW.trans hWK)).trans hinterD
  have hKindex : C.relIndex U ∣ 2 := by
    dsimp only [C]
    rw [Subgroup.inf_relIndex_left,ten_one_terminal_residual_middle_index ctx middle hpath]
  have hKcomm : ⁅C,Subgroup.zpowers (actor:G)⁆ ≤ D :=
    (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hactor)).trans hCAD
  have hrel := Subgroup.quotient_commutator_card_le_two_of_fixed_coatom
    P U D C hDU.le hPU hDnormal hWc chief hformulaChief
      actor inf_le_left hKindex hKcomm
  have hDP : Subgroup.zpowers (actor:G) ≤ P := Subgroup.zpowers_le.mpr actor.property
  have hinternal : (Subgroup.zpowers (actor:G)).subgroupOf P = Subgroup.zpowers actor := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hDP,MonoidHom.map_zpowers]
    rfl
  have hCU : ⁅U,Subgroup.zpowers (actor:G)⁆ ≤ U :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hDP.trans hPU)
  have heq := Subgroup.relIndex_sup_right
    (⁅U,Subgroup.zpowers (actor:G)⁆.subgroupOf U) (D.subgroupOf U)
  rw [←Subgroup.subgroupOf_sup hCU hDU.le,
    Subgroup.relIndex_subgroupOf (sup_le hCU hDU.le),Subgroup.relIndex_subgroupOf hCU] at heq
  have hrank := Subgroup.quotient_conjugation_commutatorAction_card
    P U D (Subgroup.zpowers (actor:G)) hPU hDP hDnormal chief hformulaChief
  rw [hinternal,MonoidHom.map_zpowers,←heq] at hrank
  have hbound := hrank.trans_le hrel
  let displacement := commutatorAction (Subgroup.zpowers (chief actor)) (U ⧸ D.subgroupOf U)
  have hbound' : Nat.card displacement ≤ 2 := hbound
  have hnotone' : Nat.card displacement ≠ 1 := hnotone
  have hnotwo' : Nat.card displacement ≠ 2 := hnotwo
  have hpos' : 0 < Nat.card displacement := Nat.card_pos
  omega
end Stellmacher.SectionTen
