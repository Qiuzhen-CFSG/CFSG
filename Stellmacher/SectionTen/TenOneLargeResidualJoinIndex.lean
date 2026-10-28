module
public import Stellmacher.SectionTen.TenOneLargeResidualQuotientElementary
public import Stellmacher.SectionTen.TenOneLargeResidualNormalClosure
public import Stellmacher.SectionTen.TenOneLargeFullSupportSixteen
public import Theory.GroupAction.CyclicQuotientSmallLayer

/-!
# The terminal residual closure and its order-sixteen quotient

In the actual large Section Ten branch, O₂(E_terminal)/V_terminal has order
sixteen. The paired source-(18) result also identifies O₂(E_terminal) with
the E_terminal-conjugate closure of the generated subgroup W. Both results
have only the original context, middle vertex and no-transvection hypothesis.

The elementary quotient producer supplies the literal normality and exact
core-kernel action. Residual perfectness gives full support. The middle
coatom in the residual core has index two and its first-module commutator
lies in W; the proved |W/(W∩V_terminal)|=2 therefore bounds every relevant
actor displacement by four. The full-support representation theorem forces
quotient order sixteen. The separate closure theorem gives the generation
identity without any quotient-cardinality assumption.

Source: Stellmacher (10.1)(18), printed p.64 of
`refs/files/stellmacher-n-group.pdf`. Both residual alternatives C₅ and C₃×C₃
are retained; the later source-(19) exclusion and Frobenius recognition are
not inputs to this result.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_residual_quotient_card
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    QuotientCardEq (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'))
      (VAt ctx.Γ ctx.criticalPath.a') 16 := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let U := twoCoreIn E
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let A := VAt ctx.Γ ctx.criticalPath.firstStep
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let W := conjugateClosure (A ⊓ Q) (GAt ctx.Γ middle)
  let C := U ⊓ QAt ctx.Γ middle
  have hE : E=twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : E≤P := hE ▸ twoResidualIn_le P
  have hUP : U≤P := (twoCoreIn_le E).trans hEP
  have hPU : P≤Subgroup.normalizer (U:Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPV : P≤Subgroup.normalizer (V:Set G) := stabilizer_le_normalizer_v ctx.Γ _
  obtain ⟨hN,helem,hUQcomm⟩ := ten_one_large_residual_quotient_elementary ctx middle hpath hno
  let _ := hN
  let X := U ⧸ V.subgroupOf U
  let _ : IsElementaryAbelian 2 X := helem
  obtain ⟨hPU',D,hVD,hDU,_⟩ := ten_one_large_noncentral_chief_factor ctx middle hpath hno
  have hVU : V≤U := hVD.trans hDU.le
  have hVlt : V<U := hVD.trans_lt hDU
  let _ : Nontrivial X := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    let _ := hs
    apply hVlt.not_ge
    intro x hx
    exact (QuotientGroup.eq_one_iff (N:=V.subgroupOf U) (x:=⟨x,hx⟩)).mp
      (Subsingleton.elim (QuotientGroup.mk' (V.subgroupOf U) ⟨x,hx⟩) 1)
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hperfect : BenderSuzuki.External.hktPResidual 2 E=⊤ := by
    rw [hE]
    exact twoResidualAmbient_has_top_twoResidual P
  have hodd : Odd (Nat.card (E ⧸ pCore 2 E)) := by
    rw [hE]
    exact local_residual_core_quotient_odd ctx.sectionSeven ctx.Γ ctx.criticalPath.a' middle
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) P le_rfl
  have hfullU : ⁅U,E⁆=U := by
    have hh := congrArg (Subgroup.map E.subtype)
      (twoCore_eq_commutator_of_residual_perfect hperfect hodd)
    rw [Subgroup.map_commutator,←MonoidHom.range_eq_map,Subgroup.range_subtype] at hh
    exact hh.symm
  obtain ⟨action,hformula,hQker,hfull⟩ :=
    Subgroup.exists_quotient_conjugation_full_action P U V E Q hPU hPV hN hEP hfullU hUQcomm
  have hQnative : Q.subgroupOf P=pCore 2 P := by
    change (ctx.Γ.twoCoreAt ctx.criticalPath.a').subgroupOf P=pCore 2 P
    rw [ctx.Γ.twoCoreAt_def,twoCoreIn,Subgroup.subgroupOf]
    change ((pCore 2 P).map P.subtype).comap P.subtype=pCore 2 P
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hcoreKernel : pCore 2 P≤action.ker := hQnative ▸ hQker
  have habelian : ⁅U,U⁆≤V := by
    have hcomm : _root_.commutator U≤V.subgroupOf U :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N:=V.subgroupOf U)).mp inferInstance
    rw [←Subgroup.map_subtype_commutator U]
    exact (Subgroup.map_mono hcomm).trans_eq (Subgroup.map_subgroupOf_eq_of_le hVU)
  have hWU : W≤U := (ten_one_large_first_residual_index ctx middle hpath hno).2
  have hWcard : Nat.card W=32 := by
    have hh := (ten_one_large_neighborhood_action ctx middle hpath hno).1
    change Nat.card W=4*Nat.card (A⊓V:Subgroup G) at hh
    rw [(ten_one_large_terminal_structure ctx middle hpath hno).2.2] at hh
    exact hh
  have hWsmall : V.relIndex W≤2 := by
    have hh := ((W⊓V).subgroupOf W).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show W⊓V≤W from inf_le_left)).toEquiv] at hh
    change (W⊓V).relIndex W*Nat.card (W⊓V:Subgroup G)=Nat.card W at hh
    rw [Subgroup.inf_relIndex_left,(ten_one_large_generated_terminal_intersection ctx middle hpath hno).1,hWcard] at hh
    omega
  have hsize : Nat.card U≤2*Nat.card C := by
    have hh := (C.subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show C≤U from inf_le_left)).toEquiv] at hh
    change C.relIndex U*Nat.card C=Nat.card U at hh
    have hi : C.relIndex U=2 := by
      dsimp only [C]
      rw [Subgroup.inf_relIndex_left,ten_one_terminal_residual_middle_index ctx middle hpath]
    rw [hi] at hh
    exact hh.ge
  have hQA : QAt ctx.Γ middle≤Subgroup.normalizer (A:Set G) :=
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2).trans
      (stabilizer_le_normalizer_v ctx.Γ _)
  have hAP : A≤P := (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2
  have hUQ : U≤Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a')≤ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hCAW : ⁅C,A⁆≤W := by
    have hCAU : ⁅C,A⁆≤U := (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hAP.trans hPU))
    intro x hx
    have hxA := Subgroup.le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hQA) hx
    exact Subgroup.subset_closure ⟨1,⟨x,hxA,hUQ (hCAU hx)⟩,by simp⟩
  have hdisp : ∀ actor:P,(actor:G)∈A→(actor:G)∉Q→
      Nat.card (commutatorAction (Subgroup.zpowers (action actor)) X)≤4 := by
    intro actor hactor _hout
    have hrel := Subgroup.quotient_commutator_relIndex_le_four_of_index_two_small_layer
      U C V W inf_le_left hVU hWU hN habelian (actor:G) (hPU actor.property)
      hsize hWsmall ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hactor)).trans hCAW)
    have hDP : Subgroup.zpowers (actor:G)≤P := Subgroup.zpowers_le.mpr actor.property
    have hinternal : (Subgroup.zpowers (actor:G)).subgroupOf P=Subgroup.zpowers actor := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hDP,MonoidHom.map_zpowers]
      rfl
    have hCU : ⁅U,Subgroup.zpowers (actor:G)⁆≤U :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (hDP.trans hPU)
    have heq := Subgroup.relIndex_sup_right
      (⁅U,Subgroup.zpowers (actor:G)⁆.subgroupOf U) (V.subgroupOf U)
    rw [←Subgroup.subgroupOf_sup hCU hVU,
      Subgroup.relIndex_subgroupOf (sup_le hCU hVU),Subgroup.relIndex_subgroupOf hCU] at heq
    have hrank := Subgroup.quotient_conjugation_commutatorAction_card
      P U V (Subgroup.zpowers (actor:G)) hPU hDP hN action hformula
    rw [hinternal,MonoidHom.map_zpowers,←heq] at hrank
    exact hrank.trans_le hrel
  have hXcard : Nat.card X=16 := ten_one_large_full_support_card_sixteen
    ctx middle hpath hno action hcoreKernel hfull hdisp
  have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf U)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv] at hh
  change Nat.card U=Nat.card X*Nat.card V at hh
  rw [hXcard] at hh
  exact hh
public theorem ten_one_large_residual_join_index
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    conjugateClosure
      (conjugateClosure (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
        (GAt ctx.Γ middle)) (EAt ctx.Γ ctx.criticalPath.a') =
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') ∧
    QuotientCardEq (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'))
      (VAt ctx.Γ ctx.criticalPath.a') 16 := by
  exact ⟨ten_one_large_residual_generated_by_neighborhood ctx middle hpath hno,
    ten_one_large_residual_quotient_card ctx middle hpath hno⟩

end Stellmacher.SectionTen
