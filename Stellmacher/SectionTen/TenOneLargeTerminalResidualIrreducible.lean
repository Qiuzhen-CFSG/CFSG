module
public import Stellmacher.SectionTen.TenOneLargeTerminalStructure
public import Stellmacher.SectionTen.TenOneLargeNineResidualExclusion
public import Stellmacher.SectionTen.TenOneLargeResidualJoinIndex
public import Theory.GroupAction.FiveOnSixteenIrreducible
public import Theory.GroupAction.CoprimeHall

/-!
# Irreducibility under the actual terminal residual

In the large Section Ten branch, every subgroup of V_terminal/Z_terminal
invariant under E_terminal is trivial or the whole quotient. The theorem
retains the caller's normality and elementary quotient instances, action,
conjugation formula, and exact two-core kernel. It requires invariance only
under the actual residual actors, not the full terminal stabilizer.

The actual source-(18) quotient packet excludes the elementary-nine
alternative in source (14). Equal kernels identify the order of the
literal residual quotient image with the odd core of the supplied action
range, giving order five. The quotient V/Z has order sixteen, and full
odd-core support together with coprime splitting makes its fixed subgroup
trivial. Lifting actors through the exact residual image identifies the
caller's invariant subgroup as invariant under this order-five action.
Orbit counting then leaves only the trivial and full subgroups.

Source: Stellmacher (10.1), Journal of Algebra 190 (1997), printed pp.64–65,
the residual commutator-family step after (19). The result supplies the
residual irreducibility needed by the final central-layer transfer without
assuming a residual model or the final core-index bound.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u

public theorem ten_one_large_terminal_residual_irreducible
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    [_hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))]
    (action : GAt ctx.Γ ctx.criticalPath.a' →* MulAut
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.a',
      ∀ point : VAt ctx.Γ ctx.criticalPath.a',
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) point) =
        QuotientGroup.mk'
          ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))
          ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp
              (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
                point).mp point.property⟩)
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a')) :
    ∀ D : Subgroup (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')),
      (∀ mover : GAt ctx.Γ ctx.criticalPath.a',
        (mover : G) ∈ EAt ctx.Γ ctx.criticalPath.a' → ∀ point,
        point ∈ D → action mover point ∈ D) → D = ⊥ ∨ D = ⊤ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let V := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let E := EAt Γ cp.a'
  let U := twoCoreIn E
  let W := V ⧸ Z.subgroupOf V
  let O := SectionOne.oddCore action.range
  let q := QuotientGroup.mk' (pCore 2 P)
  obtain ⟨hmodels,hVcard,_⟩ := ten_one_large_terminal_structure ctx middle hpath hno
  have hnotnine : ¬ Nonempty (((E.subgroupOf P).map q) ≃* (C3 × C3)) := by
    obtain ⟨hNU,hel,hcomm⟩ := ten_one_large_residual_quotient_elementary ctx middle hpath hno
    let _ := hNU
    have hindex : Nat.card U = 16 * Nat.card V :=
      ten_one_large_residual_quotient_card ctx middle hpath hno
    obtain ⟨_,C,hVC,hCU,_⟩ := ten_one_large_noncentral_chief_factor ctx middle hpath hno
    have hVU : V ≤ U := hVC.trans hCU.le
    have hcard : Nat.card (U ⧸ V.subgroupOf U) = 16 := by
      have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf U)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv,hindex,hVcard] at hh
      change 16 * 32 = Nat.card (U ⧸ V.subgroupOf U) * 32 at hh
      omega
    exact ten_one_large_terminal_residual_not_nine ctx middle hpath hno hNU hel hcard hcomm
  obtain ⟨model⟩ := hmodels.resolve_left hnotnine
  have hquotientFive : Nat.card ((E.subgroupOf P).map q) = 5 := by
    rw [Nat.card_congr model.toEquiv]
    simp [C5]
  have hshort : 1 < cp.length := by rw [ctx.critical_length]; decide
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hcenter := nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hshort cp.a' ⟨alignment,halignment⟩
  have hZcard : Nat.card Z = 2 := hcenter.1
  have hQP : QAt Γ cp.a' ≤ P := by
    change Γ.twoCoreAt cp.a' ≤ P
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le P
  have hZV : Z ≤ V := hcenter.2.1.symm.le.trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hQP.trans (stabilizer_le_normalizer_v Γ cp.a')))
  have hWcard : Nat.card W = 16 := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv,hZcard,hVcard] at hh
    change 32 = Nat.card W * 2 at hh
    omega
  obtain ⟨_,_,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hcore : pCore 2 P ≤ action.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict,hkernel]
  have hodd : (E.subgroupOf P).map action.rangeRestrict = O :=
    nine_local_residual_image_eq_oddCore ctx.toLocalContext.toSectionNineLocalContext
      cp.a' middle (Γ.adjacent_symm hterminal) action.rangeRestrict
      action.rangeRestrict_surjective hcore
  have hOcard : Nat.card O = 5 := by
    rw [←hodd,←Subgroup.relIndex_ker,MonoidHom.ker_rangeRestrict,hkernel]
    rw [←Subgroup.relIndex_ker,QuotientGroup.ker_mk'] at hquotientFive
    exact hquotientFive
  have hcop : Nat.Coprime (Nat.card O) (Nat.card W) := by
    rw [hOcard,hWcard]
    decide
  have hfixed : FixedPoints.subgroup O W = ⊥ := by
    have hh := (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := W) (A := O) (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance).disjoint
    have hfull := ten_one_large_terminal_oddCore_full_support
      ctx middle hpath hno action hformula hkernel
    change Disjoint (FixedPoints.subgroup O W) (commutatorAction O W) at hh
    rw [hfull,disjoint_top] at hh
    exact hh
  intro D hD
  have hpres : ∀ mover : O, ∀ point : W, point ∈ D → mover • point ∈ D := by
    intro mover point hp
    have hm : (mover : action.range) ∈ (E.subgroupOf P).map action.rangeRestrict :=
      hodd.symm ▸ mover.property
    obtain ⟨actor,hactor,himage⟩ := hm
    change (mover : action.range) • point ∈ D
    rw [←himage]
    change action actor point ∈ D
    exact hD actor hactor point hp
  let _ : IsInvariant O W D := ⟨by
    intro mover point
    constructor
    · exact hpres mover point
    · intro hp
      have hh := hpres mover⁻¹ (mover • point) hp
      simpa only [inv_smul_smul] using hh⟩
  exact invariant_eq_bot_or_top_of_five_actor hOcard hWcard hfixed D

end Stellmacher.SectionTen
