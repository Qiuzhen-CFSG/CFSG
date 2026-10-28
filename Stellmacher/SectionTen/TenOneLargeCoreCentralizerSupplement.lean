module
public import Stellmacher.SectionTen.TenOneLargeResidualJoinIndex
public import Stellmacher.SectionTen.TenOneLargeTerminalCoreFixed
public import Theory.GroupTheory.CentralBinaryPairingSupplement

/-!
# The terminal core is supplemented by its module centralizer

In the actual no-transvection Section Ten context, write Q for the terminal
two-core, U for the terminal residual two-core, and V for its module. Then
Q=C_Q(V)U and C_Q(V)∩U=V. Only the original context and no-transvection
premise are used; neither the final core-index bound, residual type five,
nor the source-(20) centralizer equality is assumed.

The actual module quotient V/Z and residual quotient U/V are elementary
of order sixteen by sources (14) and (18). The terminal core fixes Z and
has [V,Q]≤Z, while the proved residual-core fixed-point theorem gives
C_V(U)=Z. The central binary pairing supplement theorem applies to these
literal subgroups and quotient instances. Its perfect commutator pairing
identifies the residual centralizer kernel and matches every Q action by
an element of U, yielding the claimed product and intersection.

Source: Stellmacher (10.1), Journal of Algebra 190 (1997), printed p.65,
the core supplement immediately after (20). This separates that algebraic
step from the later bound on C_Q(V)/V.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_core_centralizer_supplement
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    let Q := QAt ctx.Γ ctx.criticalPath.a'
    let U := twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
    let V := VAt ctx.Γ ctx.criticalPath.a'
    let C := Q⊓centralizer (V:Set G)
    Q=C⊔U ∧ C⊓U=V := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let Q := QAt Γ cp.a'
  let E := EAt Γ cp.a'
  let U := twoCoreIn E
  let V := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  have hshort : 1<cp.length := by change 1<ctx.criticalPath.length; rw [ctx.critical_length]; decide
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  obtain ⟨hNZ,hWV,action,hformula,hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort cp.a' ⟨alignment,halignment⟩
  let _ := hNZ
  let _ := hWV
  obtain ⟨hNV,hUV,hcommUQ⟩ := ten_one_large_residual_quotient_elementary ctx middle hpath hno
  let _ := hNV
  let _ := hUV
  let _ : IsElementaryAbelian 2 V :=
    (nine_three_second_extraction_inputs ctx.toLocalContext.toSectionNineLocalContext hshort).2.2.1
  have hcenter := nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hshort cp.a' ⟨alignment,halignment⟩
  have hfixed : V⊓centralizer (U:Set G)=Z :=
    ten_one_large_terminal_core_fixed_line ctx middle hpath hno
  have hZV : Z≤V := hfixed.ge.trans inf_le_left
  have hVQ : V≤Q := neighbor_join_le_core_of_length_gt_one Γ cp hshort cp.a'
  have hUQ : U≤Q := by
    change twoCoreIn (Γ.twoResidualAt cp.a')≤Γ.twoCoreAt cp.a'
    rw [Γ.twoResidualAt_def,Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hVU : V≤U := by
    have hfull := ten_one_large_terminal_residual_full ctx middle hpath hno
    change ⁅V,E⁆=V at hfull
    rw [←hfull,commutator_comm]
    apply (commutator_mono le_rfl hVQ).trans
    change ⁅Γ.twoResidualAt cp.a',Γ.twoCoreAt cp.a'⁆≤twoCoreIn (Γ.twoResidualAt cp.a')
    rw [Γ.twoResidualAt_def,Γ.twoCoreAt_def]
    exact residual_commutator_core_le P
  have hQP : Q≤P := by
    change Γ.twoCoreAt cp.a'≤Γ.stabilizer cp.a'
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hcentral : Q≤centralizer (Z:Set G) := hQP.trans
    (nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext
      cp.a' ⟨alignment,halignment⟩)
  have hZcard : Nat.card Z=2 := hcenter.1
  have hVcard : Nat.card V=32 := (ten_one_large_terminal_structure ctx middle hpath hno).2.1
  have hVZcard : Nat.card (V ⧸ Z.subgroupOf V)=16 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (subgroupOfEquivOfLe hZV).toEquiv,hZcard,hVcard] at hh
    omega
  have hUVcard : Nat.card (U ⧸ V.subgroupOf U)=16 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (V.subgroupOf U)
    rw [Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv] at hh
    have hsource := ten_one_large_residual_quotient_card ctx middle hpath hno
    change Nat.card U=16*Nat.card V at hsource
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hh.symm.trans hsource)
  exact eq_centralizer_sup_of_binary_pairing Q U V Z hUQ hVU hZV hZcard
    (hVZcard.trans hUVcard.symm) hcentral hcenter.2.1.le hfixed

end Stellmacher.SectionTen
