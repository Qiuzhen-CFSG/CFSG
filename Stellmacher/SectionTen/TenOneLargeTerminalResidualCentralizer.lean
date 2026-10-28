module
public import Stellmacher.SectionTen.TenOneLargeTerminalFullSupport
public import Theory.GroupAction.CoprimeHall

/-!
# The terminal residual fixes precisely the center line

In the actual Section Ten no-transvection case, the intersection of the
terminal module with the centralizer of the terminal residual is exactly
the terminal center. The quotient action is constructed from the context;
no centralizer conclusion or source-(16) splitting is assumed.

Retain the constructed quotient normality instance, elementary quotient,
conjugation action and exact kernel. Full odd-core support and coprime
splitting make the odd-core fixed subgroup on the quotient trivial. The
actual residual image is that odd core, so any module element centralizing
the residual has trivial quotient image and belongs to the center line.
Conversely the order-two terminal center centralizes its stabilizer.

This is the fixed-intersection input in Stellmacher (10.1)(16), printed
p.64 of `refs/files/stellmacher-n-group.pdf`. It holds before choosing
between the two residual models and does not require irreducibility.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u

public theorem ten_one_large_terminal_residual_centralizer
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
    : VAt ctx.Γ ctx.criticalPath.a' ⊓
        Subgroup.centralizer (EAt ctx.Γ ctx.criticalPath.a' : Set G) =
      ZAt ctx.Γ ctx.criticalPath.a' := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let V := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let E := EAt Γ cp.a'
  have hshort : 1 < cp.length := by rw [ctx.critical_length]; decide
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  obtain ⟨hN,hW,action,hformula,hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort cp.a' ⟨alignment,halignment⟩
  let _ := hN
  let _ := hW
  let W := V ⧸ Z.subgroupOf V
  let O := SectionOne.oddCore action.range
  let q := QuotientGroup.mk' (Z.subgroupOf V)
  have hcop : Nat.Coprime (Nat.card O) (Nat.card W) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := action.range)).symm.pow_right n
  have hfixed : FixedPoints.subgroup O W = ⊥ := by
    have hh := (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := W) (A := O) (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance).disjoint
    have hfull := ten_one_large_terminal_oddCore_full_support ctx middle hpath hno action hformula hkernel
    change Disjoint (FixedPoints.subgroup O W) (commutatorAction O W) at hh
    rw [hfull,disjoint_top] at hh
    exact hh
  have hEP : E ≤ P := by
    change Γ.twoResidualAt cp.a' ≤ P
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le P
  have hQP : QAt Γ cp.a' ≤ P := by
    change Γ.twoCoreAt cp.a' ≤ P
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le P
  have hcore : pCore 2 P ≤ action.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict,hkernel]
  obtain ⟨_,_,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hres : (E.subgroupOf P).map action.rangeRestrict = O :=
    nine_local_residual_image_eq_oddCore ctx.toLocalContext.toSectionNineLocalContext
      cp.a' middle (Γ.adjacent_symm hterminal) action.rangeRestrict
      action.rangeRestrict_surjective hcore
  have hZV : Z ≤ V :=
    (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext hshort
      cp.a' ⟨alignment,halignment⟩).2.1.symm.le.trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp
          (hQP.trans (stabilizer_le_normalizer_v Γ cp.a')))
  apply le_antisymm
  · rintro point ⟨hpoint,hcentral⟩
    let pointV : V := ⟨point,hpoint⟩
    have hqfixed : q pointV ∈ FixedPoints.subgroup O W := by
      intro mover
      have hm : (mover : action.range) ∈ (E.subgroupOf P).map action.rangeRestrict :=
        hres.symm ▸ mover.property
      obtain ⟨actor,hactor,himage⟩ := hm
      change (mover : action.range) • q pointV = q pointV
      rw [←himage]
      change action actor (q pointV) = q pointV
      rw [hformula]
      apply congrArg q
      apply Subtype.ext
      change (actor:G)*point*(actor:G)⁻¹=point
      have hc := Subgroup.mem_centralizer_iff.mp hcentral actor hactor
      exact mul_inv_eq_iff_eq_mul.mpr hc
    have hqone : q pointV = 1 := hfixed.le hqfixed
    exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf V) pointV).mp hqone
  · exact le_inf hZV (Subgroup.le_centralizer_iff.mp
      (hEP.trans (nine_next_center_centralizes_stabilizer
        ctx.toLocalContext.toSectionNineLocalContext cp.a' ⟨alignment,halignment⟩)))

end Stellmacher.SectionTen
