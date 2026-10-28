module
public import Stellmacher.SectionTen.TenOneLargeNineComplement
public import Theory.GroupAction.NineSixteenFixedFactors
public import Stellmacher.SectionTen.TenOneLargeTerminalFullSupport

/-!
# The two fixed factors for the actual terminal nine complement

Retain the original terminal V/Z conjugation action, its normality and
elementary instances, and its exact two-core kernel. For an actual
complement D to O₂(E) in E with model C₃ × C₃, the literal restriction
along D ≤ P has two complementary actor lines of order three, whose
fixed subgroups have order four and complement one another in V/Z.

The kernel kills O₂(E), so complement generation identifies the image of
D with the actual odd residual image. Its already proved full support
makes the full fixed subgroup trivial. Complement disjointness and the
exact kernel make this same restricted action faithful. The actual
terminal module has order32 and its center order2, so the quotient has
order16. The generic elementary-nine fixed-factor theorem now applies.

Source: Stellmacher (10.1), printed p.64, the factor choice after (18).
This module does not replace the original action by a representation
model and does not yet assert the corresponding fixed factors of U/V.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
public theorem ten_one_large_nine_fixed_factors
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
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))    (D : Subgroup G)
    (hDE : D≤EAt ctx.Γ ctx.criticalPath.a')
    (hDP : D≤GAt ctx.Γ ctx.criticalPath.a')
    (hgen : EAt ctx.Γ ctx.criticalPath.a'=twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⊔D)
    (hdisjoint : Disjoint (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')) D)
    (hmodel : Nonempty (D ≃* (C3×C3))) :
    let W := VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')
    let _ : MulDistribMulAction D W := MulDistribMulAction.compHom W
      (action.comp (Subgroup.inclusion hDP))
    ∃ K L : Subgroup D, Nat.card K=3 ∧ Nat.card L=3 ∧ IsCompl K L ∧
      Nat.card (FixedPoints.subgroup K W)=4 ∧ Nat.card (FixedPoints.subgroup L W)=4 ∧
      IsCompl (FixedPoints.subgroup K W) (FixedPoints.subgroup L W) := by
  classical
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let U := twoCoreIn E
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let W := V ⧸ Z.subgroupOf V
  let O := SectionOne.oddCore action.range
  let e := hmodel.some
  let _ : IsElementaryAbelian 3 D := {
    toIsMulCommutative := ⟨⟨fun x y=>e.injective (by rw [map_mul,map_mul];exact mul_comm _ _)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x=>by
      apply e.injective
      rw [map_pow,map_one]
      exact (show ∀z:C3×C3,z^3=1 from by decide) (e x)) }
  have hDcard : Nat.card D=9 := by
    have hthree : Nat.card C3=3 :=
      (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3)).trans (by norm_num)
    rw [Nat.card_congr e.toEquiv,Nat.card_prod,hthree]
  have hE : E=twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : E≤P := hE ▸ twoResidualIn_le P
  have hUP : U≤P := (twoCoreIn_le E).trans hEP
  have hU : U=E⊓twoCoreIn P := by
    change twoCoreIn E=E⊓twoCoreIn P
    rw [hE,residual_core_eq_inter_core]
  have hcore : pCore 2 P≤action.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict,hkernel]
  obtain ⟨_,_,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hres : (E.subgroupOf P).map action.rangeRestrict=O :=
    nine_local_residual_image_eq_oddCore ctx.toLocalContext.toSectionNineLocalContext
      ctx.criticalPath.a' middle (ctx.Γ.adjacent_symm hterminal)
      action.rangeRestrict action.rangeRestrict_surjective hcore
  have hUcore : U.subgroupOf P≤pCore 2 P := by
    intro u hu
    have hq : (u:G)∈twoCoreIn P := (hU ▸ hu).2
    obtain ⟨p,hp,hpu⟩ := hq
    exact (show p=u from Subtype.ext hpu) ▸ hp
  have hDimage : (D.subgroupOf P).map action.rangeRestrict=O := by
    have hUs : (U.subgroupOf P).map action.rangeRestrict=⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      exact hUcore.trans hcore
    have hgen' : E=U⊔D := hgen
    rw [hgen',Subgroup.subgroupOf_sup hUP hDP,Subgroup.map_sup,hUs,bot_sup_eq] at hres
    exact hres
  have hVcard := (ten_one_large_terminal_structure ctx middle hpath hno).2.1
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length];decide
  obtain ⟨alignment,_,halign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hcenter := nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext hshort
    ctx.criticalPath.a' ⟨alignment,halign⟩
  have hQP : QAt ctx.Γ ctx.criticalPath.a'≤P := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a'≤P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le P
  have hZV : Z≤V := hcenter.2.1.symm.le.trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hQP.trans (stabilizer_le_normalizer_v ctx.Γ _)))
  have hWcard : Nat.card W=16 := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv,hcenter.1,hVcard] at hh
    change 32=Nat.card W*2 at hh
    omega
  have hcop : Nat.Coprime (Nat.card O) (Nat.card W) := by
    rw [hWcard]
    exact (pPrimeCore_coprime_card (p:=2) (G:=action.range)).symm.pow_right 4
  have hOfixed : FixedPoints.subgroup O W=⊥ := by
    have hh := (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G:=W) (A:=O) (Group.isSolvable_of_comm fun x y=>mul_comm x y) hcop inferInstance).disjoint
    have hfull := ten_one_large_terminal_oddCore_full_support ctx middle hpath hno
      action hformula hkernel
    change Disjoint (FixedPoints.subgroup O W) (commutatorAction O W) at hh
    rw [hfull,disjoint_top] at hh
    exact hh
  let dAction := action.comp (Subgroup.inclusion hDP)
  let _ : MulDistribMulAction D W := MulDistribMulAction.compHom W dAction
  have hfixed : FixedPoints.subgroup (⊤:Subgroup D) W=⊥ := by
    apply bot_unique
    intro w hw
    apply hOfixed.le
    intro o
    obtain ⟨p,hp,hpo⟩ := (show (o:action.range)∈(D.subgroupOf P).map action.rangeRestrict from
      hDimage.symm ▸ o.property)
    have hh := hw ⟨⟨p,hp⟩,Subgroup.mem_top _⟩
    change dAction ⟨p,hp⟩ w=w at hh
    change (o:action.range) • w=w
    rw [←hpo]
    exact hh
  let _ : FaithfulSMul D W := faithfulSMul_iff.mpr (by
    intro d hd
    have hdker : Subgroup.inclusion hDP d∈action.ker := by
      apply MonoidHom.mem_ker.mpr
      ext w
      exact hd w
    have hdQ : (d:G)∈twoCoreIn P :=
      ⟨Subgroup.inclusion hDP d,hkernel ▸ hdker,rfl⟩
    have hdU : (d:G)∈U := hU.symm ▸ ⟨hDE d.property,hdQ⟩
    exact Subtype.ext (Subgroup.disjoint_def.mp hdisjoint hdU d.property))
  exact nine_sixteen_fixed_factor_decomposition hDcard hWcard hfixed

end Stellmacher.SectionTen
