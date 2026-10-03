module
public import Stellmacher.SectionTen.TenOneLargeNineCoreFixedFactors
public import Stellmacher.SectionTen.TenOneLargeGeneratedResidualEscape
public import Theory.GroupTheory.Commutator.TwoCoprimeFixedFactors

/-!
# The elementary-nine terminal residual is impossible

In the actual large Section Ten branch, retain the chosen source-(18)
normality and elementary structure of U/V, its order16, and [U,Q] ≤ V.
The literal image of E in P/O₂(P) cannot have model C₃ × C₃. No Frobenius
model or desired residual classification is an input.

Lift the assumed image model to an actual odd complement D in E. Its
original action on V/Z supplies two complementary actor lines with
order-four fixed groups. Native fixed-point lifting gives noncentral
terminal factors Wi with product V and intersection Z. On the same
lines, the actual U/V action has nonzero fixed factors of order four;
their native lifts Qi generate U and have elementary order-four Qi/Wi.
The two-factor commutator theorem then puts U' in Z: opposite full actions
bound the cross commutator, and the central-four quotient theorem bounds
each diagonal commutator. The genuine generated-residual escape theorem
excludes U' ≤ Zmiddle, while the actual center decomposition gives Z ≤ Zmiddle.

Source: Stellmacher (10.1), printed p.64, the contradiction between (18)
and (19). All action and normality witnesses remain attached to their
literal quotients. The fixed-factor transfer uses the valid non-full join
obstruction, avoiding the false earlier printed centralizer equality.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_terminal_residual_not_nine
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hN:((VAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'))).Normal) :
    let _:=hN
    let P:=GAt ctx.Γ ctx.criticalPath.a'
    let E:=EAt ctx.Γ ctx.criticalPath.a'
    let U:=twoCoreIn E
    let V:=VAt ctx.Γ ctx.criticalPath.a'
    let X:=U⧸V.subgroupOf U
    IsElementaryAbelian 2 X → Nat.card X=16 → ⁅U,QAt ctx.Γ ctx.criticalPath.a'⁆≤V →
    ¬Nonempty (((E.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)))≃*(C3×C3)) := by
  classical
  let _:=hN
  dsimp only
  intro hel hcard hUQcomm hmodel
  let P:=GAt ctx.Γ ctx.criticalPath.a'
  let E:=EAt ctx.Γ ctx.criticalPath.a'
  let U:=twoCoreIn E
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Z:=ZAt ctx.Γ ctx.criticalPath.a'
  let Q:=QAt ctx.Γ ctx.criticalPath.a'
  have hshort:1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  obtain ⟨alignment,_,halign⟩:=lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  obtain ⟨hNV,hW,action,hformula,hkernel⟩:=nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort ctx.criticalPath.a' ⟨alignment,halign⟩
  let _:=hNV
  let _:=hW
  obtain ⟨D,hDE,hgen,hdisjoint,hmodelD⟩:=ten_one_large_nine_complement ctx hmodel
  have hE:E=twoResidualIn P:=ctx.Γ.twoResidualAt_def _
  have hEP:E≤P:=hE ▸ twoResidualIn_le P
  have hDP:D≤P:=hDE.trans hEP
  obtain ⟨K,L,hK,hL,hKL,hKcard,hLcard,hcompl⟩:=
    ten_one_large_nine_fixed_factors ctx middle hpath hno action hformula hkernel
      D hDE hDP hgen hdisjoint hmodelD
  obtain ⟨hVgen,hinter,hKnot,hLnot⟩:=ten_one_large_nine_native_terminal_factors
    ctx middle hpath hno action hformula D hDP K L hK hL hKcard hLcard hcompl
  obtain ⟨hVU,hUgen,hfixed,hN1,hN2,hel1,hc1,hel2,hc2⟩:=
    ten_one_large_nine_core_fixed_factors ctx middle hpath hno D hDE hDP hgen hmodelD
      K L hK hL hKL hVgen hinter hKnot hLnot hN hel hcard hUQcomm
  let _:=hN1
  let _:=hN2
  let A1:=K.map D.subtype
  let A2:=L.map D.subtype
  let Q1:=U⊓centralizer (A1:Set G)
  let Q2:=U⊓centralizer (A2:Set G)
  let W1:=V⊓centralizer (A1:Set G)
  let W2:=V⊓centralizer (A2:Set G)
  have hA1D:A1≤D:=map_subtype_le K
  have hA2D:A2≤D:=map_subtype_le L
  have hA1P:A1≤P:=hA1D.trans hDP
  have hA2P:A2≤P:=hA2D.trans hDP
  have hKp:IsPGroup 3 K:=IsPGroup.of_card (n:=1) (by simpa using hK)
  have hLp:IsPGroup 3 L:=IsPGroup.of_card (n:=1) (by simpa using hL)
  have hA1:IsPGroup 3 A1:=hKp.map D.subtype
  have hA2:IsPGroup 3 A2:=hLp.map D.subtype
  let e:=hmodelD.some
  let _ : IsMulCommutative D:=⟨⟨fun a b=>e.injective (by rw [map_mul,map_mul];exact mul_comm _ _)⟩⟩
  have hAA:A1≤centralizer (A2:Set G):=by
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (mul_comm (⟨b,hA2D hb⟩:D) ⟨a,hA1D ha⟩)
  have hjoinA:A1⊔A2=D:=by
    have hh:=congrArg (Subgroup.map D.subtype) hKL.sup_eq_top
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hUP:U≤P:=(twoCoreIn_le E).trans hEP
  have hPU:P≤normalizer (U:Set G):=
    (normal_subgroupOf_iff_le_normalizer hUP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPV:P≤normalizer (V:Set G):=stabilizer_le_normalizer_v ctx.Γ _
  have hZP:Z≤centralizer (P:Set G):=le_centralizer_iff.mp
    (nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext
      ctx.criticalPath.a' ⟨alignment,halign⟩)
  have hZV:Z≤V:=hinter.symm.le.trans (inf_le_left.trans inf_le_left)
  have hUQ:U≤Q:=by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a')≤ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hUU:⁅U,U⁆≤V:=(commutator_mono le_rfl hUQ).trans hUQcomm
  have hVUcomm:⁅V,U⁆≤Z:=(commutator_mono le_rfl hUQ).trans_eq
    (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext hshort
      ctx.criticalPath.a' ⟨alignment,halign⟩).2.1
  have hfixed':U⊓centralizer ((A1⊔A2:Subgroup G):Set G)≤Z:=by
    rw [hjoinA]
    exact hfixed
  have hUtwo:IsPGroup 2 U:=(pCore_isPGroup (p:=2) (G:=E)).map _
  have hderived:⁅U,U⁆≤Z:=commutator_le_of_two_coprime_fixed_factors
    U V Z A1 A2 Q1 Q2 W1 W2 hUtwo hA1 hA2 hZV hVU
    (hZP.trans (centralizer_le hUP)) (hZP.trans (centralizer_le hA1P))
    (hZP.trans (centralizer_le hA2P)) (hA1P.trans hPU) (hA2P.trans hPU)
    (hA1P.trans hPV) (hA2P.trans hPV) hAA rfl rfl rfl rfl
    hUgen hVgen hinter hfixed' hUU hVUcomm hN1 hN2 hel1 hc1 hel2 hc2
  apply ten_one_large_terminal_residual_derived_not_le_middle_center ctx middle hpath hno
  apply hderived.trans
  rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
  exact le_sup_right
end Stellmacher.SectionTen
