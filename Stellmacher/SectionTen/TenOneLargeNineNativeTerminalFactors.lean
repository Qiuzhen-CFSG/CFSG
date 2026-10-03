module
public import Stellmacher.SectionTen.TenOneLargeNineFixedFactors
public import Stellmacher.SectionTen.TenOneLargeTerminalCoreFixed
public import Theory.GroupAction.NativeCoprimeQuotientFixedCard
public import Theory.PGroup
public import Theory.GroupAction.NativeSubtypeFixedPoints

/-!
# Native terminal factors from the selected quotient fixed groups

Retain the original terminal V/Z action and its normality witness, and
an actual actor subgroup D ≤ P. Suppose K,L ≤ D have order three and
their fixed subgroups in V/Z are complementary of order four. For their
literal images Ai in the ambient group, the centralizers Wi=C_V(Ai)
generate V, intersect in Z, and neither lies in Z.

The subtype fixed-point transfer compares each chosen line with its
actual ambient image under the same supplied action. Coprime quotient
fixed-point lifting identifies each Wi image with the chosen fixed group.
The central order-two subgroup lies in both Wi. Complementarity then
lifts through the actual quotient map to the join and intersection, while
the nontrivial fixed images exclude Wi ≤ Z. The module order32 supplies
the coprimeness and solvability used in the lift.

This is the native terminal-factor step in Stellmacher (10.1), printed
p.64, after (18). It supplies the actual noncentral fixed subgroups for
the separate proof of nonzero fixed factors on U/V; that later quotient
is not assumed or characterized here.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped IsMulCommutative
universe u

private theorem lift_complementary_quotient_images
    {G:Type*} [Group G] (V Z W1 W2:Subgroup G)
    (_hZV:Z≤V) (hW1:W1≤V) (hW2:W2≤V) (hZ1:Z≤W1) (hZ2:Z≤W2)
    [hN:(Z.subgroupOf V).Normal]
    (hcompl:IsCompl ((W1.subgroupOf V).map (QuotientGroup.mk' (Z.subgroupOf V)))
      ((W2.subgroupOf V).map (QuotientGroup.mk' (Z.subgroupOf V)))) :
    V=W1⊔W2 ∧ W1⊓W2=Z := by
  let q:=QuotientGroup.mk' (Z.subgroupOf V)
  have hZjoin:q.ker≤W1.subgroupOf V⊔W2.subgroupOf V:=by
    rw [QuotientGroup.ker_mk']
    exact (show Z.subgroupOf V≤W1.subgroupOf V from fun _ hx=>hZ1 hx).trans le_sup_left
  have hjoin:W1.subgroupOf V⊔W2.subgroupOf V=⊤:=by
    apply map_injective_of_ker_le (f:=q) hZjoin le_top
    rw [Subgroup.map_sup,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
    exact hcompl.sup_eq_top
  have hgen:V=W1⊔W2:=by
    have hh:=congrArg (Subgroup.map V.subtype) hjoin
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hW1,map_subgroupOf_eq_of_le hW2,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.symm
  refine ⟨hgen,le_antisymm ?_ (le_inf hZ1 hZ2)⟩
  intro w hw
  have hh:q (⟨w,hW1 hw.1⟩:V)∈
      (W1.subgroupOf V).map q⊓(W2.subgroupOf V).map q:=
    ⟨mem_map_of_mem q hw.1,mem_map_of_mem q hw.2⟩
  have hq:q (⟨w,hW1 hw.1⟩:V)=1:=hcompl.inf_eq_bot.le hh
  exact (QuotientGroup.eq_one_iff (N:=Z.subgroupOf V) (⟨w,hW1 hw.1⟩:V)).mp hq

public theorem ten_one_large_nine_native_terminal_factors
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
    (D:Subgroup G) (hDP:D≤GAt ctx.Γ ctx.criticalPath.a')
    (K L:Subgroup D) (hK:Nat.card K=3) (hL:Nat.card L=3) :
    let V:=VAt ctx.Γ ctx.criticalPath.a'
    let Z:=ZAt ctx.Γ ctx.criticalPath.a'
    let W:=V⧸Z.subgroupOf V
    let _ : MulDistribMulAction D W:=MulDistribMulAction.compHom W
      (action.comp (inclusion hDP))
    Nat.card (FixedPoints.subgroup K W)=4 → Nat.card (FixedPoints.subgroup L W)=4 →
    IsCompl (FixedPoints.subgroup K W) (FixedPoints.subgroup L W) →
    let W1:=V⊓centralizer (K.map D.subtype:Set G)
    let W2:=V⊓centralizer (L.map D.subtype:Set G)
    V=W1⊔W2 ∧ W1⊓W2=Z ∧ ¬W1≤Z ∧ ¬W2≤Z := by
  dsimp only
  let P:=GAt ctx.Γ ctx.criticalPath.a'
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Z:=ZAt ctx.Γ ctx.criticalPath.a'
  let W:=V⧸Z.subgroupOf V
  let q:=QuotientGroup.mk' (Z.subgroupOf V)
  let _ : MulDistribMulAction D W:=MulDistribMulAction.compHom W (action.comp (inclusion hDP))
  intro hKcard hLcard hcompl
  let W1:=V⊓centralizer (K.map D.subtype:Set G)
  let W2:=V⊓centralizer (L.map D.subtype:Set G)
  have hshort:1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  obtain ⟨alignment,_,halign⟩:=lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hZP:Z≤centralizer (P:Set G):=Subgroup.le_centralizer_iff.mp
    (nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext
      ctx.criticalPath.a' ⟨alignment,halign⟩)
  have hZV:Z≤V:=(ten_one_large_terminal_core_fixed_line ctx middle hpath hno).symm.le.trans inf_le_left
  have hVcard:Nat.card V=32:=(ten_one_large_terminal_structure ctx middle hpath hno).2.1
  have hVtwo:IsPGroup 2 V:=IsPGroup.of_card (n:=5) hVcard
  let _ : Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
  let _ : Group.IsNilpotent V:=hVtwo.isNilpotent
  have hPV:P≤normalizer (V:Set G):=stabilizer_le_normalizer_v ctx.Γ _
  have hPZ:P≤normalizer (Z:Set G):=stabilizer_le_normalizer_z ctx.Γ _
  have hmap (M:Subgroup D) (hM:Nat.card M=3) :
      FixedPoints.subgroup M W=((V⊓centralizer (M.map D.subtype:Set G)).subgroupOf V).map q := by
    let AM:=M.map D.subtype
    have hMP:AM≤P:=(map_subtype_le M).trans hDP
    have hAMcard:Nat.card AM=3:=
      (Nat.card_congr (M.equivMapOfInjective D.subtype D.subtype_injective).toEquiv).symm.trans hM
    have hcop:Nat.Coprime (Nat.card AM) (Nat.card V):=by rw [hAMcard,hVcard];decide
    have himage:=(native_coprime_quotient_fixed_card P V Z AM hZV hPV hPZ hMP
      inferInstance hcop hN action hformula).1
    have hcompare:=fixedPoints_subgroup_of_subtype_image P D hDP action M hMP
    exact hcompare.symm.trans himage
  have hmap1:=hmap K hK
  have hmap2:=hmap L hL
  have hZ1:Z≤W1:=le_inf hZV (hZP.trans (centralizer_le ((map_subtype_le K).trans hDP)))
  have hZ2:Z≤W2:=le_inf hZV (hZP.trans (centralizer_le ((map_subtype_le L).trans hDP)))
  have hcompl':IsCompl ((W1.subgroupOf V).map q) ((W2.subgroupOf V).map q):=by
    rw [←hmap1,←hmap2]
    exact hcompl
  have hgen:=lift_complementary_quotient_images V Z W1 W2 hZV inf_le_left inf_le_left hZ1 hZ2 hcompl'
  refine ⟨hgen.1,hgen.2,?_,?_⟩
  · intro hle
    have hh:FixedPoints.subgroup K W=⊥:=by
      rw [hmap1]
      apply bot_unique
      have hm:=map_mono (f:=q) (show W1.subgroupOf V≤Z.subgroupOf V from fun _ hx=>hle hx)
      rw [QuotientGroup.map_mk'_self] at hm
      exact hm
    rw [hh,card_bot] at hKcard
    omega
  · intro hle
    have hh:FixedPoints.subgroup L W=⊥:=by
      rw [hmap2]
      apply bot_unique
      have hm:=map_mono (f:=q) (show W2.subgroupOf V≤Z.subgroupOf V from fun _ hx=>hle hx)
      rw [QuotientGroup.map_mk'_self] at hm
      exact hm
    rw [hh,card_bot] at hLcard
    omega
end Stellmacher.SectionTen
