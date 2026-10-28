module
public import Stellmacher.SectionTen.TenOneLargeNineCoreAction
public import Stellmacher.SectionTen.TenOneLargeNineNativeTerminalFactors
public import Stellmacher.SectionTen.TenOneLargeTerminalFactorNotFull
public import Theory.GroupAction.NineSixteenPrescribedFixedFactors

/-!
# The same actor lines give the native residual-core fixed factors

Keep the actual order-nine complement D and its prescribed complementary
lines K,L. The native terminal fixed groups Wi have already been shown
to generate V, intersect in Z and be noncentral. With the chosen elementary
source-(18) quotient U/V of order16 and [U,Q] ≤ V, the corresponding
Qi=C_U(Ai) generate U, the full D-centralizer in U lies in Z, and each
literal Qi/Wi is elementary of order four. Both quotient normality
witnesses are returned with these conclusions.

Construct the actual U/V conjugation action with trivial whole-D fixed
subgroup. Each selected line has nonzero fixed quotient: otherwise
coprime fixed-point decomposition would contradict the proved non-full
join obstruction supplied by Wi. The prescribed-factor theorem gives
order four and complementarity on the same action. Native coprime
fixed-point lifting supplies an exact isomorphism Qi/Wi to its fixed
quotient, preserving normality and transporting elementarity and order.
The generating quotient lifts to U because V=W1W2 already lies in Q1Q2.
Finally the full fixed quotient puts C_U(D) in V, where the intersection
of the Wi puts it in Z.

Source: Stellmacher (10.1), printed p.64, the factor argument between
(18) and (19). No faithful or irreducible action on U/V is assumed.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem elementary_two_of_equiv_subgroup
    {A X:Type*} [Group A] [Group X] [IsElementaryAbelian 2 X]
    (F:Subgroup X) (e:A≃*F) : IsElementaryAbelian 2 A := by
  refine { toIsMulCommutative := ⟨⟨fun a b => e.injective (by
    rw [map_mul, map_mul]
    exact mul_comm _ _)⟩⟩, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro a
  apply e.injective
  rw [map_pow,map_one]
  apply Subtype.ext
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 X) (e a:X)

public theorem ten_one_large_nine_core_fixed_factors
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (D:Subgroup G) (hDE:D≤EAt ctx.Γ ctx.criticalPath.a')
    (hDP:D≤GAt ctx.Γ ctx.criticalPath.a')
    (hgen:EAt ctx.Γ ctx.criticalPath.a'=twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⊔D)
    (hmodel:Nonempty (D≃*(C3×C3)))
    (K L:Subgroup D) (hK:Nat.card K=3) (hL:Nat.card L=3) (hKL:IsCompl K L)
    (hVgen:VAt ctx.Γ ctx.criticalPath.a'=
      (VAt ctx.Γ ctx.criticalPath.a'⊓centralizer (K.map D.subtype:Set G))⊔
      (VAt ctx.Γ ctx.criticalPath.a'⊓centralizer (L.map D.subtype:Set G)))
    (hinter:(VAt ctx.Γ ctx.criticalPath.a'⊓centralizer (K.map D.subtype:Set G))⊓
      (VAt ctx.Γ ctx.criticalPath.a'⊓centralizer (L.map D.subtype:Set G))=ZAt ctx.Γ ctx.criticalPath.a')
    (hKnot:¬VAt ctx.Γ ctx.criticalPath.a'⊓centralizer (K.map D.subtype:Set G)≤ZAt ctx.Γ ctx.criticalPath.a')
    (hLnot:¬VAt ctx.Γ ctx.criticalPath.a'⊓centralizer (L.map D.subtype:Set G)≤ZAt ctx.Γ ctx.criticalPath.a')
    (hN:((VAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a'))).Normal) :
    let _:=hN
    let U:=twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
    let V:=VAt ctx.Γ ctx.criticalPath.a'
    let Z:=ZAt ctx.Γ ctx.criticalPath.a'
    let X:=U⧸V.subgroupOf U
    IsElementaryAbelian 2 X → Nat.card X=16 → ⁅U,QAt ctx.Γ ctx.criticalPath.a'⁆≤V →
    let Q1:=U⊓centralizer (K.map D.subtype:Set G)
    let Q2:=U⊓centralizer (L.map D.subtype:Set G)
    let W1:=V⊓centralizer (K.map D.subtype:Set G)
    let W2:=V⊓centralizer (L.map D.subtype:Set G)
    V≤U ∧ U=Q1⊔Q2 ∧ U⊓centralizer (D:Set G)≤Z ∧
      ∃ hN1:(W1.subgroupOf Q1).Normal, ∃ hN2:(W2.subgroupOf Q2).Normal,
        let _:=hN1
        let _:=hN2
        IsElementaryAbelian 2 (Q1⧸W1.subgroupOf Q1) ∧ Nat.card (Q1⧸W1.subgroupOf Q1)=4 ∧
        IsElementaryAbelian 2 (Q2⧸W2.subgroupOf Q2) ∧ Nat.card (Q2⧸W2.subgroupOf Q2)=4 := by
  classical
  let _:=hN
  dsimp only
  intro hel hcard hUQ
  let P:=GAt ctx.Γ ctx.criticalPath.a'
  let E:=EAt ctx.Γ ctx.criticalPath.a'
  let U:=twoCoreIn E
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Z:=ZAt ctx.Γ ctx.criticalPath.a'
  let X:=U⧸V.subgroupOf U
  let _ : IsElementaryAbelian 2 X:=hel
  let q:=QuotientGroup.mk' (V.subgroupOf U)
  let Q1:=U⊓centralizer (K.map D.subtype:Set G)
  let Q2:=U⊓centralizer (L.map D.subtype:Set G)
  let W1:=V⊓centralizer (K.map D.subtype:Set G)
  let W2:=V⊓centralizer (L.map D.subtype:Set G)
  let e:=hmodel.some
  let _ : IsElementaryAbelian 3 D:={
    toIsMulCommutative:=⟨⟨fun a b=>e.injective (by rw [map_mul,map_mul];exact mul_comm _ _)⟩⟩
    exponent_dvd_p:=Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a=>by
      apply e.injective
      rw [map_pow,map_one]
      exact (show ∀x:C3×C3,x^3=1 from by decide) (e a)) }
  obtain ⟨hVU,hPU,action,hformula,hfixed⟩:=ten_one_large_nine_core_action ctx middle hpath hno
    D hDE hDP hgen (IsElementaryAbelian.isPGroup 3 D) hN hel hUQ
  let _ : MulDistribMulAction D X:=MulDistribMulAction.compHom X (action.comp (inclusion hDP))
  have hPV:P≤normalizer (V:Set G):=stabilizer_le_normalizer_v ctx.Γ _
  have hUtwo:IsPGroup 2 U:=(pCore_isPGroup (p:=2) (G:=E)).map _
  let _ : Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3):=⟨Nat.prime_three⟩
  let _ : Group.IsNilpotent U:=hUtwo.isNilpotent
  have hnonzero (M:Subgroup D) (hM:Nat.card M=3)
      (hMnot:¬V⊓centralizer (M.map D.subtype:Set G)≤Z) : FixedPoints.subgroup M X≠⊥ := by
    let AM:=M.map D.subtype
    have hMP:AM≤P:=(map_subtype_le M).trans hDP
    have hMp:IsPGroup 3 M:=IsPGroup.of_card (n:=1) (by simpa using hM)
    have hAMp:IsPGroup 3 AM:=hMp.map D.subtype
    have hcop:Nat.Coprime (Nat.card AM) (Nat.card U):=
      IsPGroup.coprime_card_of_ne 3 2 (by decide) AM U hAMp hUtwo
    have hnotfull:=ten_one_large_terminal_factor_not_full ctx middle hpath hno
      AM (V⊓centralizer (AM:Set G)) hMP inf_le_left inf_le_right hMnot
    have hne:=native_coprime_quotient_fixed_ne_bot_of_not_full P U V AM hVU hPU hPV hMP
      inferInstance hcop hN action hformula hnotfull
    have hcompare:=fixedPoints_subgroup_of_subtype_image P D hDP action M hMP
    exact fun hb=>hne (hcompare.trans hb)
  have hKne:=hnonzero K hK hKnot
  have hLne:=hnonzero L hL hLnot
  obtain ⟨hKcard,hLcard,hcompl⟩:=nine_sixteen_prescribed_fixed_factors hcard K L hK hL hKL
    hfixed hKne hLne
  have hdata (M:Subgroup D) (hM:Nat.card M=3) :
      let QM:=U⊓centralizer (M.map D.subtype:Set G)
      let WM:=V⊓centralizer (M.map D.subtype:Set G)
      ∃ hNM:(WM.subgroupOf QM).Normal,
        let _:=hNM
        (QM.subgroupOf U).map q=FixedPoints.subgroup M X ∧
        Nonempty ((QM⧸WM.subgroupOf QM)≃*FixedPoints.subgroup M X) := by
    let AM:=M.map D.subtype
    have hMP:AM≤P:=(map_subtype_le M).trans hDP
    have hMp:IsPGroup 3 M:=IsPGroup.of_card (n:=1) (by simpa using hM)
    have hAMp:IsPGroup 3 AM:=hMp.map D.subtype
    have hcop:Nat.Coprime (Nat.card AM) (Nat.card U):=
      IsPGroup.coprime_card_of_ne 3 2 (by decide) AM U hAMp hUtwo
    obtain ⟨himage,hNM,⟨equiv⟩,_⟩:=native_coprime_quotient_fixed_card P U V AM hVU hPU hPV hMP
      inferInstance hcop hN action hformula
    let _:=hNM
    have hcompare:=fixedPoints_subgroup_of_subtype_image P D hDP action M hMP
    exact ⟨hNM,himage.symm.trans hcompare,⟨equiv.trans (MulEquiv.subgroupCongr hcompare)⟩⟩
  obtain ⟨hN1,hmap1,⟨e1⟩⟩:=hdata K hK
  obtain ⟨hN2,hmap2,⟨e2⟩⟩:=hdata L hL
  let _:=hN1
  let _:=hN2
  have hQ1U:Q1≤U:=inf_le_left
  have hQ2U:Q2≤U:=inf_le_left
  have hW1Q:W1≤Q1:=inf_le_inf hVU le_rfl
  have hW2Q:W2≤Q2:=inf_le_inf hVU le_rfl
  have hVjoin:V≤Q1⊔Q2:=hVgen.le.trans
    (sup_le (hW1Q.trans le_sup_left) (hW2Q.trans le_sup_right))
  have hker:q.ker≤Q1.subgroupOf U⊔Q2.subgroupOf U:=by
    rw [QuotientGroup.ker_mk',←subgroupOf_sup hQ1U hQ2U]
    exact fun _ hv=>hVjoin hv
  have hjoin:Q1.subgroupOf U⊔Q2.subgroupOf U=⊤:=by
    apply map_injective_of_ker_le (f:=q) hker le_top
    rw [Subgroup.map_sup,hmap1,hmap2,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
    exact hcompl.sup_eq_top
  have hUgen:U=Q1⊔Q2:=by
    have hh:=congrArg (Subgroup.map U.subtype) hjoin
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hQ1U,map_subgroupOf_eq_of_le hQ2U,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.symm
  have hcentral:U⊓centralizer (D:Set G)≤Z:=by
    intro x hx
    have hxfix:q (⟨x,hx.1⟩:U)∈FixedPoints.subgroup (⊤:Subgroup D) X:=by
      intro d
      change action (inclusion hDP (d:D)) (q (⟨x,hx.1⟩:U))=q (⟨x,hx.1⟩:U)
      rw [hformula]
      apply congrArg q
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hx.2 (d:D) (d:D).property)
    have hxq:q (⟨x,hx.1⟩:U)=1:=hfixed.le hxfix
    have hxV:x∈V:=(QuotientGroup.eq_one_iff (N:=V.subgroupOf U) (⟨x,hx.1⟩:U)).mp hxq
    apply hinter.le
    exact ⟨⟨hxV,(centralizer_le (map_subtype_le K)) hx.2⟩,
      ⟨hxV,(centralizer_le (map_subtype_le L)) hx.2⟩⟩
  exact ⟨hVU,hUgen,hcentral,hN1,hN2,
    elementary_two_of_equiv_subgroup _ e1,(Nat.card_congr e1.toEquiv).trans hKcard,
    elementary_two_of_equiv_subgroup _ e2,(Nat.card_congr e2.toEquiv).trans hLcard⟩
end Stellmacher.SectionTen
