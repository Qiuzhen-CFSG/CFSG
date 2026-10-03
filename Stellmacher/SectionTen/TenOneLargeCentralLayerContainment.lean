module
public import Theory.GroupTheory.ResidualCentralLayerSplitting
public import Theory.GroupTheory.CommutatorPreimage
public import Stellmacher.SectionTen.TenOneLargeCentralizerAction
public import Stellmacher.SectionTen.TenOneLargeTerminalResidualCentralizer

/-!
# Final containment from the terminal residual central layer

In the large Section Ten configuration, let C lie in the centralizer of
V_terminal inside Q_terminal. If its commutator with O₂(E_terminal) lies
in Z_terminal and the actual source-(20) residual-core centralizer equals
Z_terminal, then C lies in V_terminal. The source-(20) equality is explicit;
no final index bound, predecessor selection, or commutativity of C is assumed.

Set B=C V_terminal. The proved centralizer residual action gives
[B,E_terminal]≤V_terminal and hence E_terminal-normality. Both C and
V_terminal have commutators with the residual core in Z_terminal, so the
commutator-preimage subgroup gives the same bound for B. Residual perfectness
and the odd residual-core quotient let the general two-group central-layer
splitting theorem write B=V_terminal C_B(E_terminal). The supplied source-(20)
equality puts the fixed factor in Z_terminal, giving the desired containment.

Source: Stellmacher (10.1), Journal of Algebra 190 (1997), printed p.65,
the final C₂ paragraph after (20). This direct fixed-component argument
does not use the questionable preceding printed “by (ii)” implication.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_central_layer_containment
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (C : Subgroup G)
    (hC : C≤QAt ctx.Γ ctx.criticalPath.a'⊓Subgroup.centralizer
      (VAt ctx.Γ ctx.criticalPath.a' : Set G))
    (hCU : ⁅C,twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⁆≤ZAt ctx.Γ ctx.criticalPath.a')
    (hfixed : QAt ctx.Γ ctx.criticalPath.a'⊓Subgroup.centralizer
      (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') : Set G)=ZAt ctx.Γ ctx.criticalPath.a') :
    C≤VAt ctx.Γ ctx.criticalPath.a' := by
  let P:=GAt ctx.Γ ctx.criticalPath.a'
  let Q:=QAt ctx.Γ ctx.criticalPath.a'
  let E:=EAt ctx.Γ ctx.criticalPath.a'
  let U:=twoCoreIn E
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  let Z:=ZAt ctx.Γ ctx.criticalPath.a'
  let BB:=C⊔V
  have hshort : 1<ctx.criticalPath.length:=by rw [ctx.critical_length];decide
  have hVQ : V≤Q:=neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hshort _
  have hQP : Q≤P:=by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a'≤P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hE : E=twoResidualIn P:=ctx.Γ.twoResidualAt_def _
  have hEP : E≤P:=hE ▸ twoResidualIn_le P
  have hUQ : U≤Q:=by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a')≤ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hQtwo : IsPGroup 2 Q:=by
    change IsPGroup 2 (ctx.Γ.twoCoreAt ctx.criticalPath.a')
    rw [ctx.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p:=2) (G:=P)).map P.subtype
  have hBQ : BB≤Q:=sup_le (hC.trans inf_le_left) hVQ
  have hQZ : Q≤Subgroup.normalizer (Z:Set G):=
    hQP.trans (stabilizer_le_normalizer_z ctx.Γ _)
  obtain ⟨alignment,_,halign⟩:=lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hcenter:=nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
    hshort ctx.criticalPath.a' ⟨alignment,halign⟩
  have hVU : ⁅V,U⁆≤Z:=(Subgroup.commutator_mono le_rfl hUQ).trans_eq hcenter.2.1
  have hBpre : BB≤Subgroup.commutatorPreimage Q U Z:=sup_le
    (Subgroup.le_commutatorPreimage (hC.trans inf_le_left) hCU)
    (Subgroup.le_commutatorPreimage hVQ hVU)
  have hBU : ⁅BB,U⁆≤Z:=(Subgroup.commutator_mono hBpre le_rfl).trans
    (Subgroup.commutator_commutatorPreimage_le Q U Z hQZ)
  let _ : IsElementaryAbelian 2 V:=by
    have ha:=((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hshort).1
    change IsElementaryAbelian 2 (v ctx.Γ ctx.criticalPath.a')
    rw [←halign,v_act]
    exact IsElementaryAbelian.map (MulAut.conj alignment⁻¹).toMonoidHom
  have hBC1 : BB≤Q⊓Subgroup.centralizer (V:Set G):=sup_le hC
    (le_inf hVQ (Subgroup.le_centralizer V))
  have hBE : ⁅BB,E⁆≤V:=(Subgroup.commutator_mono hBC1 le_rfl).trans
    (ten_one_large_centralizer_residual_commutator ctx middle hpath hno)
  have hEB : E≤Subgroup.normalizer (BB:Set G):=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hBE.trans le_sup_right)
  have hVCE : V⊓Subgroup.centralizer (E:Set G)=Z:=
    ten_one_large_terminal_residual_centralizer ctx middle hpath hno
  have hZV : Z≤V:=hVCE.symm.le.trans inf_le_left
  have hZCE : Z≤Subgroup.centralizer (E:Set G):=hVCE.symm.le.trans inf_le_right
  have hUtwo : IsPGroup 2 U:=(pCore_isPGroup (p:=2) (G:=E)).map E.subtype
  have hUN : (U.subgroupOf E).Normal:=twoCoreIn_normal E
  let _:=hUN
  have hUeq : U.subgroupOf E=pCore 2 E:=Subgroup.comap_map_eq_self_of_injective E.subtype_injective _
  obtain ⟨_,_,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hodd : Odd (Nat.card (E⧸U.subgroupOf E)):=by
    have hh : Odd (Nat.card (E⧸pCore 2 E)):=by
      rw [hE]
      exact local_residual_core_quotient_odd ctx.sectionSeven ctx.Γ ctx.criticalPath.a' middle
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) P le_rfl
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hUeq).toEquiv]
    exact hh
  have hperfect : ∀ N:Subgroup E, ∀ hN:N.Normal, let _:=hN; IsPGroup 2 (E⧸N)→N=⊤:=by
    intro N hN
    dsimp only
    intro htwo
    have hh:=BenderSuzuki.External.hktPResidual_le N hN htwo
    have heq : BenderSuzuki.External.hktPResidual 2 E=⊤:=by
      rw [hE]
      exact twoResidualAmbient_has_top_twoResidual P
    exact top_unique (heq ▸ hh)
  have hsplit:=Subgroup.eq_sup_centralizer_of_no_two_quotient_central_layer_of_isPGroup
    E U BB V Z (twoCoreIn_le E) hUtwo
    (hQtwo.of_injective (Subgroup.inclusion hBQ) (Subgroup.inclusion_injective hBQ))
    hodd hperfect hEB
    le_sup_right (hZV.trans le_sup_right) hZCE hBE hBU
  have hfixedB : BB⊓Subgroup.centralizer (E:Set G)≤V:=
    ((le_inf (inf_le_left.trans hBQ)
      (inf_le_right.trans (Subgroup.centralizer_le (twoCoreIn_le E)))).trans_eq hfixed).trans hZV
  exact (show C≤BB from le_sup_left).trans
    (hsplit.le.trans (sup_le le_rfl hfixedB))
end Stellmacher.SectionTen
