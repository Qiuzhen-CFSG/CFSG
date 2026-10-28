module
public import Stellmacher.SectionTen.TenOneLargeCentralizerAction
public import Stellmacher.SectionTen.TenOneLargeResidualJoinIndex
public import Stellmacher.SectionTen.TenOneLargeTerminalResidualIrreducible
public import Theory.GroupAction.QuotientCommutatorFamily
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Common module centralizers act centrally on the terminal residual core

In the actual large Section Ten context, a subgroup of the terminal core
which centralizes both endpoint neighbor modules has commutator with the
terminal residual core contained in the terminal center. No invariance of
that supplied subgroup is assumed.

Enlarge C by the terminal module V. The established residual action on
C_Q(V) normalizes this enlargement modulo V. Its commutator pairing on the
terminal residual core U takes values in V/Z. Each scalar pairing kills V
and the first seed Vfirst∩U. These subgroups have join of order64 in U of
order512, so each image has order at most8. The actual residual acts
irreducibly on V/Z of order16; the proved centralizing-family theorem
therefore makes every pairing trivial. Restricting back to C gives the claim.

Source: Stellmacher (10.1), printed p.65, the last commutator step. All
subgroups and the quotient action retain the original graph and ambient data.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped IsMulCommutative commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_common_module_centralizer_action
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (C : Subgroup G)
    (hC : C ≤ QAt ctx.Γ ctx.criticalPath.a' ⊓ centralizer
      (VAt ctx.Γ ctx.criticalPath.a' : Set G))
    (hCA : C ≤ centralizer (VAt ctx.Γ ctx.criticalPath.firstStep : Set G)) :
    ⁅C,twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a' := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let U := twoCoreIn E
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let A := VAt ctx.Γ ctx.criticalPath.firstStep
  let BB := C ⊔ V
  let K := A ⊓ U
  let J := V ⊔ K
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨alignment,_,halign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  obtain ⟨hZcard,hVQ,_⟩ := nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hshort ctx.criticalPath.a' ⟨alignment,halign⟩
  obtain ⟨hN,hW,action,hformula,hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort ctx.criticalPath.a' ⟨alignment,halign⟩
  let _ := hN
  let _ := hW
  let W := V ⧸ Z.subgroupOf V
  have hE : E = twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hUP : U ≤ P := (twoCoreIn_le E).trans hEP
  have hPU : P ≤ normalizer (U : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hUP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hQP : Q ≤ P := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a' ≤ P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hUQ : U ≤ Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a') ≤ ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hPV : P ≤ normalizer (V : Set G) := stabilizer_le_normalizer_v ctx.Γ _
  have hPZ : P ≤ normalizer (Z : Set G) := stabilizer_le_normalizer_z ctx.Γ _
  have hZV : Z ≤ V := hVQ.symm.le.trans
    (le_normalizer_iff_commutator_le_left.mp (hQP.trans hPV))
  have hVUcomm : ⁅V,U⁆ ≤ Z := (commutator_mono le_rfl hUQ).trans_eq hVQ
  obtain ⟨_,D,hVD,hDU,_⟩ := ten_one_large_noncentral_chief_factor ctx middle hpath hno
  have hVU : V ≤ U := hVD.trans hDU.le
  have hVQle : V ≤ Q := hVU.trans hUQ
  let _ : IsElementaryAbelian 2 V :=
    (nine_three_second_extraction_inputs ctx.toLocalContext.toSectionNineLocalContext hshort).2.2.1
  have hBC1 : BB ≤ Q ⊓ centralizer (V : Set G) :=
    sup_le hC (le_inf hVQle (le_centralizer V))
  have hBQ : BB ≤ Q := hBC1.trans inf_le_left
  have hBV : BB ≤ centralizer (V : Set G) := hBC1.trans inf_le_right
  have hBE : ⁅BB,E⁆ ≤ V := (commutator_mono hBC1 le_rfl).trans
    (ten_one_large_centralizer_residual_commutator ctx middle hpath hno)
  have hEB : E ≤ normalizer (BB : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hBE.trans le_sup_right)
  have hBU : ⁅BB,U⁆ ≤ V := (commutator_mono le_rfl (twoCoreIn_le E)).trans hBE
  have hVcard : Nat.card V = 32 := (ten_one_large_terminal_structure ctx middle hpath hno).2.1
  have hAcard : Nat.card A = 32 := by
    change Nat.card (v ctx.Γ ctx.criticalPath.a') = 32 at hVcard
    rw [←halign,v_act,card_map_of_injective (MulAut.conj alignment⁻¹).injective] at hVcard
    exact hVcard
  have hIcard : Nat.card (A ⊓ V : Subgroup G) = 8 :=
    (ten_one_large_terminal_structure ctx middle hpath hno).2.2
  have hUcard : Nat.card U = 512 := by
    have hh : Nat.card U = 16 * Nat.card V := ten_one_large_residual_quotient_card ctx middle hpath hno
    rw [hVcard] at hh
    exact hh
  have hKcard : Nat.card K = 16 := by
    have hh : Nat.card A = 2 * Nat.card K :=
      (ten_one_large_first_residual_index ctx middle hpath hno).1
    rw [hAcard] at hh
    omega
  have hJcard : Nat.card J = 64 := by
    have hVK : V ⊓ K = A ⊓ V := by
      ext x
      exact ⟨fun hx => ⟨hx.2.1,hx.1⟩, fun hx => ⟨hx.2,hx.1,hVU hx.2⟩⟩
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes V K
      ((show K ≤ U from inf_le_right).trans (hUP.trans hPV))
    rw [hVcard,hKcard,hVK,hIcard] at hh
    change 32 * 16 = 8 * Nat.card J at hh
    omega
  have hJU : J ≤ U := sup_le hVU inf_le_right
  have hCK : ⁅C,K⁆ ≤ Z := by
    have hz : ⁅C,K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (hCA.trans (centralizer_le (show K ≤ A from inf_le_left)))
    rw [hz]
    exact bot_le
  have hBK : ⁅BB,K⁆ ≤ Z := by
    have hpre : BB ≤ commutatorPreimage Q K Z := sup_le
      (le_commutatorPreimage (hC.trans inf_le_left) hCK)
      (le_commutatorPreimage hVQle ((commutator_mono le_rfl inf_le_right).trans hVUcomm))
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le Q K Z (hQP.trans hPZ))
  have hquotCard : Nat.card W = 16 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (subgroupOfEquivOfLe hZV).toEquiv,hZcard,hVcard] at hh
    change 32 = Nat.card W * 2 at hh
    omega
  have hsmall (b : BB) :
      Nat.card ((⁅zpowers (b:G),U⁆.subgroupOf V).map (QuotientGroup.mk' (Z.subgroupOf V))) < Nat.card W := by
    let f := centralQuotientCommutatorPairing BB U V Z le_sup_right hBV hBU hVUcomm b
    have hVk : V.subgroupOf U ≤ f.ker := by
      intro v hv
      apply MonoidHom.mem_ker.mpr
      rw [show f v = _ from centralQuotientCommutatorPairing_apply BB U V Z
        le_sup_right hBV hBU hVUcomm b v]
      apply (QuotientGroup.eq_one_iff _).mpr
      have hz : ⁅BB,V⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hBV
      exact (show ⁅BB,V⁆ ≤ Z from hz ▸ bot_le) (commutator_mem_commutator b.property hv)
    have hKk : K.subgroupOf U ≤ f.ker := by
      intro k hk
      apply MonoidHom.mem_ker.mpr
      rw [show f k = _ from centralQuotientCommutatorPairing_apply BB U V Z
        le_sup_right hBV hBU hVUcomm b k]
      exact (QuotientGroup.eq_one_iff _).mpr (hBK (commutator_mem_commutator b.property hk))
    have hJk : J.subgroupOf U ≤ f.ker := by
      rw [show J.subgroupOf U = V.subgroupOf U ⊔ K.subgroupOf U from subgroupOf_sup hVU inf_le_right]
      exact sup_le hVk hKk
    have hkcard : 64 ≤ Nat.card f.ker := by
      have hh := card_le_of_le hJk
      rw [Nat.card_congr (subgroupOfEquivOfLe hJU).toEquiv,hJcard] at hh
      exact hh
    have hh := f.ker.index_mul_card
    rw [index_ker,hUcard] at hh
    have hbound : Nat.card f.range ≤ 8 := by nlinarith
    rw [←centralQuotientCommutatorPairing_range BB U V Z le_sup_right hBV hBU hVUcomm b]
    exact hbound.trans_lt (by rw [hquotCard]; decide)
  let actionE : E →* MulAut W := action.comp (inclusion hEP)
  have hformulaE (e : E) (v : V) :
      actionE e (QuotientGroup.mk' (Z.subgroupOf V) v) =
        QuotientGroup.mk' (Z.subgroupOf V)
          ⟨(e:G)*(v:G)*(e:G)⁻¹,
            (mem_normalizer_iff.mp ((hEP.trans hPV) e.property) v).mp v.property⟩ := by
    exact hformula (inclusion hEP e) v
  have hIrred (D : Subgroup W)
      (hD : ∀ e : E, ∀ w, w ∈ D → actionE e w ∈ D) : D = ⊥ ∨ D = ⊤ := by
    apply ten_one_large_terminal_residual_irreducible ctx middle hpath hno action hformula hkernel D
    intro p hp w hw
    exact hD ⟨(p:G),hp⟩ w hw
  let _ : (E.subgroupOf E).Normal := by rw [subgroupOf_self]; infer_instance
  have htrivial : IsPGroup 2 (E ⧸ E.subgroupOf E) := by
    apply IsPGroup.of_card (n := 0)
    simp [subgroupOf_self]
  have hresult := commutator_le_of_small_irreducible_centralizing_family E BB U V Z E
    hZV le_sup_right hBV hEB (hEP.trans hPU) (hEP.trans hPV) (hEP.trans hPZ)
    le_rfl htrivial hBU hVUcomm hBE actionE hformulaE hIrred hsmall
  exact (commutator_mono (show C ≤ BB from le_sup_left) le_rfl).trans hresult

end Stellmacher.SectionTen
