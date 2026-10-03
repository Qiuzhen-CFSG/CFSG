module
public import Stellmacher.SectionEight.EightSixNextResidualCoreAction
public import Theory.GroupAction.OddTwoGroupFiltration

/-!
# The exact next action kernel through the actual core filtration

For the actual next local group, the supplied conjugation action on Vnext/Znext
has kernel equal to its two-core. The hypotheses are the centrality of Znext,
the proved first commutator identity [Vnext,Qnext]=Znext, and the source-(8)
bound [Qnext,O²(Pnext)]≤Vnext. The original quotient normality witness and
literal action are retained. No equality between Qnext and Vnext is assumed.

Every odd subgroup of the kernel lies in O²(Pnext), because its image in the
two-residual quotient is both odd and a two-group. Its action fixes Znext and
both successive layers Vnext/Znext and Qnext/Vnext. The odd filtration
lemma therefore makes it centralize the actual Qnext. Characteristic-two
self-centralization puts it inside Qnext, where it must be trivial. Cauchy's
theorem then shows that the whole normal kernel is a two-group, and maximality
of the two-core proves the desired equality.

This supplies the faithful ordinary quotient in Stellmacher (8.6), printed
pp.43–44, and applies beyond the cost-four case whenever the same proved
filtration facts are available. The cost-four caller obtains source (8) from
the selected actor outside the next core.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u

private theorem two_group_of_odd_subgroups_trivial
    {H : Type*} [Group H] [Finite H]
    (hodd : ∀ A : Subgroup H, Odd (Nat.card A) → A = ⊥) : IsPGroup 2 H := by
  apply (isPGroup_iff_primeFactors_card_subset (p := 2) (by decide)).mpr
  intro p hp
  obtain ⟨hprime,hdiv,_⟩ := Nat.mem_primeFactors.mp hp
  by_cases heq : p = 2
  · subst p
    exact Nat.mem_primeFactors.mpr ⟨hprime,dvd_refl _,by decide⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' p (hp := ⟨hprime⟩) hdiv
  have hA := hodd (Subgroup.zpowers a) (by
    rw [Nat.card_zpowers,ha]
    exact hprime.odd_of_ne_two heq)
  have hh := congrArg (fun K : Subgroup H => Nat.card K) hA
  rw [Nat.card_zpowers,Subgroup.card_bot,ha] at hh
  exact False.elim (hprime.ne_one hh)

public theorem eight_six_next_quotient_action_kernel
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcomm : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep)
    (hres : ⁅QAt ctx.Γ ctx.criticalPath.firstStep,
      EAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    ∀ action : P →* MulAut (V ⧸ Z.subgroupOf V),
      (∀ actor : P, ∀ point : V,
        action actor (QuotientGroup.mk' (Z.subgroupOf V) point) =
          QuotientGroup.mk' (Z.subgroupOf V)
            ⟨(actor:G)*(point:G)*(actor:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
                  actor.property) point).mp point.property⟩) →
      pCore 2 P ≤ action.ker → action.ker = pCore 2 P := by
  classical
  let _ := hN
  dsimp only
  intro action haction hkernel
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  have hRP : R ≤ P := by
    change Γ.twoCoreAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hPR := stabilizer_le_normalizer_q Γ cp.firstStep
  have hPV := stabilizer_le_normalizer_v Γ cp.firstStep
  have hZV : Z ≤ V := by
    change ZAt ctx.Γ ctx.criticalPath.firstStep ≤ V
    rw [← hcomm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hRP.trans hPV)
  have hRtwo : IsPGroup 2 R := by
    change IsPGroup 2 (Γ.twoCoreAt cp.firstStep)
    rw [Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  let original : P →* MulAut R :=
    R.normalizerMonoidHom.comp (Subgroup.inclusion hPR)
  have hoddKernel : ∀ A : Subgroup P, A ≤ action.ker → Odd (Nat.card A) → A = ⊥ := by
    intro A hAK hAodd
    let E := BenderSuzuki.External.hktPResidual 2 P
    let _ : E.Normal := BenderSuzuki.External.hktPResidual_normal
    let πE := QuotientGroup.mk' E
    have hE2 : IsPGroup 2 (P ⧸ E) := BenderSuzuki.External.hktPResidual_quotient_isPGroup
    have himage2 : IsPGroup 2 (A.map πE) := hE2.to_subgroup _
    have himageOdd : Nat.Coprime 2 (Nat.card (A.map πE)) :=
      hAodd.coprime_two_left.of_dvd_right (Subgroup.card_map_dvd A πE)
    have himage : A.map πE = ⊥ := by
      apply Subgroup.card_eq_one.mp
      rcases himage2.card_eq_or_dvd with h | h
      · exact h
      · exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp himageOdd) h)
    have hAE : A ≤ E := by
      have hh := (Subgroup.map_eq_bot_iff (f := πE) (H := A)).mp himage
      simpa only [πE,QuotientGroup.ker_mk'] using hh
    have hEambient : E.map P.subtype = EAt Γ cp.firstStep := by
      rw [EAt,CosetGraphContext.e,Γ.twoResidualAt_def]
      rw [twoResidualIn,twoResidualAmbient,SectionThree.twoResidualSubgroup_eq_hktPResidual']
      rfl
    let _ : MulDistribMulAction A R := MulDistribMulAction.compHom R
      (original.comp A.subtype)
    have hformula (a : A) (r : R) : ((a • r : R) : G) =
        ((a:P):G) * (r:G) * ((a:P):G)⁻¹ := rfl
    have hfixedZ : ∀ a : A, ∀ z ∈ Z.subgroupOf R, a • z = z := by
      intro a z hz
      apply Subtype.ext
      rw [hformula]
      obtain ⟨zP,hzP,hzval⟩ := hcenter hz
      have hcz := Subgroup.mem_center_iff.mp hzP (a:P)
      have hc : ((a:P):G) * (z:G) = (z:G) * ((a:P):G) := by
        change (zP:G) = (z:G) at hzval
        rw [← hzval]
        exact congrArg Subtype.val hcz
      rw [hc,mul_inv_cancel_right]
    have hmiddle : ∀ a : A, ∀ v ∈ V.subgroupOf R,
        v⁻¹ * (a • v) ∈ Z.subgroupOf R := by
      intro a v hv
      let vV : V := ⟨v,hv⟩
      have hh := congrArg (fun f : MulAut (V ⧸ Z.subgroupOf V) =>
        f (QuotientGroup.mk' (Z.subgroupOf V) vV))
        (MonoidHom.mem_ker.mp (hAK a.property))
      rw [haction] at hh
      have hd := QuotientGroup.eq.mp hh.symm
      change (v:G)⁻¹ * (((a:P):G)*(v:G)*((a:P):G)⁻¹) ∈ Z at hd
      exact hd
    have htop : ∀ a : A, ∀ r : R,
        r⁻¹ * (a • r) ∈ V.subgroupOf R := by
      intro a r
      have haE : ((a:P):G) ∈ EAt Γ cp.firstStep := by
        rw [← hEambient]
        exact Subgroup.mem_map_of_mem P.subtype (hAE a.property)
      have hc := hres (Subgroup.commutator_mem_commutator
        (R.inv_mem r.property) haE)
      change (r:G)⁻¹ * (((a:P):G)*(r:G)*((a:P):G)⁻¹) ∈ V
      simpa only [commutatorElement_def,inv_inv,mul_assoc] using hc
    have hfixed := MulDistribMulAction.trivial_of_odd_of_two_group_filtration
      hAodd hRtwo (Z.subgroupOf R) (V.subgroupOf R)
      (Subgroup.subgroupOf_mono R hZV) hfixedZ hmiddle htop
    have hAcore : A ≤ pCore 2 P := by
      intro a ha
      apply (edge_characteristic_data ctx.sectionSeven Γ cp).2
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      apply Subtype.ext
      have hqR : (q:G) ∈ R := by
        change (q:G) ∈ Γ.twoCoreAt cp.firstStep
        rw [Γ.twoCoreAt_def]
        exact Subgroup.mem_map_of_mem P.subtype hq
      have hh := congrArg Subtype.val (hfixed ⟨a,ha⟩ ⟨q,hqR⟩)
      rw [hformula] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hAtwo : IsPGroup 2 A := pCore_isPGroup.to_le hAcore
    apply Subgroup.card_eq_one.mp
    rcases hAtwo.card_eq_or_dvd with h | h
    · exact h
    · exact False.elim (hAodd.not_two_dvd_nat h)
  have hKtwo : IsPGroup 2 action.ker := by
    apply two_group_of_odd_subgroups_trivial
    intro A hA
    have hmap := hoddKernel (A.map action.ker.subtype) (Subgroup.map_subtype_le _) (by
      rw [Subgroup.card_map_of_injective action.ker.subtype_injective]
      exact hA)
    apply (Subgroup.map_injective action.ker.subtype_injective)
    simpa only [Subgroup.map_bot] using hmap
  exact le_antisymm (le_sSup ⟨inferInstance,hKtwo⟩) hkernel
end Stellmacher.SectionEight
