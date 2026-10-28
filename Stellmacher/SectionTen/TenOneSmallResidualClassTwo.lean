module
public import Stellmacher.SectionTen.TenOneSmallResidualQuotientCard
public import Theory.GroupTheory.Commutator.CentralElementaryFourQuotient
public import Theory.GroupAction.FourInvariantDichotomy

/-!
# The small residual core is abelian modulo the first central line

In the actual small branch of Section Ten, the commutator of the first
residual two-core lies in the first vertex center. This proves that the
residual core modulo that central line is abelian.

The established quotient R/V is elementary of order four, while V has order
eight and its first-core commutator is the order-two central line Z. Thus
V/Z is central in R/Z and (R/Z)/(V/Z) is elementary of order four. The
central elementary-four extension bound gives the derived subgroup of R/Z
order at most two. Its identical image inside V/Z is invariant under the
first stabilizer. The actual faithful quotient action has order six on this
four-element module, so the invariant-subgroup dichotomy makes that image
trivial. The proof retains the literal subgroup quotients and explicitly
identifies both derived images through their relative indices.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (10.1)(a),
printed p.60, the assertion immediately following the residual quotient
order-four calculation. No abelian residual quotient or desired commutator
containment is assumed.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_residual_commutator_le_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep),
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆ ≤
        ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let vertex := ctx.criticalPath.firstStep
  let P := GAt ctx.Γ vertex
  let Q := QAt ctx.Γ vertex
  let E := EAt ctx.Γ vertex
  let R := twoCoreIn E
  let V := VAt ctx.Γ vertex
  let Z := ZAt ctx.Γ vertex
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hE : E = twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hRQ : R ≤ Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt vertex) ≤ ctx.Γ.twoCoreAt vertex
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hQP : Q ≤ P := by
    change ctx.Γ.twoCoreAt vertex ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hRP := hRQ.trans hQP
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v ctx.Γ vertex
  have hVR : V ≤ R := ten_one_small_module_le_residual_core ctx middle hpath hsmall hmodel
  have hRcard : Nat.card R = 32 := ten_one_small_residual_core_card ctx middle hpath hsmall hmodel
  obtain ⟨hNV, helementary, _⟩ := ten_one_small_residual_quotient_elementary
    ctx middle hpath hsmall hmodel
  let _ := hNV
  obtain ⟨hZcard, hVQ, _⟩ := nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hb vertex ⟨1, ctx.Γ.act_one _⟩
  change Nat.card Z = 2 at hZcard
  change ⁅V, Q⁆ = Z at hVQ
  have hZV : Z ≤ V := by
    rw [← hVQ]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPV)
  have hZR := hZV.trans hVR
  have hPZ : P ≤ Subgroup.centralizer (Z : Set G) :=
    nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext
      vertex ⟨1, ctx.Γ.act_one _⟩
  have hNZ : (Z.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZR).mpr
      ((hRP.trans hPZ).trans (Subgroup.centralizer_le_normalizer _))
  let _ := hNZ
  let W := R ⧸ Z.subgroupOf R
  let quotientR : R →* W := QuotientGroup.mk' (Z.subgroupOf R)
  let K := (V.subgroupOf R).map quotientR
  let _ : K.Normal := hNV.map quotientR (QuotientGroup.mk'_surjective (Z.subgroupOf R))
  have hKcentral : K ≤ Subgroup.center W := by
    rintro point ⟨pointR, hpointR, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro vector
    obtain ⟨vectorR, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf R) vector
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    change ⁅(vectorR : G), (pointR : G)⁆ ∈ Z
    rw [← hVQ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (hRQ vectorR.property) hpointR
  let _ : IsElementaryAbelian 2 (R ⧸ V.subgroupOf R) := helementary
  have hnativeDerived : commutator R ≤ V.subgroupOf R :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hmapDerived : (commutator R).map quotientR = commutator W := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr
      (QuotientGroup.mk'_surjective (Z.subgroupOf R))]
    rfl
  have hderivedK : commutator W ≤ K := by
    rw [← hmapDerived]
    exact Subgroup.map_mono hnativeDerived
  have hsquare (point : R) : point ^ 2 ∈ V.subgroupOf R := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (V.subgroupOf R) (point ^ 2) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ V.subgroupOf R)) _
  let _ : IsElementaryAbelian 2 (W ⧸ K) := {
    toIsMulCommutative := Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hderivedK
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro point
      obtain ⟨pointW, rfl⟩ := QuotientGroup.mk'_surjective K point
      obtain ⟨pointR, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf R) pointW
      rw [← map_pow, ← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact Subgroup.mem_map_of_mem quotientR (hsquare pointR) }
  have hWcard : Nat.card W = 16 := by
    have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf R)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv, hZcard, hRcard] at hcount
    change 32 = Nat.card W * 2 at hcount
    omega
  have hKcard : Nat.card K = 4 := by
    change Nat.card ((V.subgroupOf R).map (QuotientGroup.mk' (Z.subgroupOf R))) = 4
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hVR]
    have hcount := (Z.subgroupOf V).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv, hZcard] at hcount
    change Z.relIndex V * 2 = Nat.card V at hcount
    change Nat.card V = 8 at hsmall
    omega
  have hquotCard : Nat.card (W ⧸ K) = 4 := by
    have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [hWcard, hKcard] at hcount
    omega
  have hderivedSmall : Nat.card (commutator W) ≤ 2 :=
    card_commutator_le_two_of_central_elementary_four_quotient K hKcentral hquotCard
  let D := DerivedAmbient R
  have hDR : D ≤ R := Subgroup.map_subtype_le _
  have hDV : D ≤ V := by
    have hh := Subgroup.map_mono (f := R.subtype) hnativeDerived
    rw [Subgroup.map_subgroupOf_eq_of_le hVR] at hh
    exact hh
  have hDnative : D.subgroupOf R = commutator R :=
    Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
  have hDcomm : D = ⁅R, R⁆ := Subgroup.map_subtype_commutator R
  have hPD : P ≤ Subgroup.normalizer (D : Set G) := by
    intro actor hactor
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hRmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPR hactor)
    change R.map (MulAut.conj actor).toMonoidHom = R at hRmap
    change D.map (MulAut.conj actor).toMonoidHom = D
    rw [hDcomm, Subgroup.map_commutator, hRmap]
  obtain ⟨hNZV, _, action, haction, hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hb vertex ⟨1, ctx.Γ.act_one _⟩
  let _ := hNZV
  let M := V ⧸ Z.subgroupOf V
  let quotientV : V →* M := QuotientGroup.mk' (Z.subgroupOf V)
  let L := (D.subgroupOf V).map quotientV
  have hLcard : Nat.card L ≤ 2 := by
    have heq : Nat.card L = Nat.card (commutator W) := by
      rw [← hmapDerived, ← hDnative]
      change Nat.card ((D.subgroupOf V).map (QuotientGroup.mk' (Z.subgroupOf V))) =
        Nat.card ((D.subgroupOf R).map (QuotientGroup.mk' (Z.subgroupOf R)))
      rw [← Subgroup.relIndex_ker, ← Subgroup.relIndex_ker,
        QuotientGroup.ker_mk', QuotientGroup.ker_mk',
        Subgroup.relIndex_subgroupOf hDV, Subgroup.relIndex_subgroupOf hDR]
    exact heq ▸ hderivedSmall
  have hMcard : Nat.card M = 4 := by
    have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv, hZcard] at hcount
    change Nat.card V = Nat.card M * 2 at hcount
    change Nat.card V = 8 at hsmall
    omega
  have hQnative : Q.subgroupOf P = pCore 2 P := by
    change (ctx.Γ.twoCoreAt vertex).subgroupOf P = _
    rw [ctx.Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hactorsCard : Nat.card action.range = 6 := by
    obtain ⟨projection, hsurj, hker⟩ := hmodel
    rw [← Subgroup.index_ker, hkernel, ← hQnative, ← hker, Subgroup.index_ker]
    rw [MonoidHom.range_eq_top.mpr hsurj, Nat.card_congr Subgroup.topEquiv.toEquiv]
    exact SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  have hforward (actor : action.range) (point : M) (hpoint : point ∈ L) :
      actor • point ∈ L := by
    obtain ⟨actorP, hactorP⟩ := actor.property
    obtain ⟨pointV, hpointV, rfl⟩ := hpoint
    change (actor : MulAut M) (quotientV pointV) ∈ L
    rw [← hactorP, haction]
    exact Subgroup.mem_map_of_mem quotientV
      ((Subgroup.mem_normalizer_iff.mp (hPD actorP.property) pointV).mp hpointV)
  let _ : IsInvariant action.range M L := ⟨by
    intro actor point
    constructor
    · exact hforward actor point
    · intro hpoint
      have hh := hforward actor⁻¹ (actor • point) hpoint
      simpa only [inv_smul_smul] using hh⟩
  have hLzero : L = ⊥ := by
    rcases four_invariant_eq_bot_or_top action.range hMcard
      (by rw [hactorsCard]; decide) L with hbot | htop
    · exact hbot
    · have hc := hLcard
      rw [htop, Nat.card_congr Subgroup.topEquiv.toEquiv, hMcard] at hc
      omega
  have hDZ : D ≤ Z := by
    have hle := (Subgroup.map_eq_bot_iff (D.subgroupOf V)).mp hLzero
    change D.subgroupOf V ≤ (QuotientGroup.mk' (Z.subgroupOf V)).ker at hle
    rw [QuotientGroup.ker_mk'] at hle
    intro point hpoint
    exact hle (show (⟨point, hDV hpoint⟩ : V) ∈ D.subgroupOf V from hpoint)
  change ⁅R, R⁆ ≤ Z
  rw [← hDcomm]
  exact hDZ
end Stellmacher.SectionTen

