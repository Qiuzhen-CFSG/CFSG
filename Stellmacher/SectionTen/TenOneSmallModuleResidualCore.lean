module
public import Stellmacher.SectionTen.TenOneFirstCoreNoncontainment
public import Stellmacher.SectionFiveToSeven.NeighborJoinCore
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Theory.GroupAction.FourInvariantDichotomy

/-!
# The small first module lies in the residual two-core

For the actual Section Ten offset-two configuration, an order-eight first
module with local quotient SL2(2) lies in the two-core of the first residual.
This proves the containment required when the source forms that residual-core
quotient in Stellmacher (10.1)(a), Journal of Algebra 190 (1997), printed p.60.

Intersect the module with the residual core. Its quotient image modulo the
first central line is nontrivial: otherwise the first residual would kill
the faithful quotient module and lie in the first two-core, contrary to
residual perfection. The actual quotient action has order six on four
elements, so the image is the whole module quotient by the invariant-subgroup
dichotomy. The intersection and central line therefore generate the module.
The first core centralizes that line, while its full module commutator equals
the line. Normality of the intersection consequently places the line in the
intersection too, proving the required containment.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

/-- The first residual escapes the first core, independently of the small case. -/
public theorem ten_one_first_residual_not_le_core
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ¬ EAt ctx.Γ ctx.criticalPath.firstStep ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  let E := EAt ctx.Γ ctx.criticalPath.firstStep
  let Q := QAt ctx.Γ ctx.criticalPath.firstStep
  have hE : E = twoResidualIn P := ctx.Γ.twoResidualAt_def _
  intro hEQ
  have hQtwo : IsPGroup 2 Q := by
    change IsPGroup 2 (ctx.Γ.twoCoreAt ctx.criticalPath.firstStep)
    rw [ctx.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := P)).map _
  have hEtwo : IsPGroup 2 E := hQtwo.to_le hEQ
  have hperfect : BenderSuzuki.External.hktPResidual 2 E = ⊤ := by
    rw [hE]
    exact twoResidualAmbient_has_top_twoResidual P
  have hzero : BenderSuzuki.External.hktPResidual 2 E ≤ ⊥ :=
    BenderSuzuki.External.hktPResidual_le (⊥ : Subgroup E) inferInstance
      (hEtwo.of_equiv QuotientGroup.quotientBot.symm)
  apply ten_one_first_core_not_le_module ctx middle hpath
  intro point hpoint
  have hpointE : point ∈ E := twoCoreIn_le E hpoint
  have hone : (⟨point, hpointE⟩ : E) = 1 := by
    apply Subgroup.mem_bot.mp
    exact hzero (hperfect.ge (Subgroup.mem_top _))
  have honeG := congrArg Subtype.val hone
  change point = 1 at honeG
  rw [honeG]
  exact (VAt ctx.Γ ctx.criticalPath.firstStep).one_mem

public theorem ten_one_small_module_le_residual_core
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    VAt ctx.Γ ctx.criticalPath.firstStep ≤
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) := by
  let vertex := ctx.criticalPath.firstStep
  let P := GAt ctx.Γ vertex
  let Q := QAt ctx.Γ vertex
  let E := EAt ctx.Γ vertex
  let R := twoCoreIn E
  let V := VAt ctx.Γ vertex
  let Z := ZAt ctx.Γ vertex
  let N := V ⊓ R
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hVQ : V ≤ Q := neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hb _
  have hQP : Q ≤ P := by
    change ctx.Γ.twoCoreAt vertex ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hVP := hVQ.trans hQP
  have hE : E = twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hRP : R ≤ P := (twoCoreIn_le E).trans hEP
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPN : P ≤ Subgroup.normalizer (N : Set G) :=
    (le_inf (stabilizer_le_normalizer_v ctx.Γ vertex) hPR).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨hZcard, hVcomm, hfaith⟩ := nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hb vertex ⟨1, ctx.Γ.act_one _⟩
  change ⁅V, Q⁆ = Z at hVcomm
  have hZV : Z ≤ V := by
    rw [← hVcomm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hQP.trans (stabilizer_le_normalizer_v ctx.Γ vertex))
  have hVEN : ⁅V, E⁆ ≤ N := le_inf
    (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hEP.trans (stabilizer_le_normalizer_v ctx.Γ vertex))) (by
      have hVEQ : ⁅V, E⁆ ≤ ⁅E, Q⁆ := by
        calc
          ⁅V, E⁆ ≤ ⁅Q, E⁆ := Subgroup.commutator_mono hVQ le_rfl
          _ = ⁅E, Q⁆ := Subgroup.commutator_comm Q E
      apply hVEQ.trans
      change ⁅E, ctx.Γ.twoCoreAt vertex⁆ ≤ twoCoreIn E
      rw [hE, ctx.Γ.twoCoreAt_def]
      exact residual_commutator_core_le P)
  have hNnotZ : ¬ N ≤ Z := by
    intro hNZ
    apply ten_one_first_residual_not_le_core ctx middle hpath
    intro actor hactor
    exact (hfaith actor (hEP hactor)).mp
      ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hactor)).trans
        (hVEN.trans hNZ))
  obtain ⟨hnormal, hW, action, haction, hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hb vertex ⟨1, ctx.Γ.act_one _⟩
  let _ := hnormal
  let W := V ⧸ Z.subgroupOf V
  let quotient : V →* W := QuotientGroup.mk' (Z.subgroupOf V)
  let D := (N.subgroupOf V).map quotient
  have hWcard : Nat.card W = 4 := by
    have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv] at hcount
    change Nat.card V = 8 at hsmall
    change Nat.card Z = 2 at hZcard
    rw [hsmall, hZcard] at hcount
    change Nat.card (V ⧸ Z.subgroupOf V) = 4
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
  have hforward (actor : action.range) (point : W) (hpoint : point ∈ D) :
      actor • point ∈ D := by
    obtain ⟨actorP, hactorP⟩ := actor.property
    obtain ⟨pointV, hpointV, rfl⟩ := hpoint
    change (actor : MulAut W) (quotient pointV) ∈ D
    rw [← hactorP, haction]
    exact Subgroup.mem_map_of_mem quotient
      ((Subgroup.mem_normalizer_iff.mp (hPN actorP.property) pointV).mp hpointV)
  let _ : IsInvariant action.range W D := ⟨by
    intro actor point
    constructor
    · exact hforward actor point
    · intro hpoint
      have hh := hforward actor⁻¹ (actor • point) hpoint
      simpa only [inv_smul_smul] using hh⟩
  have hDnon : D ≠ ⊥ := by
    intro hbot
    apply hNnotZ
    have hle := (Subgroup.map_eq_bot_iff (N.subgroupOf V)).mp hbot
    change N.subgroupOf V ≤ (QuotientGroup.mk' (Z.subgroupOf V)).ker at hle
    rw [QuotientGroup.ker_mk'] at hle
    intro point hpoint
    exact hle (show (⟨point, hpoint.1⟩ : V) ∈ N.subgroupOf V from hpoint)
  have hDtop : D = ⊤ := (four_invariant_eq_bot_or_top action.range hWcard
    (by rw [hactorsCard]; decide) D).resolve_left hDnon
  have hNZ : N ⊔ Z = V := by
    have hpre := Subgroup.comap_map_eq quotient (N.subgroupOf V)
    change D.comap quotient = N.subgroupOf V ⊔ quotient.ker at hpre
    rw [hDtop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hpre
    have hm := congrArg (Subgroup.map V.subtype) hpre
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le inf_le_left,
      Subgroup.map_subgroupOf_eq_of_le hZV, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hm
    exact hm.symm
  have hZQ : ⁅Z, Q⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (Subgroup.le_centralizer_iff.mp (hQP.trans
      (nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext
        vertex ⟨1, ctx.Γ.act_one _⟩)))
  have hZN : Z ≤ N := by
    rw [← hVcomm]
    have hNP : N ≤ P := inf_le_left.trans hVP
    have hZP : Z ≤ P := hZV.trans hVP
    let _ : (N.subgroupOf P).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr hPN
    apply Subgroup.commutator_le.mpr
    intro vector hvector actor hactor
    have hmem : (⟨vector, hVP hvector⟩ : P) ∈ N.subgroupOf P ⊔ Z.subgroupOf P := by
      rw [← Subgroup.subgroupOf_sup hNP hZP, hNZ]
      exact hvector
    obtain ⟨n, hn, z, hz, hprod⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have heq := congrArg Subtype.val hprod
    change (n : G) * (z : G) = vector at heq
    have hzero : ⁅(z : G), actor⁆ = 1 := hZQ.le
      (Subgroup.commutator_mem_commutator hz hactor)
    rw [← heq, commutatorElement_mul_left_eq_conj_mul, hzero]
    simp only [mul_one, mul_inv_cancel, one_mul]
    exact (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPN))
      (Subgroup.commutator_mem_commutator (show (n : G) ∈ N from hn) hactor)
  have hVN : V ≤ N := by rw [← hNZ]; exact sup_le le_rfl hZN
  exact hVN.trans inf_le_right
end Stellmacher.SectionTen
