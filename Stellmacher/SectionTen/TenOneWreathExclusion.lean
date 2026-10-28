module
public import Stellmacher.SectionTen.TenOneWreathCoatomData
public import Stellmacher.SectionTen.TenOneFirstCoreNoncontainment
public import Stellmacher.TwoResidualIdentification
public import Stellmacher.SectionOne.WreathFrattiniQuotientAction

/-!
# Excluding the wreath alternative in Stellmacher (10.1)

The order-thirty-two terminal module, wreath local quotient, and order-eight
endpoint intersection cannot occur for the actual quotient transvection
in Section Ten. The displacement assumption is on V/Z, exactly as in (9.5).
No ambient order-two commutator or rank assumption is introduced.

The first-module image is a normal elementary four inside the middle-core
Sylow of the actual terminal quotient. The terminal/middle-core intersection
has index at most two and commutes with the first module modulo the terminal
module. The generic wreath coatom theorem, applied through the Frattini
quotient of Q/V, therefore forces the two-residual to centralize Q/V.
The local residual core equals its commutator with that residual, so it lies
in V. Critical length three puts V in the middle core, contradicting the
transported residual-core escape from (7.6)(b).

The quotient map is the literal projection of the terminal stabilizer onto
its two-core quotient. Its supplied wreath model is used only as an
isomorphism certificate. The action on the literal Q/V and its Frattini
quotient is retained by the generic transfer.

Source: Stellmacher (10.1), printed p.60/PDF p.50, the paragraph excluding
alternative (5) using assertion (3), `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem terminal_core_action_false
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hcomm : ⁅QAt ctx.Γ ctx.criticalPath.a', EAt ctx.Γ ctx.criticalPath.a'⁆ ≤
      VAt ctx.Γ ctx.criticalPath.a') : False := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let Q := QAt Γ cp.a'
  let E := EAt Γ cp.a'
  let R := twoCoreIn E
  let U := VAt Γ cp.a'
  have hE : E = twoResidualIn P := Γ.twoResidualAt_def _
  have hperfect : BenderSuzuki.External.hktPResidual 2 E = ⊤ := by
    rw [hE]
    exact twoResidualAmbient_has_top_twoResidual P
  obtain ⟨_, _, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hodd : Odd (Nat.card (E ⧸ pCore 2 E)) := by
    rw [hE]
    exact local_residual_core_quotient_odd ctx.sectionSeven Γ cp.a' middle
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hterminal)) P le_rfl
  have hcore : R = ⁅R, E⁆ := by
    have hh := congrArg (Subgroup.map E.subtype)
      (twoCore_eq_commutator_of_residual_perfect hperfect hodd)
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hh
    exact hh
  have hRQ : R ≤ Q := by
    change twoCoreIn (Γ.twoResidualAt cp.a') ≤ Γ.twoCoreAt cp.a'
    rw [Γ.twoResidualAt_def, Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hRU : R ≤ U := hcore.le.trans ((Subgroup.commutator_mono hRQ le_rfl).trans hcomm)
  obtain ⟨alignment, _, halign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hescape := nine_seven_residual_core_escapes_neighbor
    ctx.toLocalContext.toSectionNineLocalContext cp.a' middle
      ⟨alignment, halign⟩ (Γ.adjacent_symm hterminal)
  have hb : 2 < cp.length := by have := ctx.critical_length; change 2 < ctx.criticalPath.length; omega
  have hUQm : U ≤ QAt Γ middle :=
    (show U ≤ GeneratedNeighborhoodV Γ middle from le_sSup
      ⟨cp.a', (mem_neighborhood_iff_adjacent Γ).mpr hterminal, rfl⟩).trans
        (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb middle)
  exact hescape (hRU.trans hUQm)
private theorem terminal_native_residual_action_false
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hcomm : ⁅(QAt ctx.Γ ctx.criticalPath.a').subgroupOf (GAt ctx.Γ ctx.criticalPath.a'),
      BenderSuzuki.External.hktPResidual 2 (GAt ctx.Γ ctx.criticalPath.a')⁆ ≤
        (VAt ctx.Γ ctx.criticalPath.a').subgroupOf (GAt ctx.Γ ctx.criticalPath.a')) : False := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  have hQP : QAt ctx.Γ ctx.criticalPath.a' ≤ P := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a' ≤ P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  apply terminal_core_action_false ctx middle hpath
  apply Subgroup.commutator_le.mpr
  intro q hq e he
  have hE : EAt ctx.Γ ctx.criticalPath.a' = twoResidualIn P := ctx.Γ.twoResidualAt_def _
  rw [hE] at he
  obtain ⟨en, hen, rfl⟩ := he
  have hen' : en ∈ BenderSuzuki.External.hktPResidual 2 P := by
    rwa [← SectionThree.twoResidualSubgroup_eq_hktPResidual']
  exact hcomm (Subgroup.commutator_mem_commutator
    (show (⟨q, hQP hq⟩ : P) ∈ (QAt ctx.Γ ctx.criticalPath.a').subgroupOf P from hq) hen')

set_option maxHeartbeats 800000 in
public theorem ten_one_wreath_alternative_false
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : G) (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hlarge : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hIcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) = 2 ^ 3) : False := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let Q := (QAt Γ cp.a').subgroupOf P
  let V := (VAt Γ cp.a').subgroupOf P
  let C := (VAt Γ cp.firstStep).subgroupOf P
  let N := (QAt Γ middle ⊓ QAt Γ cp.a').subgroupOf P
  have hb : 1 < cp.length := by have := ctx.critical_length; change 1 < ctx.criticalPath.length; omega
  have hQP : QAt Γ cp.a' ≤ P := by
    change Γ.twoCoreAt cp.a' ≤ P
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hVP : VAt Γ cp.a' ≤ P :=
    (neighbor_join_le_core_of_length_gt_one Γ cp hb _).trans hQP
  let _ : Q.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr
    (stabilizer_le_normalizer_q Γ cp.a')
  let _ : V.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVP).mpr
    (stabilizer_le_normalizer_v Γ cp.a')
  have hQtwo : IsPGroup 2 Q := by
    have heq : Q = pCore 2 P := by
      change (Γ.twoCoreAt cp.a').subgroupOf P = _
      rw [Γ.twoCoreAt_def]
      exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
    rw [heq]
    exact pCore_isPGroup
  have hmodelCopy := hmodel
  obtain ⟨projection, hprojection, hprojectionKernel⟩ := hmodel
  let f : P →* (P ⧸ Q) := QuotientGroup.mk' Q
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective Q
  have hkernel : f.ker = Q := QuotientGroup.ker_mk' Q
  let modelEquiv : (P ⧸ Q) ≃* SL2TwoWreathC2 :=
    (QuotientGroup.quotientMulEquivOfEq hprojectionKernel.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective projection hprojection)
  obtain ⟨sylow, hCS, hCN, hCE, hCc, hcoatom, hcomm⟩ :=
    ten_one_wreath_coatom_data ctx middle hpath actor hactor hindex hlarge hmodelCopy hIcard
      f hsurj hkernel
  have hcoatomNative : N.relIndex Q ∣ 2 := by
    change ((QAt Γ middle ⊓ QAt Γ cp.a').subgroupOf P).relIndex
      ((QAt Γ cp.a').subgroupOf P) ∣ 2
    rwa [Subgroup.relIndex_subgroupOf hQP]
  have hcommNative : ⁅N, C⁆ ≤ V := by
    apply Subgroup.commutator_le.mpr
    intro n hn a ha
    change ⁅(n : G), (a : G)⁆ ∈ VAt Γ cp.a'
    exact hcomm (Subgroup.commutator_mem_commutator hn ha)
  obtain ⟨actionTop, hactionTop⟩ := Subgroup.exists_quotient_conjugation_action
    (⊤ : Subgroup P) Q V (by rw [Subgroup.normalizer_eq_top])
      (by rw [Subgroup.normalizer_eq_top]) inferInstance
  let action := actionTop.comp (Subgroup.topEquiv.symm.toMonoidHom)
  have hformula (mover : P) (point : Q) :
      action mover (QuotientGroup.mk' (V.subgroupOf Q) point) =
        QuotientGroup.mk' (V.subgroupOf Q) (MulAut.conjNormal mover point) :=
    hactionTop ⟨mover, Subgroup.mem_top mover⟩ point
  have hres := SectionOne.wreath_residual_commutator_le_of_fixed_coatom
    Q V hQtwo f hsurj hkernel ⟨modelEquiv⟩ sylow C N
      hCS hCN hCE hCc hcoatomNative hcommNative action hformula
  exact terminal_native_residual_action_false ctx middle hpath hres

end Stellmacher.SectionTen
