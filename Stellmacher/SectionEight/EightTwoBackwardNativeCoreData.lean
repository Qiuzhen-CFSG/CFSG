module
public import Stellmacher.SectionEight.EightTwoBackwardLocalSetup
public import Stellmacher.SectionEight.EightTwoLocalQuotients
public import Stellmacher.UniqueMaximalContainingTransport
public import BenderSuzuki.External.Huppert.V.FrattiniQuotient

/-!
# Native core quotient and Sylow overgroups in the backward case of (8.2)

Assume the first-step vertex center is noncentral and the first-edge core
intersection is normal in the initial stabilizer. The join of the initial
two-residual and the next core has an ordinary dihedral three-power core
quotient. Every supplied Sylow whose ambient image is exactly the next core
lies in a unique maximal subgroup of this join. The length premise is retained
for the backward-branch interface; the transfer itself does not need it.

The local setup makes the join normal in the initial stabilizer. Result (7.6)
puts the next core outside the initial core. Its image in the initial ordinary
core quotient is therefore a nontrivial two-subgroup. Odd dihedral Sylows have
order at most two and normally generate, so the normal join maps onto the
whole quotient. Characteristic-normal transitivity identifies the restricted
kernel with the join's native two-core, giving the quotient isomorphism.

The two exact Sylow images in this common quotient coincide. The initial
stabilizer's P-family membership supplies unique maximality, which transfers
through both surjective maps: their kernels lie in the supplied Sylows, so
mapping and taking inverse images preserve all relevant maximal overgroups.
No native-module comparison, final contradiction, or classification is used.

Source: Stellmacher (8.2), first containment case, Journal of Algebra 190
(1997), pp.37–38, refs/latex/stellmacher-n-group.tex, with the local facts of
(7.6) and the ordinary dihedral quotient supplied by (6.3).

The local companion uses the ambient-retaining Section Eight context.
The legacy public signature is preserved by its exact graph-preserving
`toLocalContext` adapter; supplied Sylow maps and action instances are retained.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem eight_two_native_core_restriction
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal] :
    pCore 2 N = (pCore 2 G).subgroupOf N := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mp
    exact le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,
      (pCore_isPGroup (p := 2) (G := N)).map N.subtype⟩
  · exact le_sSup ⟨inferInstance,
      (pCore_isPGroup (p := 2) (G := G)).comap_of_injective N.subtype
        N.subtype_injective⟩

private theorem eight_two_native_dihedral_surjective
    {G : Type*} [Group G] [Finite G]
    (N B : Subgroup G) [N.Normal] (hBN : B ≤ N)
    (hB : IsPGroup 2 B) (hBnot : ¬ B ≤ pCore 2 G)
    (n : ℕ) (equiv : (G ⧸ pCore 2 G) ≃* DihedralGroup (3 ^ n)) :
    Function.Surjective ((QuotientGroup.mk' (pCore 2 G)).comp N.subtype) := by
  let projection := QuotientGroup.mk' (pCore 2 G)
  have hprojection : Function.Surjective projection := QuotientGroup.mk'_surjective _
  obtain ⟨U, hBU⟩ := (hB.map projection).exists_le_sylow
  have hU := odd_dihedral_quotient_sylow (3 ^ n) ((by decide : Odd 3).pow)
    equiv.symm.toMonoidHom equiv.symm.surjective U
  have hBne : B.map projection ≠ ⊥ := by
    intro heq
    apply hBnot
    have hle : B ≤ (⊥ : Subgroup (G ⧸ pCore 2 G)).comap projection :=
      Subgroup.map_le_iff_le_comap.mp heq.le
    simpa [projection] using hle
  have hcard : 1 < Nat.card (B.map projection) :=
    (B.map projection).one_lt_card_iff_ne_bot.mpr hBne
  have hBUeq : B.map projection = (U : Subgroup (G ⧸ pCore 2 G)) :=
    Subgroup.eq_of_le_of_card_ge hBU (by omega)
  have hNnormal : (N.map projection).Normal := (inferInstance : N.Normal).map _ hprojection
  let := hNnormal
  have hUN : (U : Subgroup (G ⧸ pCore 2 G)) ≤ N.map projection := by
    rw [← hBUeq]
    exact Subgroup.map_mono hBN
  have hNtop : N.map projection = ⊤ := by
    apply top_unique
    rw [← hU.2]
    exact Subgroup.normalClosure_le_normal hUN
  intro target
  obtain ⟨element, helement, hvalue⟩ := hNtop.ge (show target ∈ ⊤ from trivial)
  exact ⟨⟨element, helement⟩, hvalue⟩

private theorem eight_two_native_unique_quotient_iff
    {G K : Type u} [Group G] [Group K]
    (projection : G →* K) (hsurj : Function.Surjective projection)
    (S : Subgroup G) (hker : projection.ker ≤ S) :
    (∃! M : Subgroup G, IsCoatom M ∧ S ≤ M) ↔
      ∃! M : Subgroup K, IsCoatom M ∧ S.map projection ≤ M := by
  constructor
  · rintro ⟨M, ⟨hM, hSM⟩, huniq⟩
    refine ⟨M.map projection, ⟨?_, Subgroup.map_mono hSM⟩, ?_⟩
    · exact BenderSuzuki.External.hkt_isCoatom_map_of_surjective_of_ker_le
        projection hsurj (hker.trans hSM) hM
    · rintro U ⟨hU, hSU⟩
      have heq : U.comap projection = M := huniq _
        ⟨Subgroup.isCoatom_comap_of_surjective hsurj hU,
          Subgroup.map_le_iff_le_comap.mp hSU⟩
      rw [← heq, Subgroup.map_comap_eq_self_of_surjective hsurj]
  · rintro ⟨M, ⟨hM, hSM⟩, huniq⟩
    refine ⟨M.comap projection,
      ⟨Subgroup.isCoatom_comap_of_surjective hsurj hM,
        Subgroup.map_le_iff_le_comap.mp hSM⟩, ?_⟩
    rintro U ⟨hU, hSU⟩
    have heq : U.map projection = M := huniq _
      ⟨BenderSuzuki.External.hkt_isCoatom_map_of_surjective_of_ker_le
        projection hsurj (hker.trans hSU) hU, Subgroup.map_mono hSU⟩
    rw [← heq, Subgroup.comap_map_eq_self (hker.trans hSU)]

public theorem eight_two_backward_native_core_data_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (_hlen : 1 < ctx.criticalPath.length)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a)) :
    let L := EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep
    ∀ (T : Sylow 2 L),
      (T : Subgroup L).map L.subtype = QAt ctx.Γ ctx.criticalPath.firstStep →
      IsUniqueMaximalContaining (T : Subgroup L) (⊤ : Subgroup L) ∧
        ∃ n : ℕ, Nonempty ((L ⧸ pCore 2 L) ≃* DihedralGroup (3 ^ n)) := by
  intro L T hT
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let P := GAt Γ cp.a
  let B := QAt Γ cp.firstStep
  obtain ⟨hLN, _hgen, _hSyl⟩ := eight_two_local_setup_of_core_intersection_normal_local ctx hnormal
  have hLP : L ≤ P := hLN.1
  let N := L.subgroupOf P
  let equiv : N ≃* L := Subgroup.subgroupOfEquivOfLe hLP
  let _ : N.Normal := hLN.2
  let inclusion : L →* P := N.subtype.comp equiv.symm.toMonoidHom
  let projection := QuotientGroup.mk' (pCore 2 P)
  let nativeProjection := projection.comp inclusion
  have hprojection : Function.Surjective projection := QuotientGroup.mk'_surjective _
  have hBS : B ≤ S := (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  obtain ⟨hSP, U, hU⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  change (U : Subgroup P).map P.subtype = S at hU
  have hUnative : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  have hBP : B ≤ P := hBS.trans hSP
  have hBnot : ¬ B ≤ QAt Γ cp.a := by
    intro hB
    apply (lemma_seven_six h Γ cp).next_residual_core.1
    have hres : twoCoreIn (e Γ cp.firstStep) ≤ B := by
      change twoCoreIn (e Γ cp.firstStep) ≤ q Γ cp.firstStep
      rw [q, Γ.twoCoreAt_def]
      rw [show e Γ cp.firstStep = twoResidualIn (stabilizer Γ cp.firstStep)
        from Γ.twoResidualAt_def cp.firstStep, SevenSix.residual_core_eq_inter_core]
      exact inf_le_right
    exact hres.trans hB
  have hBN : B.subgroupOf P ≤ N := Subgroup.comap_mono le_sup_right
  have hBp : IsPGroup 2 (B.subgroupOf P) := by
    apply U.isPGroup'.to_le
    rw [hUnative]
    exact Subgroup.comap_mono hBS
  have hBcore : ¬ B.subgroupOf P ≤ pCore 2 P := by
    intro hle
    apply hBnot
    rw [show QAt Γ cp.a = (pCore 2 P).map P.subtype from Γ.twoCoreAt_def cp.a,
      ← Subgroup.map_subgroupOf_eq_of_le hBP]
    exact Subgroup.map_mono hle
  obtain ⟨n, ⟨dihedral⟩⟩ := eight_two_dihedral_core_local ctx hcenter cp.a
  have hsurj : Function.Surjective nativeProjection :=
    (eight_two_native_dihedral_surjective N (B.subgroupOf P) hBN hBp hBcore n dihedral).comp
      equiv.symm.surjective
  have hkerN : (projection.comp N.subtype).ker = pCore 2 N := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (eight_two_native_core_restriction N).symm
  have hker : nativeProjection.ker = pCore 2 L := by
    change ((projection.comp N.subtype).comp equiv.symm.toMonoidHom).ker = _
    rw [← MonoidHom.comap_ker, hkerN, ← pCore_map_iso 2 equiv.symm]
    exact Subgroup.comap_map_eq_self_of_injective equiv.symm.injective _
  have hTimage : (T : Subgroup L).map nativeProjection =
      (U : Subgroup P).map projection := by
    have hle : (T : Subgroup L).map nativeProjection ≤
        (U : Subgroup P).map projection := by
      rw [show nativeProjection = projection.comp inclusion from rfl, ← Subgroup.map_map]
      apply Subgroup.map_mono
      apply Subgroup.map_le_iff_le_comap.mpr
      intro element helement
      rw [hUnative]
      change (element : H) ∈ S
      apply hBS
      change (element : H) ∈ QAt ctx.Γ ctx.criticalPath.firstStep
      rw [← hT]
      exact Subgroup.mem_map_of_mem L.subtype helement
    exact ((T.mapSurjective hsurj).is_maximal'
      (U.isPGroup'.map projection) hle).symm
  have hPset := (pFamily_iff_pSet _ _ _).mp (SevenSix.edge_local_data h Γ cp).1.1
  have huniqP : ∃! M : Subgroup P, IsCoatom M ∧ (U : Subgroup P) ≤ M := by
    obtain ⟨M, hM, hSM, huniq⟩ := hPset.2
    refine ⟨M, ⟨hM, ?_⟩, ?_⟩
    · apply Subgroup.map_subtype_le_map_subtype.mp
      rwa [hU]
    · rintro K ⟨hK, hUK⟩
      apply huniq K hK
      simpa only [hU] using Subgroup.map_mono (f := P.subtype) hUK
  have hkerU : projection.ker ≤ (U : Subgroup P) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal U
  have huniqQ := (eight_two_native_unique_quotient_iff projection hprojection _ hkerU).mp huniqP
  rw [← hTimage] at huniqQ
  have hkerT : nativeProjection.ker ≤ (T : Subgroup L) := by
    rw [hker]
    exact pCore_isPGroup.le_sylow_of_normal T
  obtain ⟨M, ⟨hM, hTM⟩, huniq⟩ :=
    (eight_two_native_unique_quotient_iff nativeProjection hsurj _ hkerT).mpr huniqQ
  refine ⟨?_, n, ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective nativeProjection hsurj)).trans dihedral⟩⟩
  apply native_uniqueMaximalContaining L (T : Subgroup L)
  refine ⟨M, hM, Subgroup.map_mono hTM, ?_⟩
  intro K hK hTK
  exact huniq K ⟨hK, Subgroup.map_subtype_le_map_subtype.mp hTK⟩


public theorem eight_two_backward_native_core_data
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (_hlen : 1 < ctx.criticalPath.length)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a)) :
    let L := EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep
    ∀ (T : Sylow 2 L),
      (T : Subgroup L).map L.subtype = QAt ctx.Γ ctx.criticalPath.firstStep →
      IsUniqueMaximalContaining (T : Subgroup L) (⊤ : Subgroup L) ∧
        ∃ n : ℕ, Nonempty ((L ⧸ pCore 2 L) ≃* DihedralGroup (3 ^ n)) := by
  exact eight_two_backward_native_core_data_local ctx.toLocalContext hcenter _hlen hnormal

end Stellmacher.SectionEight
