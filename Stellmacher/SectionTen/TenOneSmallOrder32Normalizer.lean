module
public import Stellmacher.SectionTen.TenOneSmallAmbientCentralizerCore
public import Stellmacher.SectionTen.TenOneSmallMiddleCoreFrattini
public import Theory.GroupTheory.CharacteristicTwoFrattiniEightBound

/-!
# The middle-center normalizer when the middle core has order 32

In the small case of Stellmacher (10.1), if the middle two-core has order
32, the ambient normalizer of its central layer is exactly the embedded
middle stabilizer. The hypotheses retain the original ambient context,
critical path, and first-step quotient model.

The proof first moves to the initial vertex. Its stabilizer contains the
fixed ambient Sylow subgroup, using the established equality S = S₀.
The centralizer-core theorem makes the initial core normal in the ambient
center normalizer. Any normal two-subgroup of that normalizer lies in the
fixed Sylow and hence in the initial stabilizer, so the normalizer has
exactly the same two-core. The native Frattini equality then identifies
its core Frattini quotient as elementary of order eight, while its Sylow
two-subgroup has twice the core order. Ambient Hypothesis One applies to
this actual normalizer and supplies solvability and characteristic two.
The general Frattini-action bound gives normalizer order at most 192;
the contained stabilizer already has order 192 from its S₃ quotient.
Cardinality forces equality, which is conjugated back to the middle vertex.

Source: Stellmacher, “On the N-group theorem”, (10.1)(a3), printed p.61,
the order-32 branch of the normalizer assertion (7), in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open Subgroup
universe u

private theorem two_core_map_injective
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (P : Subgroup G) :
    twoCoreIn (P.map f) = (twoCoreIn P).map f := by
  let e := P.equivMapOfInjective f hf
  have hc : (pCore 2 P).map e.toMonoidHom = pCore 2 (P.map f) := pCore_map_iso 2 e
  unfold twoCoreIn
  rw [← hc,map_map,map_map]
  congr 1

private theorem core_overgroup_eq_of_normalized_local_core
    {H : Type u} [Group H] [Finite H] (S0 : Sylow 2 H)
    (M N : Subgroup H) (hSM : (S0 : Subgroup H) ≤ M) (hMN : M ≤ N)
    (hnorm : N ≤ normalizer (twoCoreIn M : Set H)) :
    twoCoreIn N = twoCoreIn M := by
  let R := twoCoreIn N
  let Q := twoCoreIn M
  let SN : Sylow 2 N := S0.subtype (hSM.trans hMN)
  have hRS : R ≤ (S0 : Subgroup H) := by
    rintro x ⟨r,hr,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal SN hr
  have hRM : R ≤ M := hRS.trans hSM
  have hNR : N ≤ normalizer (R : Set H) := by
    have hn := (pCore 2 N).le_normalizer_map N.subtype
    rwa [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] at hn
  let _ : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer (hMN.trans hNR)
  have hRp : IsPGroup 2 R := pCore_isPGroup.map N.subtype
  have hRQ : R ≤ Q := by
    rw [← map_subgroupOf_eq_of_le hRM]
    exact map_mono (show R.subgroupOf M ≤ pCore 2 M from
      le_sSup ⟨inferInstance,hRp.comap_subtype⟩)
  have hQN : Q ≤ N := (map_subtype_le (pCore 2 M)).trans hMN
  let _ : (Q.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hnorm
  have hQp : IsPGroup 2 Q := pCore_isPGroup.map M.subtype
  have hQR : Q ≤ R := by
    rw [← map_subgroupOf_eq_of_le hQN]
    exact map_mono (show Q.subgroupOf N ≤ pCore 2 N from
      le_sSup ⟨inferInstance,hQp.comap_subtype⟩)
  exact le_antisymm hRQ hQR

private theorem centralizer_map_equiv_order32
    {H : Type*} [Group H] (A : Subgroup H) (e : H ≃* H) :
    (centralizer (A : Set H)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set H) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image (A : Set H) e.toMonoidHom
  · intro x hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    rw [mem_centralizer_iff] at hx
    change e.symm x ∈ centralizer (A : Set H)
    rw [mem_centralizer_iff]
    intro a ha
    apply e.injective
    simpa using hx (e a) (mem_map_of_mem e.toMonoidHom ha)

private theorem card_frattini_quotient_of_equiv
    {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (X ⧸ frattini X) = Nat.card (Y ⧸ frattini Y) := by
  have he : (frattini X).map e.toMonoidHom = frattini Y := by
    apply le_antisymm
    · exact map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective e.surjective)
    · intro y hy
      refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
      exact frattini_le_comap_frattini_of_surjective
        (φ := e.symm.toMonoidHom) e.symm.surjective hy
  exact Nat.card_congr (QuotientGroup.congr _ _ e he).toEquiv

variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

/-- In the order-32 small branch, the ambient normalizer of the middle
central layer is precisely the embedded middle stabilizer. -/
public theorem ten_one_small_order32_center_normalizer
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hQcard : Nat.card (QAt ctx.Γ middle) = 32) :
    normalizer ((ZAt ctx.Γ middle).map embedding : Set H) =
      (GAt ctx.Γ middle).map embedding := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Za := ZAt Γ cp.a
  let Qa := QAt Γ cp.a
  let Ma := GAt Γ cp.a
  let Z := Za.map embedding
  let Q := Qa.map embedding
  let M := Ma.map embedding
  let N := normalizer (Z : Set H)
  let C := centralizer (Z : Set H)
  obtain ⟨hglobal,_,_,_⟩ := nine_two_ambient_setup ctx.toAmbientSectionNineContext
  obtain ⟨⟨actor,hactor⟩,_,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  let eg : G ≃* G := MulAut.conj actor⁻¹
  let eh : H ≃* H := MulAut.conj (embedding actor⁻¹)
  have hZa : Za.map eg.toMonoidHom = ZAt Γ middle := by
    change (z Γ cp.a).map (MulAut.conj actor⁻¹).toMonoidHom = z Γ middle
    rw [← z_act,hactor]
  have hQa : Qa.map eg.toMonoidHom = QAt Γ middle := by
    change (q Γ cp.a).map (MulAut.conj actor⁻¹).toMonoidHom = q Γ middle
    rw [← q_act,hactor]
  have hMa : Ma.map eg.toMonoidHom = GAt Γ middle :=
    (stabilizer_act Γ actor cp.a).symm.trans (congrArg _ hactor)
  have htransport (D : Subgroup G) :
      (D.map embedding).map eh.toMonoidHom = (D.map eg.toMonoidHom).map embedding := by
    rw [map_map,map_map]
    congr 1
    ext x
    simp [eh,eg]
  have hZtransport : Z.map eh.toMonoidHom = (ZAt Γ middle).map embedding := by rw [htransport,hZa]
  have hQtransport : Q.map eh.toMonoidHom = (QAt Γ middle).map embedding := by rw [htransport,hQa]
  have hMtransport : M.map eh.toMonoidHom = (GAt Γ middle).map embedding := by rw [htransport,hMa]
  have hQC : twoCoreIn C = Q := by
    apply map_injective (f := eh.toMonoidHom) eh.injective
    rw [← twoCoreIn_map_equiv,centralizer_map_equiv_order32,hZtransport,hQtransport]
    exact ten_one_small_ambient_center_centralizer_core ctx middle hpath hsmall hmodel
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hNC : N ≤ normalizer (C : Set H) :=
    (normal_subgroupOf_iff_le_normalizer hCN).mp (normal_subgroupOf_centralizer_normalizer _)
  have hNQ : N ≤ normalizer (Q : Set H) := by
    rw [← hQC]
    exact hNC.trans (BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
      C (pCore 2 C))
  have hQaMa : Qa ≤ Ma := by
    change Γ.twoCoreAt cp.a ≤ Γ.stabilizer cp.a
    rw [Γ.twoCoreAt_def]
    exact map_subtype_le _
  have hQM : Q ≤ M := map_mono hQaMa
  have hMN : M ≤ N := (map_mono (stabilizer_le_normalizer_z Γ cp.a)).trans (Za.le_normalizer_map embedding)
  have hSM : (S0 : Subgroup H) ≤ M := by
    rw [← hglobal,← ctx.map_S]
    exact map_mono (edge_sylow_data ctx.sectionSeven Γ cp).1.1
  have hSN : (S0 : Subgroup H) ≤ N := hSM.trans hMN
  have hMcore : twoCoreIn M = Q := by
    rw [two_core_map_injective embedding ctx.embedding_injective]
    change (twoCoreIn (GAt Γ cp.a)).map embedding = Qa.map embedding
    exact congrArg (Subgroup.map embedding) (Γ.twoCoreAt_def cp.a).symm
  have hNcore : twoCoreIn N = Q := by
    rw [← hMcore]
    exact core_overgroup_eq_of_normalized_local_core S0 M N hSM hMN (hMcore ▸ hNQ)
  have hcoreNative : pCore 2 N = Q.subgroupOf N := by
    have hh := congrArg (comap N.subtype) hNcore
    change ((pCore 2 N).map N.subtype).comap N.subtype = Q.subgroupOf N at hh
    rwa [comap_map_eq_self_of_injective N.subtype_injective] at hh
  have hQN : Q ≤ N := hQM.trans hMN
  let eqMiddle : Qa ≃* QAt Γ middle := (eg.subgroupMap Qa).trans (MulEquiv.subgroupCongr hQa)
  let eqCore : pCore 2 N ≃* QAt Γ middle :=
    (MulEquiv.subgroupCongr hcoreNative).trans ((subgroupOfEquivOfLe hQN).trans
      ((Qa.equivMapOfInjective embedding ctx.embedding_injective).symm.trans eqMiddle))
  have hCorecard : Nat.card (pCore 2 N) = 32 := (Nat.card_congr eqCore.toEquiv).trans hQcard
  have hQaCard : Nat.card Qa = 32 := (Nat.card_congr eqMiddle.toEquiv).trans hQcard
  have hZQ : ZAt Γ middle ≤ QAt Γ middle := by
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact map_subtype_le _
  have hPhiCard : Nat.card (frattini (QAt Γ middle)) = 4 := by
    rw [ten_one_small_middle_core_frattini ctx middle hpath hsmall hmodel,
      Nat.card_congr (subgroupOfEquivOfLe hZQ).toEquiv]
    exact (sectionTenOpeningData ctx middle hpath).center_card
  have hfrattiniEight : Nat.card (pCore 2 N ⧸ frattini (pCore 2 N)) = 8 := by
    rw [card_frattini_quotient_of_equiv eqCore]
    have hc := (frattini (QAt Γ middle)).index_mul_card
    change Nat.card (QAt Γ middle ⧸ frattini (QAt Γ middle)) *
      Nat.card (frattini (QAt Γ middle)) = Nat.card (QAt Γ middle) at hc
    rw [hPhiCard,hQcard] at hc
    omega
  have hZaQ : Za ≤ Qa :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).trans (map_subtype_le _)
  have hQaTwo : IsPGroup 2 Qa := by
    change IsPGroup 2 (Γ.twoCoreAt cp.a)
    rw [Γ.twoCoreAt_def]
    exact pCore_isPGroup.map _
  have hZtwo : IsPGroup 2 Z := (hQaTwo.to_le hZaQ).map embedding
  have hZcard : Nat.card Z = 4 := by
    rw [card_map_of_injective ctx.embedding_injective]
    have hc := (sectionTenOpeningData ctx middle hpath).center_card
    rw [← hZa,card_map_of_injective eg.injective] at hc
    exact hc
  have hZne : Z ≠ ⊥ := by intro hz; rw [hz,card_bot] at hZcard; omega
  obtain ⟨hNsolv,hNchar⟩ := ctx.hypothesisTwo.hyp1.local_solvable_characteristicTwo
    N ⟨Z,hZne,hZtwo,rfl⟩ hSN
  let _ := hNsolv
  let SN : Sylow 2 N := S0.subtype hSN
  have hS0card : Nat.card S0 = 64 := by
    have hb : 1 < cp.length := by have := ctx.critical_length; change 1 < ctx.criticalPath.length; omega
    have hjoin := (nine_initial_edge_core_product ctx.toAmbientSectionNineContext hb).1
    have hcores := local_cores_le_edge_sylow ctx.sectionSeven Γ cp
    have hTedge : T = GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
      le_antisymm cp.S_le_edge_stabilizers (hjoin ▸ sup_le hcores.1 hcores.2)
    have hTcard : Nat.card T = 2 * Nat.card Qa := by
      exact (congrArg (fun U : Subgroup G => Nat.card U) hTedge).trans
        (nine_initial_edge_core_product ctx.toAmbientSectionNineContext hb).2
    have hScard : Nat.card S = Nat.card T := by
      rw [← ctx.map_S,card_map_of_injective ctx.embedding_injective]
    change Nat.card (S0 : Subgroup H) = 64
    rw [← hglobal,hScard,hTcard,hQaCard]
  have hSNcard : Nat.card SN = 2 * Nat.card (pCore 2 N) := by
    change Nat.card ((S0 : Subgroup H).subgroupOf N) = _
    rw [Nat.card_congr (subgroupOfEquivOfLe hSN).toEquiv,hS0card,hCorecard]
  have hNcard : Nat.card N ≤ 192 := by
    have hh := card_le_six_mul_of_characteristic_two_frattini_eight
      SN hNchar hfrattiniEight hSNcard
    rw [hCorecard] at hh
    exact hh
  have hMcard : Nat.card M = 192 := by
    have hMaCard : Nat.card Ma = Nat.card (GAt Γ middle) :=
      Nat.card_congr ((eg.subgroupMap Ma).trans (MulEquiv.subgroupCongr hMa)).toEquiv
    rw [card_map_of_injective ctx.embedding_injective,hMaCard]
    obtain ⟨projection,hsurj,hker⟩ := (sectionTenOpeningData ctx middle hpath).quotient_model
    have hc := projection.ker.index_mul_card
    rw [index_ker,projection.range_eq_top_of_surjective hsurj,card_top,hker,
      Nat.card_congr (subgroupOfEquivOfLe (show QAt Γ middle ≤ GAt Γ middle by
        change Γ.twoCoreAt middle ≤ Γ.stabilizer middle
        rw [Γ.twoCoreAt_def]
        exact map_subtype_le _)).toEquiv,hQcard,
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl SL2Two⟩] at hc
    exact hc.symm
  have hNM : N = M := (eq_of_le_of_card_ge hMN (by omega)).symm
  have hh := congrArg (Subgroup.map eh.toMonoidHom) hNM
  rw [map_equiv_normalizer_eq,hZtransport,hMtransport] at hh
  exact hh

end Stellmacher.SectionTen
