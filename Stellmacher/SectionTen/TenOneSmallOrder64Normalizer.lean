module
public import Stellmacher.SectionTen.TenOneSmallAmbientCentralizerCore
public import Stellmacher.SectionTen.TenOneSmallMiddleCoreFrattini
public import Stellmacher.SectionTen.TenOneSmallMiddleCoreCard
public import Stellmacher.SectionTen.TenOneSmallCentralizerCharacteristic
public import Theory.GroupTheory.PGroup.UniqueElementaryQuotientKernel
public import Theory.GroupTheory.CharacteristicTwoCoreActionCardBound
public import Theory.GroupTheory.PCoreNormalizedOvergroup
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# The middle-center normalizer when the middle core has order 64

In the small case of Stellmacher (10.1), if the middle two-core has order
64, the ambient normalizer of its central layer is exactly the embedded
middle stabilizer. The original ambient context, critical path and first
quotient model are retained.

Work first at the initial vertex, whose stabilizer contains the fixed
ambient Sylow subgroup. The center-centralizer core equality makes its
core normal in the center normalizer, and the local-core overgroup theorem
identifies that normalizer's two-core. Exact conjugation and subtype
equivalences transport this core to the middle one.

The middle centralizer W* has order sixteen and index four, and the native
elementary-subgroup bound makes W* characteristic. The middle core has
Frattini subgroup equal to its center of order four. The general quotient
kernel theorem therefore gives a two-group kernel for the automorphism
action on Q/W*. This is an elementary group of order four, with automorphism
group of order six. Applied to the intrinsic core action, the resulting
cardinal bound makes the ambient normalizer have order at most 384. Its
contained stabilizer already has that order from the SL₂(2) quotient.
Equality follows and is conjugated back to the middle vertex.

Source: Stellmacher, “On the N-group theorem”, (10.1)(a3), printed p.61,
the order-64 branch of assertion (7), in `refs/files/stellmacher-n-group.pdf`.
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

private theorem centralizer_map_equiv_order64
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

variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

/-- In the order-64 small branch, the ambient normalizer of the middle
central layer is precisely the embedded middle stabilizer. -/
public theorem ten_one_small_order64_center_normalizer
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hQcard : Nat.card (QAt ctx.Γ middle) = 64)
    :
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
    rw [← twoCoreIn_map_equiv,centralizer_map_equiv_order64,hZtransport,hQtransport]
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
    exact mapped_pCore_eq_of_normalized_local_pCore S0 M N hSM hMN (by
      change N ≤ normalizer (twoCoreIn M : Set H)
      rw [hMcore]
      exact hNQ)
  have hcoreNative : pCore 2 N = Q.subgroupOf N := by
    have hh := congrArg (comap N.subtype) hNcore
    change ((pCore 2 N).map N.subtype).comap N.subtype = Q.subgroupOf N at hh
    rwa [comap_map_eq_self_of_injective N.subtype_injective] at hh
  have hQN : Q ≤ N := hQM.trans hMN
  let eqMiddle : Qa ≃* QAt Γ middle := (eg.subgroupMap Qa).trans (MulEquiv.subgroupCongr hQa)
  let eqCore : pCore 2 N ≃* QAt Γ middle :=
    (MulEquiv.subgroupCongr hcoreNative).trans ((subgroupOfEquivOfLe hQN).trans
      ((Qa.equivMapOfInjective embedding ctx.embedding_injective).symm.trans eqMiddle))
  have hCorecard : Nat.card (pCore 2 N) = 64 := (Nat.card_congr eqCore.toEquiv).trans hQcard
  have hZQ : ZAt Γ middle ≤ QAt Γ middle := by
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact map_subtype_le _
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
  obtain ⟨_,hNchar⟩ := ctx.hypothesisTwo.hyp1.local_solvable_characteristicTwo
    N ⟨Z,hZne,hZtwo,rfl⟩ hSN
  let W := QAt Γ middle ⊓ Subgroup.centralizer
    ((NeighborhoodQIntersection Γ (Neighborhood Γ middle) ⊓
      GeneratedNeighborhoodV Γ middle : Subgroup G) : Set G)
  let U := W.subgroupOf (QAt Γ middle)
  obtain ⟨_,hWelementary,_,hWD,_⟩ :=
    ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel
  let _ : IsElementaryAbelian 2 W := hWelementary
  let _ : IsElementaryAbelian 2 U :=
    IsElementaryAbelian.subgroupOf (inf_le_left : W ≤ QAt Γ middle)
  have hQtwo : IsPGroup 2 (QAt Γ middle) := by
    change IsPGroup 2 (Γ.twoCoreAt middle)
    rw [Γ.twoCoreAt_def]
    exact pCore_isPGroup.map _
  have hcenter : center (QAt Γ middle) = (ZAt Γ middle).subgroupOf (QAt Γ middle) := by
    apply map_injective (f := (QAt Γ middle).subtype) (QAt Γ middle).subtype_injective
    rw [map_subgroupOf_eq_of_le hZQ]
    exact ten_one_small_middle_core_center ctx middle hpath hsmall hmodel
  have hZW : ZAt Γ middle ≤ W := by
    rw [← hWD]
    exact inf_le_left
  have hZU : center (QAt Γ middle) ≤ U := by
    rw [hcenter]
    intro z hz
    exact hZW hz
  have hPhi : frattini (QAt Γ middle) = center (QAt Γ middle) := by
    rw [ten_one_small_middle_core_frattini ctx middle hpath hsmall hmodel, hcenter]
  have hZmiddlecard : Nat.card (center (QAt Γ middle)) = 4 := by
    rw [hcenter, Nat.card_congr (subgroupOfEquivOfLe hZQ).toEquiv]
    exact (sectionTenOpeningData ctx middle hpath).center_card
  have hWcard : Nat.card W = 16 := by
    have hh := ten_one_small_middle_core_card ctx middle hpath hsmall hmodel
    change Nat.card (QAt Γ middle) = 4 * Nat.card W at hh
    rw [hQcard] at hh
    omega
  let _ : U.Characteristic := ten_one_small_centralizer_characteristic
    ctx middle hpath hsmall hmodel hWcard
  have hUcard : Nat.card U = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : W ≤ QAt Γ middle)).toEquiv]
    exact hWcard
  have hUindex : U.index = 4 := by
    have hh := U.index_mul_card
    rw [hUcard, hQcard] at hh
    omega
  have hkernel := isPGroup_quotientAut_kernel_of_elementary_outside_bound
    hQtwo U hZU hPhi hZmiddlecard hUindex (by
      intro X hX hnot
      let _ : IsElementaryAbelian 2 X := hX
      exact ten_one_small_elementary_escape_card_bound
        ctx middle hpath hsmall hmodel X hnot)
  let _ : IsElementaryAbelian 2 (QAt Γ middle ⧸ U) :=
    elementary_quotient_of_frattini_le hQtwo U (by rw [hPhi]; exact hZU)
  let _ : Nontrivial (QAt Γ middle ⧸ U) := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < U.index
    rw [hUindex]
    decide)
  let _ : IsKleinFour (QAt Γ middle ⧸ U) := {
    card_four := hUindex
    exponent_two := IsElementaryAbelian.exponent_eq_prime (p:=2) (G:=QAt Γ middle ⧸ U) }
  have hNcard : Nat.card N ≤ 384 := by
    have hh := card_le_card_mul_core_of_characteristic_two_automorphism_hom
      hNchar eqCore (quotientAut U) hkernel
    rw [IsKleinFour.card_mulAut, hCorecard] at hh
    exact hh
  have hMcard : Nat.card M = 384 := by
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
