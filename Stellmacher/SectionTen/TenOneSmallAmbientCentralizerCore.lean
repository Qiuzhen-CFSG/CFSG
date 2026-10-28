module

public import Stellmacher.SectionTen.TenOneSmallMiddleCoreClassTwo
public import Stellmacher.SectionNine.NineTwoAmbientSetup
public import Stellmacher.CharacteristicTwoNormal
public import Theory.GroupTheory.CharacteristicTwoCentralLayerSylow
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# The ambient middle-center centralizer has the middle two-core

In the small branch of Stellmacher (10.1), the two-core of the full ambient
centralizer C_H(Zmiddle) is exactly the embedded middle two-core. Both
Zmiddle and Qmiddle are the images of the actual graph subgroups under the
supplied embedding. The global local-subgroup hypotheses stay on H; the
embedded graph group need not equal H.

The proved Section Nine orientation gives S=S₀. At the initial vertex,
N_H(Zinitial) therefore contains the exact distinguished ambient Sylow S₀,
so Hypothesis One makes this normalizer solvable of characteristic two.
Its normal subgroup C_H(Zinitial) inherits characteristic two. Restricting
S₀ through that normal subgroup identifies a centralizer Sylow with the
embedded initial core, using the (7.4) edge-centralizer equality. The central
initial center is a two-subgroup of this centralizer. The middle class-two
bound transports back along the opening conjugator, putting the initial
Sylow commutator in that center. The central-layer Sylow-core theorem now
identifies the centralizer core. Ambient conjugation transports the entire
identity to the middle vertex, including the full ambient centralizer.

This proves N₀=Qmiddle in the paragraph before identity (7) in Stellmacher
(10.1)(a3), printed p.61 of `refs/files/stellmacher-n-group.pdf`. The subsequent
normalizer identities and involution-fusion argument are separate results.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open Subgroup
universe u

private theorem characteristic_two_transport
    {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  have hcore := pCore_map_iso 2 e
  intro h hh
  obtain ⟨g, rfl⟩ := e.surjective h
  rw [← hcore]
  apply mem_map_of_mem
  apply hchar
  rw [mem_centralizer_iff]
  intro y hy
  apply e.injective
  have hyH : e y ∈ pCore 2 H := by
    rw [← hcore]
    exact mem_map_of_mem e.toMonoidHom hy
  simpa only [map_mul] using mem_centralizer_iff.mp hh (e y) hyH

private theorem centralizer_core_eq_at_fixed_sylow
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (hyp : HypothesisOne H S0) (Z Q : Subgroup H)
    (hZp : IsPGroup 2 Z) (hZne : Z ≠ ⊥)
    (hSN : (S0 : Subgroup H) ≤ normalizer (Z : Set H))
    (hSC : (S0 : Subgroup H) ⊓ centralizer (Z : Set H) = Q)
    (hZQ : Z ≤ Q) (hcomm : ⁅Q,Q⁆ ≤ Z) :
    twoCoreIn (centralizer (Z : Set H)) = Q := by
  let N := normalizer (Z : Set H)
  let C := centralizer (Z : Set H)
  let CN := C.subgroupOf N
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hNlocal : IsTwoLocal N := ⟨Z,hZne,hZp,rfl⟩
  obtain ⟨hNsolv,hNchar⟩ := hyp.local_solvable_characteristicTwo N hNlocal hSN
  let e : CN ≃* C := subgroupOfEquivOfLe hCN
  have hcharCN := characteristicTwo_normal_subgroup hNsolv hNchar CN
  have hCchar : IsCharacteristicTwoType C := characteristic_two_transport e hcharCN
  let SN : Sylow 2 N := S0.subtype hSN
  obtain ⟨PCN,hPCN⟩ := SN.exists_sylow_map_eq_inf_of_normal CN
  let PC : Sylow 2 C := PCN.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcomp : C.subtype.comp e.toMonoidHom = N.subtype.comp CN.subtype := by
    ext x
    rfl
  have hPC : (PC : Subgroup C).map C.subtype = Q := by
    change ((PCN : Subgroup CN).map e.toMonoidHom).map C.subtype = Q
    rw [map_map,hcomp,← map_map,hPCN,map_inf _ _ _ N.subtype_injective]
    change ((S0 : Subgroup H).subgroupOf N).map N.subtype ⊓
      (C.subgroupOf N).map N.subtype = Q
    rw [map_subgroupOf_eq_of_le hSN,map_subgroupOf_eq_of_le hCN]
    exact hSC
  have hQC : Q ≤ C := hPC ▸ map_subtype_le (PC : Subgroup C)
  have hZC : Z ≤ C := hZQ.trans hQC
  let ZC := Z.subgroupOf C
  let _ : ZC.Normal := normal_subgroupOf_of_le_normalizer (Subgroup.centralizer_le_normalizer _)
  have hZcentral : ZC ≤ center C := by
    intro z hz
    rw [mem_center_iff]
    intro c
    apply Subtype.ext
    exact (mem_centralizer_iff.mp c.property z hz).symm
  have hZcore : ZC ≤ pCore 2 C := le_sSup ⟨inferInstance,hZp.comap_subtype⟩
  have hcommPC : ⁅(PC : Subgroup C),(PC : Subgroup C)⁆ ≤ ZC := by
    intro c hc
    apply hcomm
    rw [← hPC,← map_commutator]
    exact mem_map_of_mem C.subtype hc
  have heq := sylow_two_eq_pCore_of_commutator_le_central_layer
    PC ZC hZcore hZcentral hCchar hcommPC
  change (pCore 2 C).map C.subtype = Q
  rw [← heq]
  exact hPC

private theorem centralizer_map_equiv
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

/-- The full ambient centralizer of the embedded middle center has exactly
the embedded middle two-core. -/
public theorem ten_one_small_ambient_center_centralizer_core
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    twoCoreIn (centralizer ((ZAt ctx.Γ middle).map embedding : Set H)) =
      (QAt ctx.Γ middle).map embedding := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Za := ZAt Γ cp.a
  let Qa := QAt Γ cp.a
  let Z := Za.map embedding
  let Q := Qa.map embedding
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
  have htransport (D : Subgroup G) :
      (D.map embedding).map eh.toMonoidHom = (D.map eg.toMonoidHom).map embedding := by
    rw [map_map,map_map]
    congr 1
    ext x
    simp [eh,eg]
  have hZtransport : Z.map eh.toMonoidHom = (ZAt Γ middle).map embedding := by
    rw [htransport,hZa]
  have hQtransport : Q.map eh.toMonoidHom = (QAt Γ middle).map embedding := by
    rw [htransport,hQa]
  have hclassTwo : ⁅Qa,Qa⁆ ≤ Za := by
    apply (map_le_map_iff_of_injective (f := eg.toMonoidHom) eg.injective).mp
    rw [map_commutator,hQa,hZa]
    exact ten_one_small_middle_core_commutator_le_center ctx middle hpath hsmall hmodel
  have hcomm : ⁅Q,Q⁆ ≤ Z := by
    rw [← map_commutator]
    exact map_mono hclassTwo
  have hZaQ : Za ≤ Qa :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).trans (map_subtype_le _)
  have hZQ : Z ≤ Q := map_mono hZaQ
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
  have hZne : Z ≠ ⊥ := by
    intro hz
    rw [hz,card_bot] at hZcard
    omega
  have hTZ : T ≤ normalizer (Za : Set G) :=
    (edge_sylow_data ctx.sectionSeven Γ cp).1.1.trans (stabilizer_le_normalizer_z Γ cp.a)
  have hSN : (S0 : Subgroup H) ≤ normalizer (Z : Set H) := by
    rw [← hglobal,← ctx.map_S]
    exact (map_mono hTZ).trans (Za.le_normalizer_map embedding)
  have hedge : T ⊓ centralizer (Za : Set G) = Qa :=
    (lemma_seven_four ctx.sectionSeven Γ cp).edge_centralizer
  have hSC : (S0 : Subgroup H) ⊓ centralizer (Z : Set H) = Q := by
    rw [← hglobal,← ctx.map_S]
    apply le_antisymm
    · rintro x ⟨⟨t,ht,rfl⟩,hc⟩
      apply mem_map_of_mem
      apply hedge.le
      refine ⟨ht,?_⟩
      change t ∈ centralizer (Za : Set G)
      rw [mem_centralizer_iff]
      intro z hz
      apply ctx.embedding_injective
      simpa only [map_mul] using mem_centralizer_iff.mp hc (embedding z) (mem_map_of_mem embedding hz)
    · rintro x ⟨q,hq,rfl⟩
      have hqTC := hedge.ge hq
      refine ⟨mem_map_of_mem embedding hqTC.1,?_⟩
      change embedding q ∈ centralizer (Z : Set H)
      rw [mem_centralizer_iff]
      rintro _ ⟨z,hz,rfl⟩
      simpa only [map_mul] using congrArg embedding (mem_centralizer_iff.mp hqTC.2 z hz)
  have hcore : twoCoreIn (centralizer (Z : Set H)) = Q :=
    centralizer_core_eq_at_fixed_sylow S0 ctx.hypothesisTwo.hyp1 Z Q
      hZtwo hZne hSN hSC hZQ hcomm
  rw [← hZtransport,← centralizer_map_equiv,twoCoreIn_map_equiv,hcore,hQtransport]

end Stellmacher.SectionTen
