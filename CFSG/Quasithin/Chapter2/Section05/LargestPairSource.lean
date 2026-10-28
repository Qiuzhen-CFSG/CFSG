module
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini
public import CFSG.Quasithin.Chapter2.Section01To03.Selection.Persistence
/-! # The original largest local pairs and their centers
Even characteristic gives characteristic two of every local-core normalizer.
A largest local base remains largest when extended to a Sylow in that
normalizer, so the original base is already Sylow there and in its original
local group. The center of every subgroup containing that base lies in the
base, by the self-centralizing two-core. This proves source 2.5.10 and removes
its characteristic-two callback from the later A₆ Frattini application.
Source: Aschbacher--Smith 2.5.10, printed p.557.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05
open A6Shadow.Frattini
variable {G:Type*} [Group G] [Finite G] {κ:GroupClass}
variable {M H U L:Subgroup G}

theorem local_pair_core_normalizer_mem_He
    (hG:IsSimpleQTKE κ G) (T:Sylow 2 G)
    (hM:IsMaximalTwoLocal M) (hTM:(T:Subgroup G)≤M)
    (hp:(U,L)∈localPairsIn (Chapter1.He G) M H) :
    normalizer (twoCore L:Set G)∈Chapter1.He G :=
  (lemma_2_3_8_2 hG.evenCharacteristic
    (Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)) hp).2.2

private theorem largest_base_sylow_of_local_pair
    (hp:(U,L)∈localPairs (Chapter1.He G) M)
    (hmax:∀W∈localBases (Chapter1.He G) M,Nat.card W≤Nat.card U) :
    ∃P:Sylow 2 L,(P:Subgroup L).map L.subtype=U := by
  obtain ⟨P,hUP,hPb⟩:=beta_exists_sylow hp.1 hp.2.2.2.1
  have hp':((P:Subgroup L).map L.subtype,L)∈localPairs (Chapter1.He G) M:=
    ⟨hPb,hp.2.1,hp.2.2.1,map_subtype_le _,hp.2.2.2.2⟩
  exact ⟨P,(eq_of_le_of_card_ge hUP (hmax _ ⟨L,hp'⟩)).symm⟩

/-- Both literal Sylow conclusions of 2.5.10(2). -/
theorem largest_pair_sylows
    (hG:IsSimpleQTKE κ G) (T:Sylow 2 G)
    (hM:IsMaximalTwoLocal M) (hTM:(T:Subgroup G)≤M)
    (hp:(U,L)∈largestLocalPairs M H) :
    normalizer (twoCore L:Set G)∈Chapter1.He G ∧
      (∃P:Sylow 2 (normalizer (twoCore L:Set G)),
        (P:Subgroup (normalizer (twoCore L:Set G))).map
          (normalizer (twoCore L:Set G)).subtype=U) ∧
      ∃P:Sylow 2 L,(P:Subgroup L).map L.subtype=U := by
  have hN:=local_pair_core_normalizer_mem_He hG T hM hTM hp.1
  have hLN:L≤normalizer (twoCore L:Set G):=le_normalizer_twoCore L
  have hQ:twoCore (normalizer (twoCore L:Set G))≠⊥:=by
    intro he
    exact hp.1.1.2.2.1 (bot_unique (he ▸
      le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L) (twoCore L).le_normalizer le_rfl))
  have hpair:(U,normalizer (twoCore L:Set G))∈localPairs (Chapter1.He G) M:=
    ⟨hp.1.1.1,hN,hQ,hp.1.1.2.2.2.1.trans hLN,
      fun hn=>hp.1.1.2.2.2.2 (hLN.trans hn)⟩
  exact ⟨hN,largest_base_sylow_of_local_pair hpair hp.2,
    largest_base_sylow_of_local_pair hp.1.1 hp.2⟩

/-- The center clause of 2.5.10(2), before specializing to the marked z. -/
theorem largest_pair_center_le
    (hG:IsSimpleQTKE κ G) (T:Sylow 2 G)
    (hM:IsMaximalTwoLocal M) (hTM:(T:Subgroup G)≤M)
    (hp:(U,L)∈largestLocalPairs M H) {Y:Subgroup G} (hUY:U≤Y) :
    centerIn Y≤U := by
  obtain ⟨hN,⟨P,hP⟩,_⟩:=largest_pair_sylows hG T hM hTM hp
  let N:=normalizer (twoCore L:Set G)
  have hQU:twoCore N≤U:=hP ▸ pCoreIn_le_sylow N P
  have hQ₀U:twoCore L≤U:=by
    obtain ⟨R,hR⟩:=(largest_pair_sylows hG T hM hTM hp).2.2
    exact hR ▸ pCoreIn_le_sylow L R
  intro a ha
  have haN:a∈N:=centralizer_le_normalizer (twoCore L:Set G)
    (fun b hb=>ha.2 b (hUY (hQ₀U hb)))
  exact hQU (hN ⟨haN,fun b hb=>ha.2 b (hUY (hQU hb))⟩)

end CFSG.Quasithin.Chapter2.Section05

namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini
variable {G:Type*} [Group G] [Finite G] {κ:GroupClass}

/-- The original even-characteristic setup supplies the entire 2.5.10 input. -/
theorem EarlierSetup.sourceNormalizerCondition (d:EarlierSetup κ G) :
    SourceNormalizerCondition d := by
  intro U L hp
  exact (Section05.largest_pair_sylows d.simpleQTKE d.T d.maximalM d.t_le_m hp).2.1

/-- The literal later Frattini application with source 2.5.10 discharged.
The distinct earlier four-group correspondence and centralizer clauses
remain explicit, as required by the section assembly. -/
theorem source_frattini_and_involutions_of_pair_correspondence
    (d:EarlierSetup κ G)
    (hcentral:∀g:G,g⁻¹*d.z*g∈d.S→
      (centralizer ({d.t}:Set G)⊓centralizer ({g⁻¹*d.z*g}:Set G))∈Chapter1.He G)
    (hcor:d.EarlierPairCorrespondence) :
    frattini d.SC≠⊥ ∧ d.x⁻¹*d.t*d.x=d.zK ∧ d.z=d.t*d.zK := by
  apply source_frattini_and_involutions d hcentral hcor
  intro U L hp
  exact Section05.local_pair_core_normalizer_mem_He d.simpleQTKE d.T d.maximalM d.t_le_m hp
end CFSG.Quasithin.Chapter2.A6Shadow.Frattini
