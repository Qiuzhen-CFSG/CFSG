module

public import CFSG.Quasithin.MainConverse.MathieuLocal.M24Even.LocalData
public import Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.CentralInvolutions
public import Theory.Mathieu.M24.Properties.Order
public import Theory.GroupTheory.SylowLocalCentralizerCriterion
public import CFSG.Quasithin.Defs

/-!
# Even characteristic of the concrete Mathieu group M₂₄

The certified subgroup of order 1024 is Sylow in the actual M₂₄ carrier.
Its central involutions all have the same fixed octad, by the checked
enumeration and pointwise commutation tests. Each involution centralizer
therefore lies in the octad stabilizer and contains the full Sylow subgroup.
It inherits the stabilizer's self-centralizing intrinsic two-core property.

The Sylow-center criterion now proves characteristic two for every two-local
containing this Sylow subgroup. Sylow conjugacy gives the unconditional
`m24_evenCharacteristic`. The earlier conditional route through a normal
elementary catalogue and its 22 normalizers is retained as a separate API;
the center argument discharges condition E independently of that catalogue.

Source: Aschbacher–Smith, Theorem 0.1.2(5), printed pp.3–4, repeated as
Theorem 0.1.1(5) on pp.481–482. All carriers are subgroups of the original
Witt-design automorphism group. Normality and two-cores are intrinsic.
-/

namespace CFSG.Quasithin.MainConverse.M24Even
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry

public theorem candidate_hasCharacteristicTwo {M : Subgroup M24}
    (hM : IsCandidateLocal M) : HasCharacteristicTwo M := by
  rcases hM with ⟨O, rfl⟩ | ⟨k, rfl⟩
  · exact LinearFourCore.octad_core_selfCentralizing O
  · exact EvenCandidates.localGroup_core_selfCentralizing k

/-- An alternative route to condition E from exhaustive normal elementary
and normalizer calculations, retaining both explicit premises. -/
public theorem evenCharacteristic_of_catalogue_and_normalizers
    (hcatalogue : NormalElementaryCatalogue) (hnormalizers : NormalizerCases) :
    IsEvenCharacteristic M24 := by
  have hind : ¬ 2 ∣ SylowNormalizer.candidate.index := by
    have hc := SylowNormalizer.candidate.card_mul_index
    rw [SylowNormalizer.candidate_card, m24_order] at hc
    have he : SylowNormalizer.candidate.index = 239085 := by omega
    rw [he]
    decide
  let T : Sylow 2 M24 :=
    (IsPGroup.of_card (p := 2) (n := 10) SylowNormalizer.candidate_card).toSylow hind
  apply IsEvenCharacteristicAt.all (T := T)
  intro M hM hTM
  obtain ⟨R, hR, hn, he, hMR⟩ :=
    Theory.GroupTheory.exists_normal_elementary_normalizer_of_sylow_le T hM hTM
  obtain ⟨i, hi⟩ := hcatalogue R hR hn he
  have hMi : M = EvenCatalogue.localGroup i := by
    rw [hMR, hi]
    rfl
  apply candidate_hasCharacteristicTwo
  rw [hMi] at hM ⊢
  exact hnormalizers i hM

end CFSG.Quasithin.MainConverse.M24Even

namespace CFSG.Quasithin.MainConverse
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry

/-- Condition (E) for the actual Witt-design automorphism group M₂₄. -/
public theorem m24_evenCharacteristic : IsEvenCharacteristic M24 := by
  have hind : ¬ 2 ∣ SylowNormalizer.candidate.index := by
    have hc := SylowNormalizer.candidate.card_mul_index
    rw [SylowNormalizer.candidate_card, m24_order] at hc
    have he : SylowNormalizer.candidate.index = 239085 := by omega
    rw [he]
    decide
  let T : Sylow 2 M24 :=
    (IsPGroup.of_card (p := 2) (n := 10) SylowNormalizer.candidate_card).toSylow hind
  have hc : ∀ z : T, z ∈ center T → orderOf z = 2 →
      HasCharacteristicTwo (centralizer ({(z : M24)} : Set M24)) := by
    intro z hz hz2
    let C := centralizer ({(z : M24)} : Set M24)
    let P := octadStabilizer SylowNormalizer.centralOctad
    have hTC : (T : Subgroup M24) ≤ C := by
      intro t ht
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp hz ⟨t, ht⟩))
    have hCP : C ≤ P := SylowNormalizer.central_involution_centralizer_le_octad z hz hz2
    have hTP : (T : Subgroup M24) ≤ P := hTC.trans hCP
    have hC : centralizer (pCore 2 (C.subgroupOf P) : Set (C.subgroupOf P)) ≤
        pCore 2 (C.subgroupOf P) :=
      centralizer_pCore_le_of_sylow_le (T.subtype hTP) (C.subgroupOf P)
        (fun x hx => hTC hx)
        (LinearFourCore.octad_core_selfCentralizing SylowNormalizer.centralOctad)
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (subgroupOfEquivOfLe hCP)).mp hC
  apply IsEvenCharacteristicAt.all (T := T)
  intro M hM hTM
  obtain ⟨Q, hne, hp, rfl⟩ := hM.1
  exact normalizer_core_selfCentralizing_of_sylow_centralizers T Q hp hne hTM hc

end CFSG.Quasithin.MainConverse
