module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.MaximalPairs
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Native115
public import Mathlib.GroupTheory.PGroup

/-!
# Selecting the saturated source tuple

First select a maximal local pair. A Sylow of its second coordinate above
the beta-subgroup contains its two-core and is again in beta. Extending
that Sylow to H gives a source Sylow containing the same two-core. The
proved 2.3.9(3) then chooses the ambient Sylow overgroup and its central
involution. The relative core-normalizer argument puts this original
involution in the center of the saturated core.

Thus all saturation, Sylow alignment and marked-core premises needed by
the later component projections are constructed from the original Gamma
and normalizer-intersection hypotheses. No component model is used.

Source: Aschbacher--Smith 2.5.3(4), first paragraphs, printed p.552.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H : Subgroup G}

/-- The marked tuple and saturated pair of the original component-selection
argument exist, with the same ambient H and M and an actual central-core mark. -/
theorem exists_saturated_source_configuration
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G)) :
    ∃ U HU S T : Subgroup G, ∃ z : G,
      SourceTuple M H S T z ∧
      (U, HU) ∈ localPairsIn (Chapter1.He G) M H ∧
      U ≤ S ∧
      twoCore HU ≤ S ∧
      z ∈ (center (twoCore HU)).map (twoCore HU).subtype ∧
      ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
        HU ≤ normalizer (P : Set G) → P ≤ twoCore HU := by
  have hgamma : H ∈ gamma (Chapter1.He G) M :=
    hH.elim (fun hh => hh.1.1) (fun hh => hh.1)
  obtain ⟨U, HU, hpair, _hmax, hsat⟩ := exists_saturated_local_pair hgamma
  obtain ⟨P, hUP, hPb⟩ := beta_exists_sylow hpair.1.1 hpair.1.2.2.2.1
  obtain ⟨S, hPS, _hSb⟩ := beta_exists_sylow hPb ((map_subtype_le _).trans hpair.2)
  have hUS : U ≤ (S : Subgroup H).map H.subtype := hUP.trans hPS
  have hMe : M ∈ Chapter1.He G :=
    Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T₀ M hM hT₀M)
  obtain ⟨R, hRM, hSR, hZS, _hZC⟩ := lemma_2_3_9_3 T₀ hT₀M hunique hMe
    hH hpair S hUS
  have hRne : (R : Subgroup G) ≠ ⊥ := by
    intro hb
    exact hSR.not_ge (hb ▸ bot_le)
  let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot _).mpr hRne
  let : Nontrivial (center R) := R.isPGroup'.center_nontrivial
  have hd : 2 ∣ Nat.card (center R) :=
    ((R.isPGroup'.to_subgroup (center R)).card_eq_or_dvd.resolve_left
      (by have := Finite.one_lt_card (α := center R); omega))
  obtain ⟨z, hzo⟩ := exists_prime_orderOf_dvd_card' (G := center R) 2 hd
  let zG : G := ((z : R) : G)
  have hzR : zG ∈ (center (R : Subgroup G)).map (R : Subgroup G).subtype :=
    mem_map_of_mem _ z.property
  have hz2 : orderOf zG = 2 := by
    dsimp [zG]
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hzo]
  have hSi := (lemma_2_3_8_1 T₀ hT₀M hunique hgamma hpair S hUS).2.2.2
  have hRi : ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = (R : Subgroup G) := by
    refine ⟨R.subtype hRM, ?_⟩
    simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hRM]
  let d : SourceTuple M H ((S : Subgroup H).map H.subtype) (R : Subgroup G) zG :=
    ⟨hH, hSi, hRi, hZS, hSR, hz2, hzR⟩
  have hQS : twoCore HU ≤ (S : Subgroup H).map H.subtype :=
    (pCoreIn_le_sylow HU P).trans hPS
  have hzQ := SourceTuple.central_involution_mem_core_of_saturation d hG.evenCharacteristic
    hMe B hp hBH hHnorm hpair hQS hsat
  have hzcenter : zG ∈ (center (twoCore HU)).map (twoCore HU).subtype := by
    refine ⟨⟨zG, hzQ⟩, mem_center_iff.mpr ?_, rfl⟩
    intro q
    apply Subtype.ext
    change (q : G) * zG = zG * (q : G)
    exact congrArg (fun a : R => (a : G))
      (mem_center_iff.mp z.property ⟨q, hSR.le (hQS q.property)⟩)
  exact ⟨U, HU, _, _, zG, d, hpair, hUS, hQS, hzcenter, hsat⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
