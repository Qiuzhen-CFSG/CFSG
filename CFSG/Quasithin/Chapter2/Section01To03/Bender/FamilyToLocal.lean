module

public import CFSG.Quasithin.Chapter2.Defs
public import CFSG.Quasithin.Chapter1.Section01Overgroups
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.FusionLocalControl

/-!
# The characteristic-two family connection in the Bender branch

Every literal Alperin–Goldschmidt family member contains the center of the
ambient Sylow subgroup. Since the family member is nontrivial, that Sylow
subgroup and its center are nontrivial. Lemma 1.1.4(3), using only even
characteristic, therefore puts the family member in S₂e. Empty δ now gives
the normalizer containment required by the complete local-control theorem.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Lemma 2.2.3
and the input reduction in Theorem 2.2.5, printed pp.520–521.
This does not assert Bender recognition.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.BenderFusion

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The complete source Lemma 2.2.3; no additional even-order hypothesis. -/
theorem family_mem_S2e (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    {D : Subgroup G} (hD : alperinGoldschmidtFamily T D) :
    D ∈ Chapter1.S2e G := by
  have hTne : (T : Subgroup G) ≠ ⊥ := fun he =>
    hD.ne_bot (bot_unique (he ▸ hD.le_sylow))
  have : Nontrivial (T : Subgroup G) :=
    ((T : Subgroup G).nontrivial_iff_ne_bot).mpr hTne
  have hZne : (center (T : Subgroup G)).map (T : Subgroup G).subtype ≠ ⊥ :=
    fun he => (ne_of_gt T.isPGroup'.bot_lt_center)
      ((map_eq_bot_iff_of_injective _ Subtype.val_injective).mp he)
  apply Chapter1.lemma_1_1_4_3 T hE hD.ne_bot
    (T.isPGroup'.of_injective (inclusion hD.le_sylow) (inclusion_injective _))
  rwa [inf_eq_left.mpr hD.center_le]

/-- Empty δ supplies the genuine family-normalizer premise; the family is
the literal Definition 2.2.1 family, and the local class is the actual He. -/
theorem family_normalizer_le_of_delta_empty (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T) {M : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hdelta : delta (Chapter1.He G) M = ∅)
    {D : Subgroup G} (hD : alperinGoldschmidtFamily T D) :
    normalizer (D : Set G) ≤ M := by
  by_contra hnot
  have hDe := family_mem_S2e T hE hD
  have hmem : D ∈ delta (Chapter1.He G) M :=
    ⟨⟨hDe.1, hDe.2.1⟩, hDe.2.2, hD.le_sylow.trans hTM, hnot⟩
  simp only [hdelta, Set.mem_empty_iff_false] at hmem

/-- The empty-δ source branch constructs all local-control witnesses without
assuming any fusion, selected-subgroup, or unique-fixed-coset data. -/
theorem source_local_control_of_delta_empty {K : GroupClass.{u}}
    (hG : IsSimpleQTKE K G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      (T : Subgroup G) ≤ N → N = M)
    (hdelta : delta (Chapter1.He G) M = ∅) :
    HasCharacteristicTwo M ∧ Nonempty (LocalControlWitness T M) :=
  source_local_control hG T M hM hTM hunique
    (fun _ hD => family_normalizer_le_of_delta_empty T
      (hG.evenCharacteristic T) hTM hdelta hD)

end CFSG.Quasithin.Chapter2.BenderFusion
