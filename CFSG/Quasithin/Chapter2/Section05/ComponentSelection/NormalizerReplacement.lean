module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.MaximalPairBase

/-!
# Source normalizer replacement preserving both starred families

A two-subgroup of the saturated core normalized by the chosen local pair and
original Sylow can be adjoined to the literal normalizer-intersection family.
The old local pair and Sylow survive, and saturation places the old normal
core and every member of that family in the replacement. Thus the source
Gamma conditions and both starred conditions survive on the same data.

Source: Aschbacher--Smith 2.5.3(4), printed pp.552--553.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The replacement retains the literal finite normalizer family and both stars. -/
theorem normalizer_replacement_preserves_source
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hbig : H ∈ gammaStar (Chapter1.He G) M →
      ∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (R : Subgroup H) (hRQ : R ≤ (twoCore HU).subgroupOf H)
    (hUR : HU.subgroupOf H ≤ normalizer (R : Set H))
    (hSR : (S : Subgroup H) ≤ normalizer (R : Set H)) :
    let X := (normalizer (R : Set H)).map H.subtype
    ∃ B' : Fin (n + 1) → Subgroup G,
      X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) ∧
      HU ≤ X ∧ (S : Subgroup H).map H.subtype ≤ X ∧
      (∀ i, IsPGroup 2 (B' i)) ∧ (∀ i, B' i ≤ X) ∧
      X = ⨅ i, normalizer (B' i : Set G) := by
  let W := R.map H.subtype
  let X := (normalizer (R : Set H)).map H.subtype
  have hWH : W ≤ H := map_subtype_le R
  have hXeq : X = H ⊓ normalizer (W : Set G) := by
    have hWR : W.subgroupOf H = R :=
      comap_map_eq_self_of_injective H.subtype_injective R
    change (normalizer (R : Set H)).map H.subtype = H ⊓ normalizer (W : Set G)
    rw [← hWR, ← subgroupOf_normalizer_eq hWH, subgroupOf_map_subtype, inf_comm]
  have hHUX : HU ≤ X := by
    intro a ha
    exact ⟨⟨a, hpair.2 ha⟩, hUR ha, rfl⟩
  have hSX : (S : Subgroup H).map H.subtype ≤ X := map_mono hSR
  have hQHU : twoCore HU ≤ HU := pCoreIn_le 2 HU
  have hcoreX : twoCore X ≠ ⊥ := by
    have hQH : twoCore H ≤ twoCore HU := hsat _ (pCoreIn_le 2 H)
      (isPGroup_pCoreIn 2 H) (hpair.2.trans (le_normalizer_twoCore H))
    have hcore : twoCore H ≤ twoCore X := le_pCoreIn_of_normalizes
      (isPGroup_pCoreIn 2 H) (hQH.trans (hQHU.trans hHUX))
      ((map_subtype_le _).trans (le_normalizer_twoCore H))
    intro hb
    have hg : H ∈ gamma (Chapter1.He G) M := hH.elim (fun h => h.1.1) (fun h => h.1)
    exact hg.1 (bot_unique (hb ▸ hcore))
  obtain ⟨hX, _hSyl, _hSylM, hstar, hmax⟩ := replacement_preserves_stars
    hH hpair hbig S hUS hHUX hSX hcoreX
  have hBX : ∀ i, B i ≤ X := by
    intro i
    have hnorm : H ≤ normalizer (B i : Set G) := hHnorm.le.trans (iInf_le _ i)
    have hBcore := hsat (B i) (hBH i) (hp i) (hpair.2.trans hnorm)
    exact hBcore.trans (hQHU.trans hHUX)
  have hWp : IsPGroup 2 W :=
    (((isPGroup_pCoreIn 2 HU).comap_subtype).to_le hRQ).map H.subtype
  have hWX : W ≤ X := map_mono R.le_normalizer
  change ∃ B' : Fin (n + 1) → Subgroup G, _
  refine ⟨Fin.cases W B, hX, hstar, hmax, hHUX, hSX,
    fun i => Fin.cases hWp hp i, fun i => Fin.cases hWX hBX i, ?_⟩
  change X = ⨅ i, normalizer ((Fin.cases W B i : Subgroup G) : Set G)
  rw [hXeq, hHnorm]
  apply le_antisymm
  · exact le_iInf fun i => Fin.cases inf_le_right
      (fun j => inf_le_left.trans (iInf_le _ j)) i
  · exact le_inf (le_iInf fun i => iInf_le _ i.succ) (iInf_le _ 0)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
