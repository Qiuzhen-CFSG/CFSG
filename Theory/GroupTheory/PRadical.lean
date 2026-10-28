module

public import Theory.PGroupCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Radical p-subgroups

A nontrivial p-subgroup is radical if it is the p-core of its normalizer.
Every nontrivial p-subgroup lies in a radical subgroup whose normalizer
contains its normalizer. Choose a maximal normalizer-preserving enlargement;
passing to the p-core of its normalizer forces radicality.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), C.1.1 and C.1.2(1–2), pp. 121–122.
-/

@[expose] public section

namespace Subgroup

variable {G : Type*} [Group G] {p : ℕ}

/-- Nontrivial radical p-subgroups, with the p-core mapped to the ambient group. -/
def IsPRadical (p : ℕ) (R : Subgroup G) : Prop :=
  R ≠ ⊥ ∧ (pCore p (normalizer (R : Set G))).map (normalizer (R : Set G)).subtype = R

/-- A radical subgroup is a p-group. -/
theorem IsPRadical.isPGroup {R : Subgroup G} (hR : IsPRadical p R) :
    IsPGroup p R := by
  rw [← hR.2]
  exact pCore_isPGroup.map _

/-- Every p-subgroup is contained in the ambient image of the p-core of its normalizer. -/
theorem le_map_pCore_normalizer {R : Subgroup G} (hR : IsPGroup p R) :
    R ≤ (pCore p (normalizer (R : Set G))).map (normalizer (R : Set G)).subtype := by
  have hle : R.subgroupOf (normalizer (R : Set G)) ≤
      pCore p (normalizer (R : Set G)) :=
    le_sSup ⟨inferInstance, hR.of_equiv (subgroupOfEquivOfLe R.le_normalizer).symm⟩
  simpa only [map_subgroupOf_eq_of_le R.le_normalizer] using
    (map_mono (f := (normalizer (R : Set G)).subtype) hle)

/-- Every nontrivial Sylow subgroup is radical. -/
theorem isPRadical_sylow (S : Sylow p G) (hS : (S : Subgroup G) ≠ ⊥) :
    IsPRadical p (S : Subgroup G) := by
  exact ⟨hS, S.is_maximal' (pCore_isPGroup.map _)
    (le_map_pCore_normalizer S.isPGroup')⟩

/-- Normalizer-preserving radical enlargement of a nontrivial p-subgroup. -/
theorem exists_isPRadical_of_isPGroup [Finite G] (R : Subgroup G)
    (hR : IsPGroup p R) (hne : R ≠ ⊥) :
    ∃ B : Subgroup G, IsPRadical p B ∧ R ≤ B ∧
      normalizer (R : Set G) ≤ normalizer (B : Set G) := by
  classical
  let candidates : Set (Subgroup G) :=
    {B | IsPGroup p B ∧ R ≤ B ∧ normalizer (R : Set G) ≤ normalizer (B : Set G)}
  obtain ⟨B, hB, hmax⟩ := candidates.toFinite.exists_maximal ⟨R, hR, le_rfl, le_rfl⟩
  let N := normalizer (B : Set G)
  let D := (pCore p N).map N.subtype
  have hBD : B ≤ D := le_map_pCore_normalizer hB.1
  have hND : N ≤ normalizer (D : Set G) :=
    N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore p N))
  have hDB : D ≤ B := hmax ⟨pCore_isPGroup.map _, hB.2.1.trans hBD,
    hB.2.2.trans hND⟩ hBD
  refine ⟨B, ⟨?_, le_antisymm hDB hBD⟩, hB.2⟩
  intro hbot
  exact hne (eq_bot_iff.mpr (hbot ▸ hB.2.1))

/-- Radicality transfers to an overgroup when its normalizer stays in the smaller group.
This is the arbitrary-prime form of Aschbacher–Smith C.1.2(3). -/
theorem IsPRadical.subgroupOf_of_normalizer_le {G : Type*} [Group G] {p : ℕ} (R H K : Subgroup G)
    (hRH : R ≤ H) (hHK : H ≤ K)
    (hrad : IsPRadical p (R.subgroupOf H))
    (hNK : K ⊓ normalizer (R : Set G) ≤ H) :
    IsPRadical p (R.subgroupOf K) := by
  let NH := normalizer (R.subgroupOf H : Set H)
  let NK := normalizer (R.subgroupOf K : Set K)
  have hRK := hRH.trans hHK
  have hHmem (x : H) : x ∈ NH ↔ (x : G) ∈ normalizer (R : Set G) := by
    change x ∈ normalizer (R.subgroupOf H : Set H) ↔ _
    rw [← subgroupOf_normalizer_eq hRH]
    rfl
  have hKmem (x : K) : x ∈ NK ↔ (x : G) ∈ normalizer (R : Set G) := by
    change x ∈ normalizer (R.subgroupOf K : Set K) ↔ _
    rw [← subgroupOf_normalizer_eq hRK]
    rfl
  let e : NK ≃* NH :=
    { toFun := fun x => ⟨⟨x, hNK ⟨x.val.property, (hKmem x).mp x.property⟩⟩,
        (hHmem _).mpr ((hKmem x).mp x.property)⟩
      invFun := fun x => ⟨⟨x, hHK x.val.property⟩,
        (hKmem _).mpr ((hHmem x).mp x.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hcore : (pCore p NK).map e.toMonoidHom = pCore p NH := pCore_map_iso p e
  have hmap : ((pCore p NK).map NK.subtype).map K.subtype =
      ((pCore p NH).map NH.subtype).map H.subtype := by
    rw [← hcore, map_map, map_map, map_map]
    rfl
  have htarget : ((pCore p NK).map NK.subtype).map K.subtype =
      (R.subgroupOf K).map K.subtype := by
    rw [hmap, hrad.2, map_subgroupOf_eq_of_le hRH, map_subgroupOf_eq_of_le hRK]
  refine ⟨?_, map_injective K.subtype_injective htarget⟩
  intro hbot
  have hRbot : R = ⊥ := by
    have hh := congrArg (fun C : Subgroup K => C.map K.subtype) hbot
    simpa only [map_subgroupOf_eq_of_le hRK, Subgroup.map_bot] using hh
  apply hrad.1
  simp [hRbot]

end Subgroup
