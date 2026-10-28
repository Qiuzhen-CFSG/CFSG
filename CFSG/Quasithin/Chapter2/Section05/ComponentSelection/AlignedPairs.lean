module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.MaximalPairBase
public import CFSG.Quasithin.Chapter2.Section05.ComponentSetup
public import Theory.GroupTheory.SylowKernelCore

/-!
# Aligning the saturated pair with the prescribed source Sylow

Conjugation within H intersect M preserves the genuine local pair, its
largest-base condition and saturation. Sylow conjugacy in that intersection
therefore places its base and two-core inside the prescribed source Sylow.
This supplies the conjugation step on printed p.552 of source 2.5.3(4).
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

omit [Finite G] in
private theorem core_map (K : Subgroup G) (e : MulAut G) :
    (twoCore K).map e.toMonoidHom = twoCore (K.map e.toMonoidHom) :=
  map_pCoreIn_of_injective 2 K e.toMonoidHom e.injective

omit [Finite G] in
/-- A conjugator in H intersect M preserves the actual local pair. -/
theorem local_pair_conjugate
    (hp : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    {a : G} (haH : a ∈ H) (haM : a ∈ M) :
    (U.map (MulAut.conj a).toMonoidHom, HU.map (MulAut.conj a).toMonoidHom) ∈
      localPairsIn (Chapter1.He G) M H := by
  let e := MulAut.conj a
  have hM : M.map e.toMonoidHom = M := mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer haM)
  have hH : H.map e.toMonoidHom = H := mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer haH)
  refine ⟨⟨beta_conjugate hp.1.1 haM, ?_, ?_, map_mono hp.1.2.2.2.1, ?_⟩,
    (map_mono hp.2).trans hH.le⟩
  · exact Chapter1.mem_He_iff.mpr ((Theory.Quasithin.centralizer_pCore_le_iff 2
      (e.subgroupMap HU)).mp (Chapter1.mem_He_iff.mp hp.1.2.1))
  · rw [← core_map]
    intro hb
    apply hp.1.2.2.1
    apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
    simpa using hb
  · intro hle
    apply hp.1.2.2.2.2
    exact (e.mapSubgroup.le_iff_le).mp (hle.trans hM.ge)

omit [Finite G] in
/-- The selected saturated pair can be conjugated under H intersect M
without losing its largest-base or saturation properties. -/
theorem saturated_pair_conjugate
    (hbig : H ∈ gammaStar (Chapter1.He G) M →
      ∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    {a : G} (haH : a ∈ H) :
    (H ∈ gammaStar (Chapter1.He G) M →
      ∀ V ∈ localBases (Chapter1.He G) M,
        Nat.card V ≤ Nat.card (U.map (MulAut.conj a).toMonoidHom)) ∧
    ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU.map (MulAut.conj a).toMonoidHom ≤ normalizer (P : Set G) →
        P ≤ twoCore (HU.map (MulAut.conj a).toMonoidHom) := by
  let e := MulAut.conj a
  have hH : H.map e.toMonoidHom = H := mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer haH)
  have hHi : H.map e.symm.toMonoidHom = H := (map_symm_eq_iff_map_eq (K := H) (H := H) (e := e)).mpr hH
  have hei : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by ext x; exact e.symm_apply_apply x
  have hie : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by ext x; exact e.apply_symm_apply x
  refine ⟨?_, ?_⟩
  · intro hs V hV
    exact (hbig hs V hV).trans_eq (Nat.card_congr (e.subgroupMap U).toEquiv)
  · intro P hPH hpP hn
    have hnorm : HU ≤ normalizer (P.map e.symm.toMonoidHom : Set G) := by
      rw [← map_equiv_normalizer_eq P e.symm]
      change HU.map e.toMonoidHom ≤ normalizer (P : Set G) at hn
      have hh := map_mono (f := e.symm.toMonoidHom) hn
      simpa only [map_map, hei, map_id] using hh
    have hb := hsat (P.map e.symm.toMonoidHom)
      ((map_mono hPH).trans hHi.le) (hpP.map e.symm.toMonoidHom) hnorm
    have hh := map_mono (f := e.toMonoidHom) hb
    simpa only [map_map, hie, map_id, core_map] using hh

/-- The original prescribed Sylow contains the selected base and saturated
core, while both source maximality properties are retained. -/
theorem exists_saturated_pair_aligned
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M) :
    ∃ U HU : Subgroup G, (U, HU) ∈ localPairsIn (Chapter1.He G) M H ∧
      U ≤ (S : Subgroup H).map H.subtype ∧
      twoCore HU ≤ (S : Subgroup H).map H.subtype ∧
      (H ∈ gammaStar (Chapter1.He G) M →
        ∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U) ∧
      ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
        HU ≤ normalizer (P : Set G) → P ≤ twoCore HU := by
  obtain ⟨U, HU, hp, hbig, hsat⟩ := exists_saturated_pair_preserving_star hH
  obtain ⟨R₀, hUR₀, hb₀⟩ := beta_exists_sylow hp.1.1 hp.1.2.2.2.1
  obtain ⟨R, hR₀R, hb⟩ := beta_exists_sylow hb₀ ((map_subtype_le _).trans hp.2)
  have hUR : U ≤ (R : Subgroup H).map H.subtype := hUR₀.trans hR₀R
  have hQR : twoCore HU ≤ (R : Subgroup H).map H.subtype :=
    (pCoreIn_le_sylow HU R₀).trans hR₀R
  obtain ⟨P, hP⟩ := sylow_image_in_inf R hb.2.1
  obtain ⟨Q, hQ⟩ := sylow_image_in_inf S hSM
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq ↥(H ⊓ M) P Q
  let e := MulAut.conj (a : G)
  have he : ((R : Subgroup H).map H.subtype).map e.toMonoidHom =
      (S : Subgroup H).map H.subtype := by
    rw [← hP, ← hQ]
    have hh := congrArg (fun W : Sylow 2 ↥(H ⊓ M) =>
      (W : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) ha
    change ((P : Subgroup ↥(H ⊓ M)).map (MulAut.conj a).toMonoidHom).map
      (H ⊓ M).subtype = _ at hh
    rw [map_map] at hh ⊢
    exact hh
  obtain ⟨hbig', hsat'⟩ := saturated_pair_conjugate hbig hsat a.property.1
  refine ⟨U.map e.toMonoidHom, HU.map e.toMonoidHom,
    local_pair_conjugate hp a.property.1 a.property.2,
    (map_mono hUR).trans he.le, ?_, hbig', hsat'⟩
  rw [← core_map]
  exact (map_mono hQR).trans he.le

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
