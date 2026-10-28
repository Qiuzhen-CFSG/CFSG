module

public import CFSG.Quasithin.ChapterE.Section01.QuotientLifting.OddSections
public import Theory.GroupTheory.ConjugacyFamilySpan

/-!
# Quotient families and lifting generation

Sylow conjugacy inside the preimage of the quotient Sylow group produces
a representative of each image-family member inside the original Sylow
group. Weak closure similarly lifts its full normalizer. Combined with
E.1.10(7), these prove generation modulo a normal kernel, and generation
itself when that kernel is a two-group.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, E.1.7 and E.1.11--13, pp.210--214.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]
variable {H : Type*} [Group H]

omit [Finite G] in
theorem IsElementaryFamily.conjugationInvariant {Ω : Set (Subgroup G)}
    (hΩ : IsElementaryFamily Ω) : SubgroupFamily.ConjugationInvariant Ω :=
  fun A hA g => hΩ.2 g A hA

theorem sylow_le_weakClosure_normalizer (T : Sylow 2 G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    (T : Subgroup G) ≤ normalizer (weakClosure (T : Subgroup G) Ω : Set G) :=
  T.toSubgroup.le_normalizer.trans
    (SubgroupFamily.normalizer_le_span_normalizer hΩ.conjugationInvariant _)

private theorem exists_conjugate_le_sylow_in_preimage (T : Sylow 2 G)
    (f : G →* H) (A : Subgroup G) (hp : IsPGroup 2 A)
    (hA : A.map f ≤ (T : Subgroup G).map f) :
    ∃ k : ((T : Subgroup G).map f).comap f,
      A.map (MulAut.conj (k : G)).toMonoidHom ≤ (T : Subgroup G) := by
  let K := ((T : Subgroup G).map f).comap f
  have hTK : (T : Subgroup G) ≤ K := le_comap_map f _
  have hAK : A ≤ K := map_le_iff_le_comap.mp hA
  obtain ⟨P, hAP⟩ := hp.comap_subtype (K := K) |>.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P (T.subtype hTK)
  refine ⟨k, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have hm : (⟨a, hAK ha⟩ : K) ∈ (P : Subgroup K) := hAP ha
  have hn : k * (⟨a, hAK ha⟩ : K) * k⁻¹ ∈ (T.subtype hTK : Subgroup K) := by
    rw [← hk]
    exact mem_map_of_mem (MulAut.conj k).toMonoidHom hm
  exact hn

/-- A family member whose image lies in the quotient Sylow group has a
kernel-conjugate inside the original Sylow group, with the same image. -/
theorem IsElementaryFamily.exists_sylow_representative
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) (T : Sylow 2 G)
    (f : G →* H) {B : Subgroup H} (hB : B ∈ Subgroup.map f '' Ω)
    (hBT : B ≤ (T : Subgroup G).map f) :
    ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ A.map f = B := by
  obtain ⟨A, hA, rfl⟩ := hB
  let _ := hΩ.1 A hA
  obtain ⟨k, hk⟩ := exists_conjugate_le_sylow_in_preimage T f A
    (IsElementaryAbelian.isPGroup 2 A) hBT
  obtain ⟨t, ht, htk⟩ := k.property
  let g := t⁻¹ * (k : G)
  have hfg : f g = 1 := by simp [g, htk]
  refine ⟨A.map (MulAut.conj g).toMonoidHom, hΩ.2 g A hA, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    have haT := hk (mem_map_of_mem (MulAut.conj (k : G)).toMonoidHom ha)
    have hb := (T : Subgroup G).mul_mem
      ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem ht) haT) ht
    simpa [g, MulAut.conj_apply, mul_assoc] using hb
  · rw [map_map]
    have he : f.comp (MulAut.conj g).toMonoidHom = f := by
      ext a
      simp [MulAut.conj_apply, hfg]
    rw [he]

omit [Finite G] in
theorem IsElementaryFamily.map {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (f : G →* H) (hf : Function.Surjective f) : IsElementaryFamily (Subgroup.map f '' Ω) := by
  constructor
  · rintro _ ⟨A, hA, rfl⟩
    let _ := hΩ.1 A hA
    exact IsElementaryAbelian.map f
  · rintro h _ ⟨A, hA, rfl⟩
    obtain ⟨g, rfl⟩ := hf h
    refine ⟨A.map (MulAut.conj g).toMonoidHom, hΩ.2 g A hA, ?_⟩
    rw [map_map, map_map]
    congr 1
    ext a
    simp

theorem map_weakClosure_surjective (T : Sylow 2 G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) (f : G →* H) :
    (weakClosure (T : Subgroup G) Ω).map f =
      weakClosure ((T : Subgroup G).map f) (Subgroup.map f '' Ω) := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro A hA
    exact map_le_iff_le_comap.mp (le_sSup ⟨⟨A, hA.1, rfl⟩, map_mono hA.2⟩)
  · apply sSup_le
    intro B hB
    obtain ⟨A, hA, hAT, rfl⟩ := hΩ.exists_sylow_representative T f hB.1 hB.2
    exact map_mono (le_sSup ⟨hA, hAT⟩)

/-- Weak closure gives full lifting of its normalizer, for an arbitrary quotient. -/
theorem map_weakClosure_normalizer_surjective (T : Sylow 2 G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (f : G →* H) (hf : Function.Surjective f) :
    (normalizer (weakClosure (T : Subgroup G) Ω : Set G)).map f =
      normalizer ((weakClosure (T : Subgroup G) Ω).map f : Set H) := by
  let W := weakClosure (T : Subgroup G) Ω
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) :=
    sylow_le_weakClosure_normalizer T hΩ
  apply le_antisymm (le_normalizer_map f)
  intro b hb
  obtain ⟨g, rfl⟩ := hf b
  change f g ∈ normalizer (W.map f : Set H) at hb
  have hmap : (W.map (MulAut.conj g).toMonoidHom).map f ≤ (T : Subgroup G).map f := by
    have he : (W.map (MulAut.conj g).toMonoidHom).map f =
        (W.map f).map (MulAut.conj (f g)).toMonoidHom := by
      rw [map_map, map_map]
      congr 1
      ext w
      simp
    rw [he]
    exact (mem_normalizer_iff_map_conj_eq.mp hb).le.trans (map_mono (weakClosure_le _ _))
  obtain ⟨k, hk⟩ := exists_conjugate_le_sylow_in_preimage T f _
    ((T.isPGroup'.to_le (weakClosure_le _ _)).map _) hmap
  have hkg : (k : G) * g ∈ normalizer (W : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply SubgroupFamily.span_weakly_closed hΩ.conjugationInvariant (T : Subgroup G)
    rintro _ ⟨w, hw, rfl⟩
    have hm := hk (mem_map_of_mem (MulAut.conj (k : G)).toMonoidHom
      (mem_map_of_mem (MulAut.conj g).toMonoidHom hw))
    simpa [MulAut.conj_apply, mul_assoc] using hm
  have hfk : f k ∈ (normalizer (W : Set G)).map f := (map_mono hTW) k.property
  have hfkg : f k * f g ∈ (normalizer (W : Set G)).map f := by
    simpa using mem_map_of_mem f hkg
  simpa [mul_assoc] using ((normalizer (W : Set G)).map f).mul_mem
    (((normalizer (W : Set G)).map f).inv_mem hfk) hfkg

/-- E.1.10(7), summed over the actual image family. -/
theorem quotient_eFamilySubgroup_le_map_sup_sylow {i : ℕ} (T : Sylow 2 G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) (Y : Subgroup G) [Y.Normal] :
    eFamilySubgroup i ((T : Subgroup G).map (QuotientGroup.mk' Y))
      (Subgroup.map (QuotientGroup.mk' Y) '' Ω) ≤
      (eFamilySubgroup i (T : Subgroup G) Ω ⊔ (T : Subgroup G)).map (QuotientGroup.mk' Y) := by
  apply iSup_le
  intro B
  obtain ⟨A, hA, hAT, he⟩ := hΩ.exists_sylow_representative T (QuotientGroup.mk' Y)
    B.property.1 B.property.2
  let _ := hΩ.1 A hA
  change eSubgroup i _ B.val ≤ _
  rw [← he]
  have hAE : eSubgroup i (T : Subgroup G) A ≤ eFamilySubgroup i (T : Subgroup G) Ω :=
    le_iSup_of_le (⟨A, hA, hAT⟩ : {A : Subgroup G // A ∈ Ω ∧ A ≤ (T : Subgroup G)}) le_rfl
  exact (quotient_eSubgroup_le_map_sup_sylow (i := i) T A Y hAT).trans
    (map_mono (sup_le_sup_right hAE _))

/-- Quotient generation lifts modulo the normal kernel. -/
theorem generation_modulo_normal {i : ℕ} (T : Sylow 2 G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) (Y : Subgroup G) [Y.Normal]
    (hgen : IsEGenerated i (G ⧸ Y)) :
    (eFamilySubgroup i (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G)) ⊔ Y = ⊤ := by
  let q := QuotientGroup.mk' Y
  have hq := QuotientGroup.mk'_surjective Y
  have hg := hgen (T.mapSurjective (f := q) hq) _ (hΩ.map q hq)
  let M := eFamilySubgroup i (T : Subgroup G) Ω ⊔
    normalizer (weakClosure (T : Subgroup G) Ω : Set G)
  have hmap : M.map q = ⊤ := by
    apply top_unique
    rw [← hg]
    apply sup_le
    · exact (quotient_eFamilySubgroup_le_map_sup_sylow T hΩ Y).trans
        (map_mono (sup_le le_sup_left
          ((sylow_le_weakClosure_normalizer T hΩ).trans le_sup_right)))
    · change normalizer (weakClosure ((T : Subgroup G).map q) (Subgroup.map q '' Ω) : Set (G ⧸ Y)) ≤ _
      rw [← map_weakClosure_surjective T hΩ q,
        ← map_weakClosure_normalizer_surjective T hΩ q hq]
      exact map_mono le_sup_right
  have hm := congrArg (comap q) hmap
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hm

/-- A normal two-group kernel does not obstruct E-generation. -/
theorem IsEGenerated.of_normal_two_subgroup {i : ℕ} (Y : Subgroup G) [Y.Normal]
    (hY : IsPGroup 2 Y) (hgen : IsEGenerated i (G ⧸ Y)) : IsEGenerated i G := by
  intro T Ω hΩ
  have h := generation_modulo_normal T hΩ Y hgen
  have hYM : Y ≤ eFamilySubgroup i (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) :=
    ((hY.le_sylow_of_normal T).trans (sylow_le_weakClosure_normalizer T hΩ)).trans le_sup_right
  simpa only [sup_eq_left.mpr hYM] using h


end CFSG.Quasithin.ChapterE
