module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.ThompsonExtension

/-!
# Applying the intrinsic Thompson argument to ambient subgroups

The source subgroups live in `G`, whereas the normal cores and Thompson
extension must be formed inside `G₀`. Injectivity of the inclusion transports
`J(T_E)`, its normalizer, the omega-center, and the actual right-conjugate
span. Centralizer and subgroup orders divide their ambient counterparts,
so the two prime-support bounds restrict correctly. The resulting theorem
applies the completed Thompson extension argument without assuming either
its factorization or its core equality.

The explicit earlier-source witnesses are F.6.11(1), giving the normal
Sylow two-subgroup and solvability of the three-prime core, and the complete
source statement of B.2.16. No ambient normality of `O₂(G₀)` is imposed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.68, printed pp.1154–1155.
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore
open ThompsonExtension
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem span_subgroupOf_map (H Y Z : Subgroup G) (hY : Y ≤ H) (hZ : Z ≤ H) :
    (conjugateSpan (Y.subgroupOf H) (Z.subgroupOf H)).map H.subtype =
      conjugateSpan Y Z := by
  unfold conjugateSpan
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro y
    apply le_trans _ (le_iSup _ (⟨y.val.val, y.property⟩ : Y))
    rintro x ⟨v, ⟨z, hz, rfl⟩, rfl⟩
    exact mem_map.mpr ⟨z.val, hz, rfl⟩
  · apply iSup_le
    intro y
    apply le_trans _ (le_iSup _ (⟨⟨y, hY y.property⟩, y.property⟩ : Y.subgroupOf H))
    rintro x ⟨z, hz, rfl⟩
    exact mem_map.mpr ⟨_, mem_map.mpr ⟨⟨z, hZ hz⟩, hz, rfl⟩, rfl⟩

/-- Restrict the genuine ambient local data to the intrinsic group and derive the extension products and core equality. -/
theorem extension_of_ambient_data
    (H D V R Y Z F M : Subgroup G)
    (hF611 : ∀ A B : Subgroup H, ChapterF.IsGoldschmidtTriple A B →
      IsSylowSubgroupIn (pCore 2 H) (pPrimeCore 3 H) ∧ Group.IsSolvable (pPrimeCore 3 H))
    (hB216 : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (A B : Subgroup H) (hGold : ChapterF.IsGoldschmidtTriple A B)
    (U : Sylow 2 H) (hU : (U : Subgroup H).map H.subtype = D)
    (hV : V ≤ twoCoreAmbient H) (hC : centralizer (V : Set G) ≤ R) (hR : IsPGroup 2 R)
    (hYH : Y ≤ H) (hFH : F ≤ H)
    (hY : Y ≤ normalizer (elementaryAbelianMaxJ D : Set G))
    (hZ : Z ≤ omegaOneCenterAmbient D) (hF : F = conjugateSpan Y Z)
    (hJF : elementaryAbelianMaxJ D ≤ centralizer (F : Set G))
    (hCF : ∀ p : ℕ, p.Prime → p ∣ Nat.card (centralizer (F : Set G)) → p = 2 ∨ p = 3)
    (hM : ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3)
    (hJM : normalizer (elementaryAbelianMaxJ D : Set G) ≤ M) :
    ExtensionResult U (Y.subgroupOf H) (F.subgroupOf H) := by
  have hDH : D ≤ H := hU ▸ map_subtype_le _
  have hVH : V ≤ H := hV.trans (map_subtype_le _)
  have hZH : Z ≤ H := hZ.trans ((map_subtype_le _).trans hDH)
  have hJmap : (elementaryAbelianMaxJ (U : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ D := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective, hU]
  have hJH : elementaryAbelianMaxJ D ≤ H := hJmap ▸ map_subtype_le _
  have hJeq : elementaryAbelianMaxJ (U : Subgroup H) =
      (elementaryAbelianMaxJ D).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hJmap, map_subgroupOf_eq_of_le hJH]
  have hCi : centralizer (V.subgroupOf H : Set H) ≤ R.subgroupOf H := by
    intro c hc
    apply hC
    apply mem_centralizer_iff.mpr
    intro v hv
    exact congrArg Subtype.val (mem_centralizer_iff.mp hc ⟨v, hVH hv⟩ hv)
  have hFi : F.subgroupOf H = conjugateSpan (Y.subgroupOf H) (Z.subgroupOf H) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hFH, span_subgroupOf_map H Y Z hYH hZH, hF]
  apply apply_F611_B216 hF611 hB216 A B hGold U
    (V.subgroupOf H) (R.subgroupOf H) (Y.subgroupOf H) (Z.subgroupOf H)
    (F.subgroupOf H) (M.subgroupOf H)
  · intro v hv
    obtain ⟨q, hq, he⟩ := hV hv
    exact (Subtype.ext he : q = v) ▸ hq
  · exact hCi
  · exact hR.comap_subtype
  · rw [hJeq, ← subgroupOf_normalizer_eq hJH]
    exact comap_mono hY
  · have hmap : (omegaOneCenterAmbient (U : Subgroup H)).map H.subtype =
        omegaOneCenterAmbient D := by
      rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective, hU]
    intro z hz
    obtain ⟨w, hw, he⟩ := hmap ▸ hZ hz
    exact (Subtype.ext he : w = z) ▸ hw
  · exact hFi
  · intro j hj
    apply mem_centralizer_iff.mpr
    intro f hf
    apply Subtype.ext
    exact mem_centralizer_iff.mp (hJF (hJmap ▸ mem_map_of_mem H.subtype hj)) f hf
  · intro p hp hd
    apply hCF p hp
    have hc : (centralizer (F.subgroupOf H : Set H)).map H.subtype ≤
        centralizer (F : Set G) := by
      have hh := map_centralizer_le_centralizer_image (F.subgroupOf H) H.subtype
      change _ ≤ centralizer (((F.subgroupOf H).map H.subtype) : Set G) at hh
      rwa [map_subgroupOf_eq_of_le hFH] at hh
    have hd' := card_dvd_of_le hc
    rw [card_map_of_injective H.subtype_injective] at hd'
    exact hd.trans hd'
  · intro p hp hd
    have hd' := card_dvd_of_le (map_comap_le H.subtype M)
    rw [card_map_of_injective H.subtype_injective] at hd'
    exact hM p hp (hd.trans hd')
  · rw [hJeq, ← subgroupOf_normalizer_eq hJH]
    exact comap_mono hJM

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore
