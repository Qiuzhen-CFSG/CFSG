module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.BlockSylow
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.Inheritance
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The reduced group hypotheses in C.5.9

The original characteristic-two core lies in T₁ because it centralizes U₁.
Consequently K₁T₁ inherits characteristic two and the genuine ambient QTKE
hypothesis makes it SQTK. The original chi-zero block gives its marked
Sylow and unique maximal overgroup; two-perfectness identifies its residual.
The original escaping conjugate rules out normality of T₁ in K₁T₁.

Source: Aschbacher–Smith, C.5.9, printed p.161.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
variable {G : Type*} [Group G] [Finite G]

theorem reduced_group_mem_He (T : Sylow 2 G) (H K U T₁ : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hKH : K ≤ H) (hH : H ∈ Chapter1.He G)
    (hcoreU : H.pCoreIn 2 ≤ centralizer (U : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (U : Set G)) (hK : K ≠ ⊥) :
    K ⊔ T₁ ∈ Chapter1.He G := by
  have hcoreT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at hh
  have hcoreT₁ : H.pCoreIn 2 ≤ T₁ := by
    rw [hT₁]
    exact le_inf hcoreT (hcoreU.trans (Subgroup.centralizer_le_normalizer _))
  have hT₁H : T₁ ≤ H := (hT₁ ▸ inf_le_left).trans hTH
  exact Chapter1.lemma_1_1_4_4
    (fun he => hK (bot_unique (he ▸ (show K ≤ K ⊔ T₁ from le_sup_left))))
    (sup_le hKH hT₁H) hH (inf_le_left.trans (hcoreT₁.trans le_sup_right))

theorem sqtk_of_mem_He {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (A : Subgroup G) (hA : A ∈ Chapter1.He G) (hAne : A ≠ ⊥) : IsSQTK 𝒦 A := by
  have hcore : A.pCoreIn 2 ≠ ⊥ := by
    intro he
    apply hAne
    apply bot_unique
    intro a ha
    have hc : a ∈ A ⊓ centralizer (A.pCoreIn 2 : Set G) := by
      refine ⟨ha,?_⟩
      rw [he]
      intro z hz
      have hz1 : z = 1 := hz
      simp [hz1]
    simpa only [he] using hA hc
  have hAN : A ≤ normalizer (A.pCoreIn 2 : Set G) := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hs := hG.twoLocal_sqtk (show IsTwoLocal (normalizer (A.pCoreIn 2 : Set G)) from
    ⟨A.pCoreIn 2,hcore,isPGroup_pCoreIn 2 A,rfl⟩)
  exact ⟨hs.stronglyQuasithin.of_injective (inclusion hAN) (inclusion_injective hAN),
    hs.isKGroup.of_injective (inclusion hAN) (inclusion_injective hAN)⟩

omit [Finite G] in
theorem normal_extension_residual (K T : Subgroup G) (hK : IsPPerfect 2 K)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G)) :
    (pResidual 2 (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = K := by
  let A := K ⊔ T
  let K₀ := K.subgroupOf A
  let T₀ := T.subgroupOf A
  let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le K.le_normalizer hn)
  have hp : IsPPerfect 2 K₀ := hK.of_surjective
    (subgroupOfEquivOfLe (show K ≤ A from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show K ≤ A from le_sup_left)).symm.surjective
  have he : K₀ ⊔ T₀ = ⊤ := by
    change K.subgroupOf A ⊔ T.subgroupOf A = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self A
  rw [pResidual_eq_of_isPPerfect_sup K₀ T₀ hp hT.comap_subtype he]
  exact map_subgroupOf_eq_of_le (show K ≤ A from le_sup_left)

omit [Finite G] in
theorem normal_extension_not_normal (K S T U : Subgroup G)
    (hT : IsPGroup 2 T) (hST : S ≤ T)
    (hc : (K ⊔ S).pCoreIn 2 ≤ centralizer (U : Set G))
    (x : G) (hxS : U.map (MulAut.conj x⁻¹).toMonoidHom ≤ S)
    (hnc : ¬ U.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U : Set G)) :
    ¬ K ⊔ T ≤ normalizer (T : Set G) := by
  intro hn
  have hBA : K ⊔ S ≤ K ⊔ T := sup_le_sup le_rfl hST
  have hnormal : K ⊔ S ≤ normalizer ((T ⊓ (K ⊔ S) : Subgroup G) : Set G) :=
    (le_inf (hBA.trans hn) (K ⊔ S).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hi : T ⊓ (K ⊔ S) ≤ (K ⊔ S).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (hT.to_le inf_le_left) inf_le_right hnormal
  exact hnc (hxS.trans ((le_inf hST le_sup_right).trans (hi.trans hc)))

theorem minimal_parabolic_of_ambient_unique (A T : Subgroup G)
    (P : Sylow 2 A) (hP : (P : Subgroup A).map A.subtype = T)
    (hu : Order.HasUniqueMaximalOver T A) (hn : ¬ A ≤ normalizer (T : Set G)) :
    ChapterB.IsMinimalParabolicOver P ⊤ := by
  obtain ⟨M,hM,huniq⟩ := hu.2
  have hMA : M ≤ A := hM.2.le
  have hPM : (P : Subgroup A) ≤ M.subgroupOf A := by
    intro a ha
    exact hM.1 (hP ▸ mem_map_of_mem A.subtype ha)
  have hMne : M.subgroupOf A ≠ ⊤ := by
    intro he
    have hh := congrArg (map A.subtype) he
    rw [map_subgroupOf_eq_of_le hMA,← MonoidHom.range_eq_map,A.range_subtype] at hh
    exact hM.2.ne hh
  have hproper (B : Subgroup A) (hPB : (P : Subgroup A) ≤ B) (hB : B ≠ ⊤) :
      B ≤ M.subgroupOf A := by
    have hb : B.map A.subtype < A := lt_of_le_of_ne (map_subtype_le _) (by
      intro he
      apply hB
      apply (map_injective A.subtype_injective)
      simpa only [← MonoidHom.range_eq_map,A.range_subtype] using he)
    have ht : T ≤ B.map A.subtype := hP ▸ map_mono hPB
    exact map_le_iff_le_comap.mp (hu.le_maximal hM ht hb)
  have hco : IsCoatom (M.subgroupOf A) := by
    refine ⟨hMne,?_⟩
    intro B hMB
    by_contra hB
    exact hMB.not_ge (hproper B (hPM.trans hMB.le) hB)
  apply (ChapterB.isMinimalParabolicOver_top_iff P).mpr
  refine ⟨⟨M.subgroupOf A,⟨hco,hPM⟩,?_⟩,?_⟩
  · intro B hB
    have hBM := hproper B hB.2 hB.1.ne_top
    by_contra he
    exact hMne (hB.1.2 _ (lt_of_le_of_ne hBM he))
  · intro hnormal
    let := hnormal
    apply hn
    rw [← hP]
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,A.range_subtype] using
      (P : Subgroup A).le_normalizer_map A.subtype
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
