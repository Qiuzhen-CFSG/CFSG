module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedGroup
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.Source
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.SourceSylow

/-!
# Constructing the genuine reduced hypotheses of C.5.9

The original marked block supplies the intrinsic Sylow intersection, while
its original escaping conjugate rules out normality in K₁T₁. Characteristic
two, SQTK, the unique maximal Sylow overgroup and O²(K₁T₁)=K₁ are all
derived on those literal subgroups. The original central-involution orbit
also proves the absence of a common normal subgroup with N_G(T₁).

These are exactly the reduced C.5.1–2 inputs. Constructing the subsequent
marked C.5.3–4 setup is an application of that earlier source producer;
no reduced marked setup is assumed by the theorems here.

Source: Aschbacher–Smith, C.5.9, printed p.161.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
open ConjugateSource
variable {G : Type*} [Group G] [Finite G]

private theorem source_reduced_conditions (T : Sylow 2 G) {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (H K L T₁ S : Subgroup G) (hH : H = (K ⊔ L) ⊔ (T : Subgroup G))
    (hHe : H ∈ Chapter1.He G) (hcoreU : H.pCoreIn 2 ≤ centralizer (RankOne.U K : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (RankOne.U K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2) (hK : IsChiZeroBlock K)
    (hNK : T₁ ≤ normalizer (K : Set G)) (hST₁ : S ≤ T₁)
    (hcore : (K ⊔ S).pCoreIn 2 ≤ centralizer (RankOne.U K : Set G))
    (hP : ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype ≤ T₁)
    (hUorbit : RankOne.U K ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G))
    (hxS : (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ S)
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G)) :
    let A := K ⊔ T₁
    let Y := normalizer (T₁ : Set G)
    A ∈ Chapter1.He G ∧ IsSQTK 𝒦 A ∧ (pResidual 2 A).map A.subtype = K ∧
      (∃ P : Sylow 2 A, (P : Subgroup A).map A.subtype = T₁ ∧ ChapterB.IsMinimalParabolicOver P ⊤) ∧
      (T₁.subgroupOf Y).Normal ∧
      ∀ N : Subgroup G, N ≤ T₁ → Y ≤ normalizer (N : Set G) →
        A ≤ normalizer (N : Set G) → N = ⊥ := by
  have hT₁T : T₁ ≤ (T : Subgroup G) := hT₁ ▸ inf_le_left
  have hTH : (T : Subgroup G) ≤ H := hH ▸ le_sup_right
  have hKH : K ≤ H := hH ▸ le_sup_left.trans le_sup_left
  have hT₁p : IsPGroup 2 T₁ := T.isPGroup'.to_le hT₁T
  have hKshort : IsShort K := by
    rcases hK with ⟨_,hn⟩ | hn | hn <;> exact hn.2.1
  have hKne : K ≠ ⊥ := by
    intro he
    have hu : RankOne.U K = ⊥ := bot_unique (he ▸ (map_subtype_le (blockU K)))
    apply hnc
    rw [hu,Subgroup.map_bot]
    exact bot_le
  have hAe := reduced_group_mem_He T H K (RankOne.U K) T₁ hTH hKH hHe hcoreU hT₁ hKne
  have hAne : K ⊔ T₁ ≠ ⊥ := fun he => hKne (bot_unique (he ▸ (show K ≤ K ⊔ T₁ from le_sup_left)))
  obtain ⟨P,hP⟩ := hP
  have hu := chiZeroBlock_extension_unique K T₁ hK hT₁p hNK P hP
  obtain ⟨Q,hQ⟩ := chiZeroBlock_extension_sylow K T₁ hT₁p hNK P hP
  have hn := normal_extension_not_normal K S T₁ (RankOne.U K) hT₁p hST₁ hcore x hxS hnc
  refine ⟨hAe,sqtk_of_mem_He hG _ hAe hAne,
    normal_extension_residual K T₁ hKshort.twoPerfect hT₁p hNK,
    ⟨Q,hQ,minimal_parabolic_of_ambient_unique _ T₁ Q hQ hu hn⟩,
    (normal_subgroupOf_iff_le_normalizer T₁.le_normalizer).mpr le_rfl,?_⟩
  intro N hNT hYN hKN
  exact CounterexampleReduction.reduced_common_normal_eq_bot T (hG.evenCharacteristic T)
    H K L T₁ (RankOne.U K) hT₁T hhalf hH t ht hKt hUorbit hcoreU x hx
    (hxS.trans (hST₁.trans (hT₁T.trans hTH))) hnc N hNT hYN hKN

/-- C.5.9 for the original natural/A₃ marked block; every reduced group condition is constructed. -/
theorem rank_one_reduced_conditions (T : Sylow 2 G) {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (H R K L T₁ : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    {F : Type*} [Field F] (h : RankOne.Setup R K F)
    (hH : H = (K ⊔ L) ⊔ (T : Subgroup G)) (hHe : H ∈ Chapter1.He G)
    (hcoreU : H.pCoreIn 2 ≤ centralizer (RankOne.U K : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (RankOne.U K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2) (hNK : T₁ ≤ normalizer (K : Set G))
    (hUorbit : RankOne.U K ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G)) :
    let A := K ⊔ T₁
    let Y := normalizer (T₁ : Set G)
    A ∈ Chapter1.He G ∧ IsSQTK 𝒦 A ∧ (pResidual 2 A).map A.subtype = K ∧
      (∃ P : Sylow 2 A, (P : Subgroup A).map A.subtype = T₁ ∧ ChapterB.IsMinimalParabolicOver P ⊤) ∧
      (T₁.subgroupOf Y).Normal ∧
      ∀ N : Subgroup G, N ≤ T₁ → Y ≤ normalizer (N : Set G) →
        A ≤ normalizer (N : Set G) → N = ⊥ := by
  have hST₁ : RankOne.S R ≤ T₁ := by
    rw [hT₁]
    exact le_inf (inf_le_left.trans hRT) h.coordinates.normalizes
  have hK : IsChiZeroBlock K := by
    rcases h.block with ⟨n,hn,_⟩ | ha
    · exact Or.inl ⟨n,hn⟩
    · exact Or.inr (Or.inl ha)
  obtain ⟨P,hP⟩ := h.source_sylow_block (T.isPGroup'.to_le hRT)
  exact source_reduced_conditions T hG H K L T₁ (RankOne.S R) hH hHe hcoreU hT₁ hhalf
    hK hNK hST₁ (h.core.le.trans inf_le_right) ⟨P,by rw [hP]; exact inf_le_left.trans hST₁⟩
    hUorbit t ht hKt x hx (h.conjugate_le hxR) hnc

/-- C.5.9 for the original alternating-five block; no reduced marked setup is assumed. -/
theorem alternating_reduced_conditions (T : Sylow 2 G) {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (H R K L T₁ : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (h : AlternatingPairSetup R K L)
    (hH : H = (K ⊔ L) ⊔ (T : Subgroup G)) (hHe : H ∈ Chapter1.He G)
    (hcoreU : H.pCoreIn 2 ≤ centralizer (sourceModule K : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (sourceModule K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2) (hNK : T₁ ≤ normalizer (K : Set G))
    (hUorbit : sourceModule K ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let A := K ⊔ T₁
    let Y := normalizer (T₁ : Set G)
    A ∈ Chapter1.He G ∧ IsSQTK 𝒦 A ∧ (pResidual 2 A).map A.subtype = K ∧
      (∃ P : Sylow 2 A, (P : Subgroup A).map A.subtype = T₁ ∧ ChapterB.IsMinimalParabolicOver P ⊤) ∧
      (T₁.subgroupOf Y).Normal ∧
      ∀ N : Subgroup G, N ≤ T₁ → Y ≤ normalizer (N : Set G) →
        A ≤ normalizer (N : Set G) → N = ⊥ := by
  have hnU : normalizer (K : Set G) ≤ normalizer (sourceModule K : Set G) :=
    normalizer_le_normalizer_characteristic_image K (blockU K)
  have hST₁ : ChapterB.baumann R ≤ T₁ := by
    rw [hT₁]
    exact le_inf (inf_le_left.trans hRT) (h.normalizes.trans hnU)
  have hP : (h.sylow : Subgroup K).map K.subtype ≤ T₁ := by
    rw [h.sylow_image,hT₁]
    exact le_inf (inf_le_left.trans hRT) (inf_le_right.trans (K.le_normalizer.trans hnU))
  have hs : (ChapterB.baumann R).map (MulAut.conj x⁻¹).toMonoidHom = ChapterB.baumann R :=
    mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hxR))
  exact source_reduced_conditions T hG H K L T₁ (ChapterB.baumann R) hH hHe hcoreU hT₁ hhalf
    (Or.inr (Or.inr h.block)) hNK hST₁ (h.core.le.trans inf_le_right) ⟨h.sylow,hP⟩
    hUorbit t ht hKt x hx ((map_mono h.module_le).trans_eq hs) hnc
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
