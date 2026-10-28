module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowComponents
public import Theory.GroupTheory.CComponent.ProperQuotient
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender

/-!
# The proper quotient embedding at the smaller changed Sylow

When T₀ is Sylow in G₀T₀, its two-core normalizes L₂. Thus the proper
containing-component embedding remains strict in the actual quotient
by O₂(G₀T₀). The source local-family condition maps to the same quotient,
with the image of T₀ as its Sylow subgroup. The proved rank-one
non-enlargement theorem excludes every Bender containing model, using
the canonical equivalence from the component's intrinsic two-core quotient.

The final theorem applies this to the previously constructed changed
Sylow, keeping both its DT₀ action and the ambient-Sylow alternative.
The remaining model sieve and the larger-Sylow exclusion stay with
qt-d-1222-rankone-cartan-local-to-global; this module does not assert the
final cubic-plane or normalization conclusion.
Source: Aschbacher--Smith A.3.12, pp.47--48, and 5.2.2, p.648.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- At the smaller Sylow, strict overcomponent containment survives the
literal quotient by the two-core of the local overgroup. -/
theorem LocalData.right_image_lt
    {T : Sylow 2 G} {L W H B D L₂ X K : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D L₂) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T L₂) X)
    (hRX : L₂ ≤ X) (hKX : K ≤ X) (hRK : L₂ < K)
    (hK : (K.subgroupOf X).IsCComponent) :
    (L₂.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) <
      (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) := by
  obtain ⟨P,hP⟩ := hSyl
  have hTX : normalizingSylow T L₂ ≤ X := hP ▸ map_subtype_le (P : Subgroup X)
  have hlocal : L₂.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T L₂).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  let := Chapter1.mem_L_isPerfect hlocal
  have hlt : L₂.subgroupOf X < K.subgroupOf X := by
    apply (map_lt_map_iff_of_injective X.subtype_injective).mp
    simpa only [map_subgroupOf_eq_of_le hRX, map_subgroupOf_eq_of_le hKX] using hRK
  have hne : L₂.subgroupOf X ≠ ⊥ := by
    intro he
    apply hlocal.1.ne_bot
    simp only [he, bot_subgroupOf]
  apply hK.map_lt_of_kernel_normalizes hlt hne
  rw [← subgroupOf_normalizer_eq hRX]
  intro x hx
  have hc : X.pCoreIn 2 ≤ normalizingSylow T L₂ := hP ▸ pCoreIn_le_sylow X P
  exact (hc (mem_map_of_mem X.subtype hx)).2

/-- The small changed-Sylow branch gives a proper marked local embedding
in the source two-core quotient, together with relative normality upstairs. -/
theorem LocalData.source_overcomponent_quotient
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T L₂)
      (generated L H D L₂ ⊔ normalizingSylow T L₂)) :
    let X := generated L H D L₂ ⊔ normalizingSylow T L₂
    let q := QuotientGroup.mk' (pCore 2 X)
    ∃ K : Subgroup G, L₂ < K ∧ K ≤ X ∧
      (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
      (L₂.subgroupOf X).map q < (K.subgroupOf X).map q ∧
      ∃ P : Sylow 2 (X ⧸ pCore 2 X),
        (P : Subgroup (X ⧸ pCore 2 X)) = ((normalizingSylow T L₂).subgroupOf X).map q ∧
        (L₂.subgroupOf X).map q ∈ ChapterA.Section03.localCComponents P := by
  dsimp only
  let X := generated L H D L₂ ⊔ normalizingSylow T L₂
  let q := QuotientGroup.mk' (pCore 2 X)
  obtain ⟨K,hRK,hKX,hK,hKn,_⟩ := d.source_overcomponent h hH c hd hz
  have hRX : L₂ ≤ X := le_sup_left.trans (le_sup_right.trans le_sup_left)
  have hlocal : L₂.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T L₂).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf le_sup_right hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  refine ⟨K,hRK,hKX,hK,hKn,d.right_image_lt h hH hSyl hRX hKX hRK hK,?_⟩
  obtain ⟨P,hP⟩ := hSyl
  have he : (P : Subgroup X) = (normalizingSylow T L₂).subgroupOf X := by
    apply (map_injective X.subtype_injective)
    rw [map_subgroupOf_eq_of_le (show normalizingSylow T L₂ ≤ X from le_sup_right)]
    exact hP
  refine ⟨P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X)), ?_, ?_⟩
  · change (P : Subgroup X).map q = _
    rw [he]
  · change (L₂.subgroupOf X).map q ∈ ChapterA.Section03.localCComponents ((P : Subgroup X).map q)
    rw [he]
    exact Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hlocal

/-- The actual containing quotient cannot be a Bender model: the proved
rank-one non-enlargement theorem would collapse the strict marked embedding. -/
theorem LocalData.source_overcomponent_nonBender
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T L₂)
      (generated L H D L₂ ⊔ normalizingSylow T L₂)) :
    let X := generated L H D L₂ ⊔ normalizingSylow T L₂
    let q := QuotientGroup.mk' (pCore 2 X)
    ∃ K : Subgroup G, L₂ < K ∧ K ≤ X ∧
      (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
      (L₂.subgroupOf X).map q < (K.subgroupOf X).map q ∧
      ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) := by
  dsimp only
  obtain ⟨K,hRK,hKX,hK,hKn,hlt,P,_,hlocal⟩ :=
    d.source_overcomponent_quotient h hH c hd hz hSyl
  refine ⟨K,hRK,hKX,hK,hKn,hlt,?_⟩
  intro hm
  let X := generated L H D L₂ ⊔ normalizingSylow T L₂
  let q := QuotientGroup.mk' (pCore 2 X)
  let e := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  have hm' : ClassificationModels.IsBenderModel ((K.subgroupOf X).map q) :=
    hm.of_mulEquiv ((cComponentTwoCoreQuotientEquiv hK).symm.trans e)
  let := pCore_isNilpotent (p := 2) (G := X)
  exact hlt.ne (ChapterA.Section03.SourceEmbeddings.eq_of_bender_containing_component
    P hlocal (hK.map_quotient (pCore 2 X)) hlt.le hm')

/-- Retain the actual changed-Sylow action. The small branch now supplies
its proper quotient embedding; the larger branch is an ambient Sylow. -/
theorem LocalData.changedSylow_component_dichotomy
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥) :
    ∃ P : Sylow 2 (extension T L H B D L₂),
      let T₁ := (P : Subgroup (extension T L H B D L₂)).map (extension T L H B D L₂).subtype
      normalizingSylow T L₂ ≤ T₁ ∧
      T₁ ≤ normalizer ((D ⊔ normalizingSylow T L₂ : Subgroup G) : Set G) ∧
      ((T₁ = normalizingSylow T L₂ ∧
        let X := generated L H D L₂ ⊔ normalizingSylow T L₂
        ∃ K : Subgroup G, L₂ < K ∧ K ≤ X ∧
          (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
          (L₂.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) <
            (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) ∧
          ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K)) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) := by
  obtain ⟨_,_,P,hTP,_,hD,_,hcases⟩ := d.changedSylow_action h hH c hd hz
  refine ⟨P,hTP,hD,?_⟩
  rcases hcases with he | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T L₂)
        (generated L H D L₂ ⊔ normalizingSylow T L₂) :=
      (Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left)
    obtain ⟨K,hRK,hKX,hK,hKn,hlt,hm⟩ := d.source_overcomponent_nonBender h hH c hd hz hSyl
    exact Or.inl ⟨he,K,hRK,hKX,hK,hKn,hlt,hm⟩
  · exact Or.inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
