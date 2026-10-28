module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSevenSection
public import CFSG.Quasithin.ChapterF.Section01.RankOneBinaryLinear
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryIntrinsicQuotients

/-!
# Higher binary-linear containers at the smaller changed Sylow

The actual right factor is a local C-component for the normalizing Sylow.
If its containing component has quotient PSL₄(2) or PSL₅(2), the intrinsic
binary local-component calculation identifies R/O₂(R) with GLₘ(2),
3 ≤ m ≤ 5. The rank-one Sylow-normalizer property contradicts the binary
flag geometry. This uses the literal quotient maps and requires neither
quasisimplicity of R nor its being an actual component of H.

The proved exceptional isomorphism excludes A₈ as well. The final theorem
applies these exclusions to the same source pair and changed Sylow as the
previous sieve, preserving both Hall markings and every earlier exclusion.

The remaining containing families, larger changed-Sylow argument, marked
zero-core recognition, higher-field reduction and full normalization remain
with the original local-to-global owner. The authorized h513 is unchanged.
Source: Aschbacher–Smith A.3.12(4–5), F.1.3(1) and 5.2.2,
printed pp.47–48,260,648–649 (`refs/quasithin.pdf`). Imported binary linear
and exceptional-isomorphism facts retain LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The actual rank-one right quotient excludes both higher binary-linear
containing components, with the intrinsic two-core quotients preserved. -/
theorem LocalData.source_overcomponent_not_binary_linear
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n k : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R ≤ K)
    (hK : (K.subgroupOf X).IsCComponent) (hk : k = 4 ∨ k = 5) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) k 2 := by
  intro hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  obtain ⟨S,hS⟩ := hSyl
  have hTX : normalizingSylow T R ≤ X := hS ▸ map_subtype_le (S : Subgroup X)
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  have hlocal : R.subgroupOf X ∈ ChapterA.Section03.localCComponents S := by
    rw [heS]
    exact ((Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp
      ⟨hRX,d.right_mem_local_family h hH⟩).1
  let eK := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let a := eK.trans ((e.trans (Atlas.fieldEquivPSL k f)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < k)))
  obtain ⟨m,hm,_,⟨b⟩⟩ :=
    ChapterA.Section03.SourceEmbeddings.BinaryIntrinsic.local_twoCore_quotient_of_containing_quotient
      S hlocal (ChapterA.Section03.isCComponent_mem_localCComponents hK)
      (comap_mono hRK) k (by omega) a
  let eR := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hRX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hRX))
  exact d.right_quotient.not_binary_linear hm (eR.symm.trans b)

/-- The two higher binary-linear containers and the isomorphic A₈ row are
incompatible with the selected source rank-one quotient. -/
theorem LocalData.source_overcomponent_not_binary_or_eight
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R ≤ K)
    (hK : (K.subgroupOf X).IsCComponent) :
    ¬ (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2 ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Chapter1.Section02.LocalModels.IsAlternating (K ⧸ pCore 2 K) 8) := by
  intro hh
  rcases hh with hm | hm | hm
  · exact d.source_overcomponent_not_binary_linear h hH hSyl hRX hKX hRK hK (.inl rfl) hm
  · exact d.source_overcomponent_not_binary_linear h hH hSyl hRX hKX hRK hK (.inr rfl) hm
  · obtain ⟨e⟩ := hm
    apply d.source_overcomponent_not_binary_linear h hH hSyl hRX hKX hRK hK (.inl rfl)
    exact ⟨ZMod 2,inferInstance,inferInstance,by simp,
      ⟨e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩

open Chapter1.Section02.LocalModels
/-- The actual selected source pair and changed Sylow exclude the higher
binary-linear and alternating-eight containers, retaining every earlier exclusion. -/
theorem source_prime_pair_binary_containing_exclusions
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R ≤ T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ((T₁ = normalizingSylow T R ∧
            let X := generated L H D R ⊔ normalizingSylow T R
            let q := QuotientGroup.mk' (pCore 2 X)
            ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
              (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
              (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
              ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∧
              ¬ (IsAlternating (K ⧸ pCore 2 K) 5 ∨ IsAlternating (K ⧸ pCore 2 K) 6 ∨
                IsAlternatingCover (K ⧸ pCore 2 K) 6) ∧
              (∀ k : ℕ, 1 ≤ k → ¬ (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨
                IsSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨ IsSU (K ⧸ pCore 2 K) 3 (2 ^ k))) ∧
              ¬ RankTwoTheoremC (K ⧸ pCore 2 K) ∧
              ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) ∧
              ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25 ∧
              ¬ (IsAlternating (K ⧸ pCore 2 K) 7 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 7) ∧
              (∀ q : ℕ, q.Prime → Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 q) ∧
              ¬ (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2 ∨
                ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨ IsAlternating (K ⧸ pCore 2 K) 8)) ∨
            ∃ U : Sylow 2 G, (U : Subgroup G) = T₁))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_alternating_containing_exclusions h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,hseven,hprime⟩ | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    exact .inl ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,hseven,hprime,
      d.source_overcomponent_not_binary_or_eight h hH hSyl
        (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK.le hK⟩
  · exact .inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
