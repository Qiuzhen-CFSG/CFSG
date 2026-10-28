module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowMathieuEleven
public import Theory.Mathieu.M12.SylowOvergroups.Solvable

/-!
# The M₁₂ containing component at the smaller changed Sylow

The full normalizing Sylow makes the right factor a genuine local
C-component of the containing group. Every proper full-Sylow overgroup
of an M₁₂ two-core cover is solvable. Intersecting the original Sylow with
the containing component therefore forces the local factor to equal that
component, contrary to its proper containment. The whole two-core is
retained; no faithfulness or trivial-kernel premise is needed.

The final theorem applies this obstruction to the actual selected source
pair and changed Sylow, preserving all previous exclusions and both Hall
markings. The remaining containing families, larger changed-Sylow assembly,
compatible zero-core recognition and higher-field reductions remain open.
The authorized h513 input is unchanged.
Source: Aschbacher–Smith A.3.12 and 5.2.2, printed pp.47–48 and648–649
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The actual source local component cannot lie properly in an M₁₂
containing component at its full normalizing Sylow. -/
theorem LocalData.source_overcomponent_not_mathieu_twelve
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R < K)
    (hK : (K.subgroupOf X).IsCComponent) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M12) := by
  rintro ⟨e⟩
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
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_solvable_sylow_overgroups
    S hlocal hK (comap_mono hRK.le)
    (Sporadic.Mathieu.M12SmallPair.SylowOvergroups.isSolvable_of_twoCore_quotient (eK.trans e))
  apply hRK.ne
  simpa only [map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hKX] using
    congrArg (map X.subtype) he

open Chapter1.Section02.LocalModels

/-- The actual selected source pair excludes M₁₂ at the smaller changed Sylow,
retaining the preceding model exclusions and the literal Hall and quotient markings. -/
theorem source_prime_pair_mathieu_twelve_containing_exclusions
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
                ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨ IsAlternating (K ⧸ pCore 2 K) 8) ∧
              (∀ q k : ℕ, q.Prime → Odd q → (k = 1 ∨ k = 2) →
                ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (q ^ k)) ∧
              ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M11) ∧
              ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M12)) ∨
            ∃ U : Sylow 2 G, (U : Subgroup G) = T₁))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_mathieu_eleven_containing_exclusions h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,hseven,hprime,hbinary,hodd,hm11⟩ | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    exact .inl ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,hseven,hprime,hbinary,hodd,hm11,
      d.source_overcomponent_not_mathieu_twelve h hH hSyl
        (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK hK⟩
  · exact .inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
