module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowRudvalis
public import CFSG.Quasithin.ChapterF.Section01.RankOneHeldLocal

/-!
# Excluding Held at the smaller changed Sylow

Pass the actual selected right local component through X/O₂(X), then restrict
its Sylow marking to the containing component. The quotient transport keeps
its intrinsic two-core quotient a source rank-one model. The native Held
local theorem excludes that configuration. The original Hall markings and
all previous containing exclusions survive the same selected-pair construction.

This closes the Held containing row of original 5.2.2; the remaining families,
larger changed Sylow, zero-core recognition, and higher-field normalization
remain with the local-to-global assembly, with authorized h513 explicit.
Source: Aschbacher–Smith A.3.12, 5.1.12–13 and 5.2.2,
pp.47–48, 635–638 and 648–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The actual containing component cannot have Held as its two-core quotient.
The restriction keeps the right local subgroup and its intrinsic quotient. -/
theorem LocalData.source_overcomponent_not_held
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R < K)
    (hK : (K.subgroupOf X).IsCComponent)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Held.He)) :
    False := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map q
  let Kbar := (K.subgroupOf X).map q
  obtain ⟨S,hS⟩ := hSyl
  have hTX : normalizingSylow T R ≤ X := hS ▸ map_subtype_le (S : Subgroup X)
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hlocal : R.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T R).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  have hlocalbar : Rbar ∈ ChapterA.Section03.localCComponents P := by
    change Rbar ∈ ChapterA.Section03.localCComponents ((S : Subgroup X).map q)
    rw [heS]
    exact Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hlocal
  have hn : (P : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (Rbar : Set (X ⧸ pCore 2 X)) := by
    change (S : Subgroup X).map q ≤ _
    rw [heS]
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRX]
    exact comap_mono (show normalizingSylow T R ≤ normalizer (R : Set G) from inf_le_right)
  have hRKbar : Rbar ≤ Kbar := map_mono (comap_mono hRK.le)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  obtain ⟨Q,hQ,hU⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    P hlocalbar hRKbar (hK.map_quotient (pCore 2 X)).subnormal
  let U := Rbar.subgroupOf Kbar
  have hnU : (Q : Subgroup Kbar) ≤ normalizer (U : Set Kbar) := by
    rw [hQ,←subgroupOf_normalizer_eq hRKbar]
    exact comap_mono hn
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) :=
    (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  let r := q.subgroupMap (R.subgroupOf X)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eRX := (subgroupOfEquivOfLe hRX).symm
  let e₁ := QuotientGroup.congr _ _ eRX (pCore_map_iso 2 eRX)
  let e₂ := r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr
  let b := (subgroupOfEquivOfLe hRKbar).symm
  let e₃ := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let eR : (R ⧸ pCore 2 R) ≃* (U ⧸ pCore 2 U) := e₁.trans (e₂.trans e₃)
  exact ChapterF.Source.HeldLocal.not_rankOne (eK.trans hm.some) Q U hU hnU
    (d.right_quotient.of_equiv eR.symm)

open Chapter1.Section02.LocalModels

/-- The constructed source pair excludes the Held container,
retaining both Hall markings and all previous containing-model exclusions. -/
theorem source_prime_pair_held_containing_exclusion
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
              ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M12) ∧
              ¬ (Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) ∨
                Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) ∨
                Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24)) ∧
              ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) ∧
              ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.HS.Carrier) ∧
              ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Rudvalis.Model) ∧
              ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Held.He)) ∨
            ∃ U : Sylow 2 G, (U : Subgroup G) = T₁))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_rudvalis_containing_exclusion h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,hseven,hprime,hbinary,hodd,hm11,hm12,hm,hj2,hhs,hru⟩ | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    refine .inl ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,hseven,hprime,hbinary,hodd,hm11,hm12,hm,hj2,hhs,hru,?_⟩
    intro hhe
    exact d.source_overcomponent_not_held h hH hSyl
      (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK hK hhe
  · exact .inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
