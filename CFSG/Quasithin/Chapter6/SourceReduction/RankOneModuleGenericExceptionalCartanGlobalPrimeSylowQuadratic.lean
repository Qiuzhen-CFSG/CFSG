module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowBinaryLinear
public import CFSG.Quasithin.ChapterF.Section01.RankOneOddPrime

/-!
# All odd PSL₂ containers at the smaller changed Sylow

In the literal quotient X/O₂(X), X=G₀T₀, a proper local factor in
PSL₂(q²), q an odd prime, is PSL₂(q). The source rank-one comparison
forces q=5. The previously proved PSL₂(25) exclusion therefore removes
this whole family. The proof uses the original restricted quotient map,
its two-group kernel and the actual intrinsic two-core of the image.
It does not assume an alternating-five marking of the right factor.

The final theorem retains the same selected source pair, both Hall
markings and all earlier exclusions, and rules out both odd PSL₂ field
exponents from Theorem C. Its Chapter12 application uses the original
chosen module. Remaining containing families, larger changed-Sylow
assembly, compatible zero-core recognition and higher-field normalization
remain with the original local-to-global owner; h513 is unchanged.
Source: Aschbacher–Smith A.3.12(8), F.1.1 and 5.2.2,
printed pp.47–48,259,648–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- A proper local rank-one factor in an odd quadratic-prime PSL₂ container
forces the defining prime to be five, preserving the intrinsic two-core quotients. -/
theorem LocalData.source_overcomponent_quadratic_parameter
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n q₀ : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R < K)
    (hK : (K.subgroupOf X).IsCComponent)
    (hq : q₀.Prime) (ho : Odd q₀)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (q₀ ^ 2)) : q₀ = 5 := by
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
  have hlt : Rbar < Kbar := d.right_image_lt h hH ⟨S,hS⟩ hRX hKX hRK hK
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  have hm' : ClassicalGroup.IsPSL Kbar 2 (q₀ ^ 2) := hm.of_mulEquiv eK
  obtain ⟨hgt,hsmall⟩ := ChapterA.Section03.SourceEmbeddings.proper_quadraticPSL2_models
    P hlocalbar (hK.map_quotient (pCore 2 X)) hlt.le hlt.ne hq ho hm'
  have hns : ¬ Group.IsSolvable Rbar := by
    intro hs
    let := hs
    exact hlocalbar.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (show Rbar ≤ Rbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) from le_sup_left)).toMonoidHom)
        (subgroupOfEquivOfLe le_sup_left).injective)
  have hs : IsSimpleGroup Rbar := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hsmall
    exact e.isSimpleGroup_congr.mpr
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega))
  let := hs
  have hz : pCore 2 Rbar = ⊥ := by
    apply (inferInstance : (pCore 2 Rbar).Normal).eq_bot_or_eq_top.resolve_right
    intro he
    let : Group.IsNilpotent (⊤ : Subgroup Rbar) := he ▸ pCore_isNilpotent (p := 2) (G := Rbar)
    exact hns (Group.isSolvable_of_surjective
      (f := (topEquiv (G := Rbar)).toMonoidHom) (topEquiv (G := Rbar)).surjective)
  let r := q.subgroupMap (R.subgroupOf X)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eRX := (subgroupOfEquivOfLe hRX).symm
  let e₁ := QuotientGroup.congr _ _ eRX (pCore_map_iso 2 eRX)
  let e₂ := r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr
  let e₃ : (Rbar ⧸ pCore 2 Rbar) ≃* Rbar :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  have hrank := d.right_quotient.of_equiv (e₁.trans (e₂.trans e₃)).symm
  exact hrank.odd_prime_parameter hns hq ho hgt hsmall

/-- All odd quadratic-prime PSL₂ containers reduce to the already excluded
PSL₂(25), using the actual smaller local quotient rather than an A₅ premise. -/
theorem LocalData.source_overcomponent_not_odd_quadratic
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p q : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hq : q.Prime) (ho : Odd q) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (q ^ 2) := by
  intro hm
  have he := d.source_overcomponent_quadratic_parameter h hH hSyl
    (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK hK hq ho hm
  subst q
  exact d.source_overcomponent_not_twentyFive h hH c hd hz hSyl hRK hKX hK hKn hm

open Chapter1.Section02.LocalModels

/-- The actual selected source pair and changed Sylow exclude the higher
binary-linear and alternating-eight containers and every odd PSL₂ row in Theorem C,
retaining every earlier exclusion. -/
theorem source_prime_pair_odd_linear_containing_exclusions
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
                ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (q ^ k))) ∨
            ∃ U : Sylow 2 G, (U : Subgroup G) = T₁))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_binary_containing_exclusions h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,hseven,hprime,hbinary⟩ | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    refine .inl ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,hseven,hprime,hbinary,?_⟩
    intro q k hq ho hk
    rcases hk with rfl | rfl
    · simpa only [pow_one] using hprime q hq ho
    · exact d.source_overcomponent_not_odd_quadratic h hH c hd hz hSyl hRK hKX hK hKn hq ho
  · exact .inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
