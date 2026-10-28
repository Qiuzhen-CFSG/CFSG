module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowQuadratic
public import CFSG.Quasithin.ChapterF.Section01.RankOneMathieuEleven

/-!
# The M₁₁ containing component at the smaller changed Sylow

The source right factor remains a genuine local C-component after mapping
into X/O₂(X). Intersect the full normalizing Sylow with its containing
component and transfer both subgroups through the actual M₁₁ isomorphism.
The restricted quotient map has two-group kernel, so the intrinsic right
two-core quotient is preserved. The M₁₁ rank-one section theorem then
excludes this row without an assumed A₅ marking or a trivial-kernel premise.

The final theorem applies this exclusion to the constructed source pair and
its changed Sylow, retaining every preceding exclusion and both original
Hall markings. Remaining containing families, larger changed-Sylow assembly,
compatible zero-core recognition and higher-field reductions remain with
the original local-to-global owner; the authorized h513 is unchanged.
Source: Aschbacher–Smith A.3.12 and 5.2.2, printed pp.47–48 and648–649
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- A full normalizing Sylow and the actual source rank-one quotient exclude
M₁₁ as a containing component, before any original and changed Sylow are identified. -/
theorem LocalData.source_overcomponent_not_mathieu_eleven
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R ≤ K)
    (hK : (K.subgroupOf X).IsCComponent) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M11) := by
  rintro ⟨e⟩
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
  have hRKbar : Rbar ≤ Kbar := map_mono (comap_mono hRK)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  obtain ⟨Q,hQ,hU⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    P hlocalbar hRKbar (hK.map_quotient (pCore 2 X)).subnormal
  let U := Rbar.subgroupOf Kbar
  have hnU : (Q : Subgroup Kbar) ≤ normalizer (U : Set Kbar) := by
    rw [hQ,←subgroupOf_normalizer_eq hRKbar]
    exact comap_mono hn
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let a : Kbar ≃* Sporadic.Mathieu.M11 :=
    ((cComponentTwoCoreQuotientEquiv hK).symm.trans ec).trans e
  let C := U.map a.toMonoidHom
  let b : Rbar ≃* C := (subgroupOfEquivOfLe hRKbar).symm.trans (a.subgroupMap U)
  let : Group.IsPerfect (R.subgroupOf X) := Chapter1.mem_L_isPerfect hlocal
  let : Group.IsPerfect Rbar := Group.IsPerfect.map _
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := b.toMonoidHom) b.surjective
  have hns : ¬ Group.IsSolvable C := by
    intro hs
    let := hs
    let : Group.IsSolvable Rbar := Group.isSolvable_of_isSolvable_injective
      (f := b.toMonoidHom) b.injective
    exact hlocalbar.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show Rbar ≤ Rbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).injective)
  apply ChapterF.Source.MathieuEleven.not_rankOne_quotient
    (Q.mapSurjective (f := a.toMonoidHom) a.surjective) C hns
    ((map_mono hnU).trans (le_normalizer_map a.toMonoidHom))
  let r := q.subgroupMap (R.subgroupOf X)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eRX := (subgroupOfEquivOfLe hRX).symm
  let e₁ := QuotientGroup.congr _ _ eRX (pCore_map_iso 2 eRX)
  let e₂ := r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr
  let e₃ := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  exact d.right_quotient.of_equiv (e₁.trans (e₂.trans e₃)).symm

open Chapter1.Section02.LocalModels

/-- The actual selected source pair excludes M₁₁ at the smaller changed Sylow,
retaining the preceding model exclusions and the literal Hall and quotient markings. -/
theorem source_prime_pair_mathieu_eleven_containing_exclusions
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
              ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M11)) ∨
            ∃ U : Sylow 2 G, (U : Subgroup G) = T₁))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_odd_linear_containing_exclusions h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,hseven,hprime,hbinary,hodd⟩ | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    exact .inl ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,hseven,hprime,hbinary,hodd,
      d.source_overcomponent_not_mathieu_eleven h hH hSyl
        (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK.le hK⟩
  · exact .inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
