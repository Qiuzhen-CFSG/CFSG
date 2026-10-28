module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSourceSieve
public import Theory.SpecificGroups.PSL2.TwentyFiveSolvableActors
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuadraticPSL2
public import Theory.SpecificGroups.SL2.SmallOddComparisons

/-!
# The PSL₂(25) container at the smaller changed Sylow

In the literal quotient X/O₂(X), for X=G₀T₀, the proper right local factor
inside a PSL₂(25) component is PSL₂(5). Restricting the actual quotient map
and removing its two-group kernel identifies the original R/O₂(R) with
PSL₂(4). Thus the original Hall intersection B∩R has order three.

The prime actor is faithful on the containing component. Its solvable
Sylow join rules out order five by the intrinsic PSL₂(25) calculation.
In the remaining cubic case B∩R centralizes D, and their join has action
image of order at most three because Out(PSL₂(25)) is a two-group and
nine does not divide its order. The marked cubic fills this image, so the
perfect-subgroup kernel theorem forces D to normalize R, a contradiction.

The final theorem applies this exclusion to the same constructed source
pair and changed Sylow as the preceding sieve, retaining every earlier
exclusion. Marked zero-core recognition, the other containing rows,
larger-Sylow assembly and higher-field reduction remain with the original
local-to-global owner. No equality of field degrees or ambient Sylows is
assumed, and the authorized h513 input remains unchanged.
Source: Aschbacher–Smith A.3.12(8), A.3.14,5.1.13 and5.2.2,
printed pp.47–50,636–638,648–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02.LocalModels
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
/-- A PSL₂(25) containing quotient forces the actual escaping actor to be cubic. -/
theorem LocalData.source_overcomponent_twentyFive_prime
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25) :
    p = 3 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rcases hd.prime with hp | hp
  · exact hp
  subst p
  exfalso
  let X := generated L H D R ⊔ normalizingSylow T R
  let q := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map q
  let Kbar := (K.subgroupOf X).map q
  let Dbar := (D.subgroupOf X).map q
  have hRX : R ≤ X := le_sup_left.trans (le_sup_right.trans le_sup_left)
  have hDX : D ≤ X := le_sup_left.trans le_sup_left
  have hTX : normalizingSylow T R ≤ X := le_sup_right
  obtain ⟨hc,hdis,_⟩ := d.right_quotient_prime_orbit h hH c hd hz hRX hDX hSyl
  obtain ⟨S,hS⟩ := hSyl
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  let : (K.subgroupOf X).Normal := hKn
  let : Kbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let : Group.IsPerfect Kbar := (hK.map_quotient (pCore 2 X)).perfect
  have hdC : Disjoint Dbar (centralizer (Kbar : Set (X ⧸ pCore 2 X))) :=
    hdis.mono_right ((centralizer_le (map_mono (comap_mono hRK))).trans
      (centralizer_le_normalizer (Rbar : Set (X ⧸ pCore 2 X))))
  have hsol : Group.IsSolvable (Dbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) : Subgroup _) := by
    let := d.actor_join_solvable h hH c hd
    let : Group.IsSolvable ((D ⊔ normalizingSylow T R).subgroupOf X) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (sup_le hDX hTX)).toMonoidHom)
        (subgroupOfEquivOfLe (sup_le hDX hTX)).injective
    have hs : Group.IsSolvable (((D ⊔ normalizingSylow T R).subgroupOf X).map q) :=
      Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
    change Group.IsSolvable (Dbar ⊔ (S : Subgroup X).map q : Subgroup _)
    rw [heS]
    rw [subgroupOf_sup hDX hTX,Subgroup.map_sup] at hs
    exact hs
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  exact Theory.PSL2.TwentyFive.no_five_actor Kbar Dbar hF (eK.trans e) P hc hdC hsol


/-- A proper local factor inside PSL₂(25) has the literal A₅ two-core quotient. -/
theorem LocalData.source_overcomponent_twentyFive_right_section
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R < K)
    (hK : (K.subgroupOf X).IsCComponent)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 := by
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
  have hm' : ClassicalGroup.IsPSL Kbar 2 (5 ^ 2) := hm.of_mulEquiv eK
  obtain ⟨_,F,_,_,hF,⟨e⟩⟩ := ChapterA.Section03.SourceEmbeddings.proper_quadraticPSL2_models
    P hlocalbar (hK.map_quotient (pCore 2 X)) hlt.le hlt.ne
    (by decide : Nat.Prime 5) (by decide : Odd 5) hm'
  let e4 := e.trans (Matrix.ProjectiveSpecialLinearGroup.cardFiveEquivFour hF)
  have hz : pCore 2 Rbar = ⊥ := by
    apply (map_eq_bot_iff_of_injective (pCore 2 Rbar) (f := e4.toMonoidHom) e4.injective).mp
    rw [pCore_map_iso 2 e4,Atlas.RankOneFieldAutomorphisms.psl_twoCore_eq_bot]
  let r := q.subgroupMap (R.subgroupOf X)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eRX := (subgroupOfEquivOfLe hRX).symm
  let e₁ := QuotientGroup.congr _ _ eRX (pCore_map_iso 2 eRX)
  let e₂ := r.quotientPCoreEquivOfSurjective (q.subgroupMap_surjective _) hr
  let e₃ : (Rbar ⧸ pCore 2 Rbar) ≃* Rbar :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  exact ⟨GaloisField 2 2,inferInstance,inferInstance,
    by rw [GaloisField.card 2 2 (by decide)]; norm_num,
    ⟨e₁.trans (e₂.trans (e₃.trans e4))⟩⟩

/-- The cubic actor joins the actual right Hall subgroup in a three-group.
The PSL₂(25) action image has order at most three, forcing normalization. -/
theorem LocalData.A5_right_not_twentyFive_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25 := by
  intro hm
  have hp := d.source_overcomponent_twentyFive_prime h hH c hd hz hSyl hRK hKX hK hKn hm
  subst p
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let X := generated L H D R ⊔ normalizingSylow T R
  let := Chapter1.mem_L_isPerfect (d.right_mem_local_family h hH)
  have hXK : X ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKX).mp hKn
  have hDK : D ≤ normalizer (K : Set G) :=
    (le_sup_left.trans le_sup_left).trans hXK
  obtain ⟨S,hS⟩ := hSyl
  have hQ : K.pCoreIn 2 ≤ normalizer (R : Set G) :=
    (pCoreIn_mono_of_normalizes hKX hXK).trans
      ((hS ▸ pCoreIn_le_sylow X S).trans inf_le_right)
  have hC : Nat.card (B ⊓ R : Subgroup G) = 3 := by
    simpa using d.right_cartan_card c (m := 2) hA5
  have hCD : B ⊓ R ≤ centralizer (D : Set G) :=
    inf_le_left.trans (c.centralizes_prime_actor h hd)
  have hA : D ⊔ (B ⊓ R) ≤ normalizer (K : Set G) :=
    sup_le hDK ((inf_le_right.trans hRK).trans K.le_normalizer)
  have hthree : IsPGroup 3 (D ⊔ (B ⊓ R) : Subgroup G) :=
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hd.card)).to_sup_of_normal_left'
      (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hC))
      (hCD.trans (centralizer_le_normalizer (D : Set G)))
  have hn := Theory.PSL2.TwentyFive.cartan_normalizes_perfect_subgroup
    R K (D ⊔ (B ⊓ R)) (B ⊓ R) hRK hA le_sup_right inf_le_right hQ hthree hC hF e
  exact d.prime_actor_not_normalizes_right h hH c hd hz (le_sup_left.trans hn)

/-- The entire PSL₂(25) containing row is impossible at the smaller changed
Sylow; no A₅ or source-component marking is an additional premise. -/
theorem LocalData.source_overcomponent_not_twentyFive
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25 := by
  intro hm
  have hA5 := d.source_overcomponent_twentyFive_right_section h hH hSyl
    (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK hK hm
  exact d.A5_right_not_twentyFive_container h hH c hd hz hA5 hSyl hRK.le hKX hK hKn hm

/-- Apply the PSL₂(25) exclusion to the same constructed pair and changed
Sylow, retaining all previously proved containing-model exclusions. -/
theorem source_prime_pair_containing_exclusions
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
              (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 →
                ¬ (IsAlternating (K ⧸ pCore 2 K) 7 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 7)) ∧
              (¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 →
                ∀ q : ℕ, q.Prime → Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 q)) ∨
            ∃ U : Sylow 2 G, (U : Subgroup G) = T₁))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_changedSylow_exclusions h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,hseven,hprime⟩ | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    exact .inl ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,
      d.source_overcomponent_not_twentyFive h hH c hd hz hSyl hRK hKX hK hKn,hseven,hprime⟩
  · exact .inr ha
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
