module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSourceSelection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowBinaryHall
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowJanko

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicCover

/-!
# Containing-component exclusions for the actual source-selected prime pair

The source selection retains either an actual H-component or the intrinsic
classical residual field of its selected parabolic. This discharges the
source alternatives in the Hall-rank exclusion of every rank-two containing
component, including binary triality. The same selected pair also excludes
J₁: in the non-A₅ parabolic row the binary right quotient supplies the exact
four-model embedding input, without asserting full original-Sylow membership.

An A₅ right quotient forces the actual escaping prime to be five in every
source row. Hence neither alternating-seven covering model can contain it
at the smaller changed Sylow, and the original left degree cannot be two.
The final theorem constructs the source pair and applies these exclusions to
its actual changed-Sylow witness, keeping strictness in the literal quotient
by O₂(G₀T₀) and relative component normality.

The zero-core F.1.1 branch and the larger ambient-Sylow branch remain explicit.
Marked zero-core recognition, the remaining containing families, higher-field
reduction and full normalization remain with the same local-to-global owner.
Source: Aschbacher–Smith A.3.12, 5.1.10–13 and 5.2.2,
printed pp.47–48,634–638,647–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- A proper containing J₁ quotient is impossible for a non-A₅ right factor
with one of the literal four quotient models. Only smaller-Sylow local
membership is used; the factor need not be a component of H. -/
theorem LocalData.nonA5_model_not_janko_container
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hmodel : Chapter1.Section02.NonnormalCComponentModel (R ⧸ pCore 2 R))
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R < K)
    (hK : (K.subgroupOf X).IsCComponent) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  rintro ⟨e⟩
  obtain ⟨S,hS⟩ := hSyl
  have hTX : normalizingSylow T R ≤ X := hS ▸ map_subtype_le (S : Subgroup X)
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  have hl : R.subgroupOf X ∈ ChapterA.Section03.localCComponents S := by
    rw [heS]
    exact ((Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp
      ⟨hRX,d.right_mem_local_family h hH⟩).1
  let eR := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hRX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hRX))
  let eK := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  have he := Chapter1.Section02.MovedMaximality.eq_of_janko_quotient S hl hK
    (comap_mono hRK.le) (hmodel.of_mulEquiv eR)
    (fun hh => hnot (hh.of_mulEquiv eR.symm)) (eK.trans e)
  have hh := congrArg (map X.subtype) he
  rw [map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hKX] at hh
  exact hRK.ne hh

/-- The actual source alternative excludes every rank-two containing component
at the smaller changed Sylow, including the binary triality endpoint. -/
theorem LocalData.selected_source_not_rankTwo_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hs : SelectedSourceModels H R)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) := by
  rcases hs with hC | ⟨f,hf,_,hm⟩
  · exact d.component_source_not_rankTwo_container h hH c hd hz hC hSyl hRK hKX hK hKn
  · exact d.classical_residual_not_rankTwo_container h hH hgen c hd hz hSyl hRK hKX hK hKn hf hm

/-- Both actual components and selected diagram parabolics exclude J₁, with
their intrinsic quotient markings and the same strict embedding. -/
theorem LocalData.selected_source_not_janko_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hs : SelectedSourceModels H R)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  rcases hs with hC | ⟨f,hf,hr,_⟩
  · exact d.component_source_not_janko_container h hH c hd hz hC hSyl hRK hKX hK hKn
  · by_cases hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4
    · exact d.A5_right_not_janko_container h hH c hd hz hA5 hSyl hRK.le hKX hK hKn
    · exact d.nonA5_model_not_janko_container h hH (.linear_even f (by omega) hr) hA5 hSyl
        (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK hK

/-- An A₅ selected right factor forces the escaping actor to have order five
in every original source row, including the nonprojective linear cover. -/
theorem LocalData.selected_A5_actor_prime
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hs : SelectedSourceModels H R)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) : p = 5 := by
  rcases hs with hC | ⟨f,hf,_,hm⟩
  · exact d.A5_component_actor_prime h hH c hd hz hC hA5
  · rcases hm with hm | hm | hm
    · exact (d.A5_right_not_linear_residual hH.1.1.2
        (d.right_lt_residual hH.1.1.2 c hd hz) hf hthree hA5 hm).elim
    · exact (d.A5_right_specialLinear_prime h hH c hd hz hf hm hA5).2
    · exact d.A5_right_symplectic_residual_actor_prime h hH hgen c hd hf hm hA5

/-- The selected A₅ factor excludes both alternating-seven covering models: a
containing model forces the same escaping actor to have order three. -/
theorem LocalData.selected_A5_not_alternating_seven_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hs : SelectedSourceModels H R)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternating (K ⧸ pCore 2 K) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (K ⧸ pCore 2 K) 7) := by
  intro hm
  have hp := d.selected_A5_actor_prime h hH hgen c hd hz hs hthree hA5
  have hq := d.source_overcomponent_alternating_seven_prime h hH c hd hz hSyl hRK.le hKX hK hKn hm
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- Construct the source pair and apply the completed containing-model sieve
to its actual changed Sylow. The zero-core and ambient-Sylow alternatives
remain genuine source obligations, not assumed recognition outputs. -/
theorem source_prime_pair_changedSylow_exclusions
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
              (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 →
                ¬ (IsAlternating (K ⧸ pCore 2 K) 7 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 7)) ∧
              (¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 →
                ∀ q : ℕ, q.Prime → Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 q)) ∨
            ∃ U : Sylow 2 G, (U : Subgroup G) = T₁))) := by
  obtain ⟨R,d,hs⟩ := source_prime_pair_selected_models h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  by_cases hz : (generated L H D R).pCoreIn 2 = ⊥
  · exact Or.inl ⟨hz,d.hypothesisF11 h hH c hd hz⟩
  right
  have hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2 := by
    intro hm
    have hp := d.selected_A5_actor_prime h hH hgen c hd hz hs hthree hm
    refine ⟨hp,?_⟩
    intro hn
    have hdiv : p ∣ 2 ^ n - 1 := by
      rw [←c.left_card h.linear h.sylow_normalizes,←hd.card]
      exact card_dvd_of_le hd.le_cartan
    norm_num [hp,hn] at hdiv
  refine ⟨hz,d.prime_actor_not_normalizes_right h hH c hd hz,
    d.normalizingSylow_index hH.1.1.2 c hd hz,hA5,?_⟩
  obtain ⟨P,hTP,hD,hcases⟩ := d.changedSylow_small_exclusions h hH c hd hz
  refine ⟨P,hTP,hD,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,_⟩ | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    refine Or.inl ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,
      d.selected_source_not_rankTwo_container h hH hgen c hd hz hs hSyl hRK hKX hK hKn,
      d.selected_source_not_janko_container h hH c hd hz hs hSyl hRK hKX hK hKn,?_,?_⟩
    · intro hm
      exact d.selected_A5_not_alternating_seven_container h hH hgen c hd hz hs hthree hm
        hSyl hRK hKX hK hKn
    · intro hm q hq ho
      exact d.source_overcomponent_not_primePSL2 h hH hSyl
        (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK hK hm hq ho
  · exact Or.inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
