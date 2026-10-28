module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowRee
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SmallAlternating
public import Theory.SpecificGroups.PSL3Two.SolvableSylowOvergroups
public import Theory.SpecificGroups.G2Even.BinaryDerivedSolvableOvergroups
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.Tits.SolvableSylowOvergroups
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock

/-!
# Small containing components at the smaller changed Sylow

The smaller local component remains proper in the literal quotient X/O₂(X).
Any containing model with solvable proper Sylow overgroups would collapse
that embedding. This excludes A₅, A₆, 3.A₆, binary SL₃ and PSL₃, the actual
binary derived symplectic and G₂ carriers, and the Tits group. The same
argument treats every binary special-unitary-three cover.

Combining these endpoints with the previously proved large-field exclusions
reduces the entire rank-two Theorem C list to genuine ³D₄(2). Both linear-three
forms and the special-unitary-three family are excluded for every positive
binary exponent. The final witness retains the actual containing component,
its relative normality, the quotient embedding and the changed-Sylow action.

The binary triality and other remaining containing models, larger-Sylow
argument, source choice, higher-field reduction, zero-core exclusions and
final normalization remain with qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher–Smith A.3.12, pp.47–48, and 5.2.2, pp.648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- A proper containing component cannot have solvable proper Sylow overgroups.
The comparison uses the actual component quotient inside X/O₂(X). -/
theorem LocalData.source_overcomponent_not_solvableSylow
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R < K)
    (hK : (K.subgroupOf X).IsCComponent) :
    ¬ SolvableSylowOvergroups (K ⧸ pCore 2 K) := by
  intro hs
  let q := QuotientGroup.mk' (pCore 2 X)
  obtain ⟨S,hS⟩ := hSyl
  have hTX : normalizingSylow T R ≤ X := hS ▸ map_subtype_le (S : Subgroup X)
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply (map_injective X.subtype_injective)
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  have hlocal : R.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T R).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hlocalbar : (R.subgroupOf X).map q ∈ ChapterA.Section03.localCComponents P := by
    change (R.subgroupOf X).map q ∈ ChapterA.Section03.localCComponents ((S : Subgroup X).map q)
    rw [heS]
    exact Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hlocal
  have hlt := d.right_image_lt h hH ⟨S,hS⟩ hRX hKX hRK hK
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let e : (K.subgroupOf X).map q ≃* (K ⧸ pCore 2 K) :=
    (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  exact hlt.ne (ChapterA.Section03.SourceEmbeddings.eq_of_solvable_sylow_overgroups
    P hlocalbar (hK.map_quotient (pCore 2 X)) hlt.le
    (SolvableSylowOvergroups.of_equiv e hs))

/-- Exclude the small alternating, binary linear, binary derived symplectic,
binary derived G₂ and Tits containing quotients, including the triple cover of A₆. -/
theorem LocalData.source_overcomponent_not_small
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R < K)
    (hK : (K.subgroupOf X).IsCComponent) :
    ¬ (IsAlternating (K ⧸ pCore 2 K) 5 ∨
      IsAlternating (K ⧸ pCore 2 K) 6 ∨
      IsAlternatingCover (K ⧸ pCore 2 K) 6 ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 ∨
      IsSL (K ⧸ pCore 2 K) 3 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Tits.ParrottGroup)) := by
  intro hm
  apply d.source_overcomponent_not_solvableSylow h hH hSyl hRX hKX hRK hK
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm
  · obtain ⟨e⟩ := hm
    exact SolvableSylowOvergroups.of_equiv e (fun _ P _ hP =>
      alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP)
  · obtain ⟨e⟩ := hm
    exact SolvableSylowOvergroups.of_equiv e AlternatingSix.ProperSylowOvergroups.isSolvable
  · obtain ⟨hq,_,⟨e⟩⟩ := hm
    let := hq
    exact SolvableSylowOvergroups.of_central_quotient (QuotientGroup.mk' (center (K ⧸ pCore 2 K)))
      (QuotientGroup.mk'_surjective _) (by simp)
      (SolvableSylowOvergroups.of_equiv e AlternatingSix.ProperSylowOvergroups.isSolvable)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact SolvableSylowOvergroups.of_equiv e
      (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two hF)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact SolvableSylowOvergroups.of_equiv e
      (Matrix.PSL3Two.solvableSylowOvergroups_specialLinear_of_card_two hF)
  · obtain ⟨e⟩ := hm
    exact SolvableSylowOvergroups.of_equiv
      (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
      AlternatingSix.ProperSylowOvergroups.isSolvable
  · obtain ⟨e⟩ := hm
    exact SolvableSylowOvergroups.of_equiv e Atlas.G2.binaryDerived_solvableSylowOvergroups
  · obtain ⟨e⟩ := hm
    exact SolvableSylowOvergroups.of_equiv e Tits.ProperSylowOvergroups.solvableSylowOvergroups

/-- The covering unitary-three family is excluded without identifying the
special-unitary group with its projective quotient. -/
theorem LocalData.source_overcomponent_not_binary_suThree
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n k : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R < K)
    (hK : (K.subgroupOf X).IsCComponent) (hk : 0 < k) :
    ¬ IsSU (K ⧸ pCore 2 K) 3 (2 ^ k) := by
  rintro ⟨F,_,_,J,hF,hc,⟨e⟩⟩
  apply d.source_overcomponent_not_solvableSylow h hH hSyl hRX hKX hRK hK
  apply SolvableSylowOvergroups.of_equiv e
  intro S P hSP hP
  have hf := ChapterF.Source.rankOneSylowFacts_su3 J k hk hF hc S
  let := hf.solvable
  exact Group.isSolvable_of_isSolvable_injective
    (inclusion_injective (hf.unique_maximal P hSP (lt_top_iff_ne_top.mpr hP)))

/-- After the small endpoints and the large-field exclusions, the only
remaining rank-two Theorem C model is the genuine binary triality group. -/
theorem LocalData.source_overcomponent_rankTwo_binaryTriality
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hm : RankTwoTheoremC (K ⧸ pCore 2 K)) :
    Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K) := by
  have hs := d.source_overcomponent_not_small h hH hSyl
    (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK hK
  cases hm with
  | linear k hk hm =>
    by_cases hk2 : 2 ≤ k
    · exact (d.source_overcomponent_not_classical_rankTwo h hH c hd hSyl hRK hKX hK hKn hk2 (.inr hm)).elim
    · have he : k = 1 := by omega
      subst k
      exact (hs (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [pow_one] using hm)))))).elim
  | symplectic k hk hm =>
    exact (d.source_overcomponent_not_classical_rankTwo h hH c hd hSyl hRK hKX hK hKn hk (.inl hm)).elim
  | g2 k hk hm =>
    exact (d.source_overcomponent_not_g2 h hH c hd hSyl hRK hKX hK hKn hk hm).elim
  | triality k hk hm =>
    by_cases hk2 : 2 ≤ k
    · exact (d.source_overcomponent_not_triality h hH c hd hSyl hRK hKX hK hKn hk2 hm).elim
    · have he : k = 1 := by omega
      subst k
      simpa only [pow_one] using hm
  | ree m hm hmodel =>
    obtain ⟨b,⟨e⟩⟩ := hmodel
    exact (d.source_overcomponent_not_ree h hH c hd hSyl hRK hKX hK hKn
      ⟨m,hm,⟨e.trans b.modelEquiv⟩⟩).elim
  | symplectic_derived hm =>
    exact (hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))))).elim
  | g2_derived hm =>
    exact (hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))))).elim
  | tits hm =>
    exact (hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm)))))))).elim

/-- Both linear-three forms and the special-unitary-three cover are excluded
over every positive binary field exponent, including exponent one. -/
theorem LocalData.source_overcomponent_not_binary_ternary
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p k : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hk : 1 ≤ k) :
    ¬ (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨
      IsSL (K ⧸ pCore 2 K) 3 (2 ^ k) ∨ IsSU (K ⧸ pCore 2 K) 3 (2 ^ k)) := by
  have hRX : R ≤ generated L H D R ⊔ normalizingSylow T R :=
    le_sup_left.trans (le_sup_right.trans le_sup_left)
  intro hm
  rcases hm with hm | hm | hm
  · by_cases hk2 : 2 ≤ k
    · exact d.source_overcomponent_not_classical_rankTwo h hH c hd hSyl hRK hKX hK hKn hk2 (.inr hm)
    · have he : k = 1 := by omega
      subst k
      exact d.source_overcomponent_not_small h hH hSyl hRX hKX hRK hK
        (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [pow_one] using hm)))))
  · by_cases hk2 : 2 ≤ k
    · exact d.source_overcomponent_not_specialLinear h hH c hd hSyl hRK hKX hK hKn hk2 hm
    · have he : k = 1 := by omega
      subst k
      exact d.source_overcomponent_not_small h hH hSyl hRX hKX hRK hK
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [pow_one] using hm))))))
  · exact d.source_overcomponent_not_binary_suThree h hH hSyl hRX hKX hRK hK hk hm

/-- The actual proper containing component carries the small-model exclusions
and the rank-two reduction, while retaining the literal quotient embedding. -/
theorem LocalData.source_overcomponent_small_exclusions
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R)) :
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
      (RankTwoTheoremC (K ⧸ pCore 2 K) →
        Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K)) := by
  obtain ⟨K,hRK,hKX,hK,hKn,hlt,hb⟩ := d.source_overcomponent_nonBender h hH c hd hz hSyl
  refine ⟨K,hRK,hKX,hK,hKn,hlt,hb,?_,?_,?_⟩
  · have hs := d.source_overcomponent_not_small h hH hSyl
      (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK hK
    rintro (ha | ha | ha)
    · exact hs (.inl ha)
    · exact hs (.inr (.inl ha))
    · exact hs (.inr (.inr (.inl ha)))
  · exact fun _ hk => d.source_overcomponent_not_binary_ternary h hH c hd hSyl hRK hKX hK hKn hk
  · exact d.source_overcomponent_rankTwo_binaryTriality h hH c hd hSyl hRK hKX hK hKn

/-- Apply the complete small-family reduction to the same changed-Sylow
witness; the larger alternative remains an actual ambient Sylow subgroup. -/
theorem LocalData.changedSylow_small_exclusions
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) :
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
          (RankTwoTheoremC (K ⧸ pCore 2 K) →
            Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K))) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) := by
  obtain ⟨_,_,P,hTP,_,hD,_,hcases⟩ := d.changedSylow_action h hH c hd hz
  refine ⟨P,hTP,hD,?_⟩
  rcases hcases with he | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    exact Or.inl ⟨he,d.source_overcomponent_small_exclusions h hH c hd hz hSyl⟩
  · exact Or.inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
