module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowAction
public import Theory.SpecificGroups.SymplecticFour.Sylow.OddSupplement
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.OddSupplement

/-!
# Classical containing-component exclusions at the smaller changed Sylow

In X=G₀T₀ the right factor R has proper image in the normal containing
component. The image of T₀ is a full Sylow, normalizes that factor, and
joins with the actual odd prime actor D to a solvable subgroup. These
subgroups generate the literal X/O₂(X). The intrinsic two-parabolic
obstruction therefore excludes PSp₄(2ᵏ) and PSL₃(2ᵏ), k≥2, as the actual
containing two-core quotient. No parabolic marking callback is retained.

The final theorem connects these exclusions to the actual changed-Sylow
dichotomy. The other component models, the larger-Sylow branch, and final
normalization remain with qt-d-1222-rankone-cartan-local-to-global.
This does not exclude central covers or the exceptional rank-two families.
Source: Aschbacher--Smith 5.1.13 and 5.2.2, pp.636 and 648--649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- At the smaller changed Sylow, the actual containing component cannot
have a nonbinary symplectic-four or projective linear-three quotient. -/
theorem LocalData.source_overcomponent_not_classical_rankTwo
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p k : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hk : 2 ≤ k) :
    ¬ (ClassicalGroup.IsPSp (K ⧸ pCore 2 K) 2 (2 ^ k) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ k)) := by
  intro hm
  let X := generated L H D R ⊔ normalizingSylow T R
  let q := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map q
  let Kbar := (K.subgroupOf X).map q
  let Dbar := (D.subgroupOf X).map q
  have hRX : R ≤ X := le_sup_left.trans (le_sup_right.trans le_sup_left)
  have hDX : D ≤ X := le_sup_left.trans le_sup_left
  have hTX : normalizingSylow T R ≤ X := le_sup_right
  obtain ⟨S,hS⟩ := hSyl
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply (map_injective X.subtype_injective)
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hlocal : R.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T R).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  have hlocalbar : Rbar ∈ ChapterA.Section03.localCComponents P := by
    change Rbar ∈ ChapterA.Section03.localCComponents ((S : Subgroup X).map q)
    rw [heS]
    exact Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hlocal
  have hRns : ¬ Group.IsSolvable Rbar := by
    intro hs
    let := hs
    exact hlocalbar.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (show Rbar ≤ Rbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) from le_sup_left)).toMonoidHom)
        (subgroupOfEquivOfLe le_sup_left).injective)
  have hlt : Rbar < Kbar := d.right_image_lt h hH ⟨S,hS⟩ hRX hKX hRK hK
  let : (K.subgroupOf X).Normal := hKn
  let : Kbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hn : (P : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (Rbar : Set (X ⧸ pCore 2 X)) := by
    change (S : Subgroup X).map q ≤ _
    rw [heS]
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRX]
    exact comap_mono (show normalizingSylow T R ≤ normalizer (R : Set G) from inf_le_right)
  have hoddD : Odd (Nat.card D) := by
    rw [hd.card]
    rcases hd.prime with rfl | rfl <;> decide
  have hodd : Odd (Nat.card Dbar) := by
    apply Odd.of_dvd_nat _ (card_map_dvd (D.subgroupOf X) q)
    simpa only [Nat.card_congr (subgroupOfEquivOfLe hDX).toEquiv] using hoddD
  have hsol : Group.IsSolvable ((P : Subgroup (X ⧸ pCore 2 X)) ⊔ Dbar : Subgroup (X ⧸ pCore 2 X)) := by
    let := d.actor_join_solvable h hH c hd
    have hh : Group.IsSolvable ((D ⊔ normalizingSylow T R).subgroupOf X) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (sup_le hDX hTX)).toMonoidHom)
        (subgroupOfEquivOfLe (sup_le hDX hTX)).injective
    let := hh
    have hs : Group.IsSolvable (((D ⊔ normalizingSylow T R).subgroupOf X).map q) :=
      Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
    change Group.IsSolvable ((S : Subgroup X).map q ⊔ Dbar : Subgroup (X ⧸ pCore 2 X))
    rw [heS]
    rw [subgroupOf_sup hDX hTX, Subgroup.map_sup] at hs
    rw [sup_comm]
    exact hs
  have hgen : Rbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) ⊔ Dbar = ⊤ := by
    have he : R ⊔ normalizingSylow T R ⊔ D = X := by
      calc
        _ = D ⊔ (R ⊔ normalizingSylow T R) := by ac_rfl
        _ = D ⊔ (R ⊔ (Global.sourceS L H ⊔ normalizingSylow T R)) := by
          rw [sup_eq_right.mpr (d.sourceS_le_normalizingSylow h hH)]
        _ = X := by dsimp only [X,generated]; ac_rfl
    have hgenX : R.subgroupOf X ⊔ (normalizingSylow T R).subgroupOf X ⊔ D.subgroupOf X = ⊤ := by
      rw [←subgroupOf_sup hRX hTX, ←subgroupOf_sup (sup_le hRX hTX) hDX,he,subgroupOf_self]
    change (R.subgroupOf X).map q ⊔ (S : Subgroup X).map q ⊔ (D.subgroupOf X).map q = ⊤
    rw [heS,←Subgroup.map_sup,←Subgroup.map_sup,hgenX,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact Theory.SpecificGroups.SymplecticFour.no_odd_solvable_supplement hF hk
      P Kbar Rbar Dbar (eK.trans (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm))
      hlt hRns hn hodd hsol hgen
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact Matrix.PSL3.LinearThree.OddSupplement.no_odd_solvable_supplement hF hk
      P Kbar Rbar Dbar (eK.trans e) hlt hRns hn hodd hsol hgen

/-- The proper quotient overcomponent excludes the Bender and both
nonbinary classical rank-two families using the same marked local subgroups. -/
theorem LocalData.source_overcomponent_classical_exclusions
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
      ∀ k : ℕ, 2 ≤ k →
        ¬ (ClassicalGroup.IsPSp (K ⧸ pCore 2 K) 2 (2 ^ k) ∨
          ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ k)) := by
  obtain ⟨K,hRK,hKX,hK,hKn,hlt,hm⟩ := d.source_overcomponent_nonBender h hH c hd hz hSyl
  exact ⟨K,hRK,hKX,hK,hKn,hlt,hm,fun _ hk =>
    d.source_overcomponent_not_classical_rankTwo h hH c hd hSyl hRK hKX hK hKn hk⟩

/-- The actual changed-Sylow dichotomy carries the new model exclusions
in its smaller branch and keeps the ambient-Sylow alternative explicit. -/
theorem LocalData.changedSylow_classical_exclusions
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
          ∀ k : ℕ, 2 ≤ k →
            ¬ (ClassicalGroup.IsPSp (K ⧸ pCore 2 K) 2 (2 ^ k) ∨
              ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ k))) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) := by
  obtain ⟨_,_,P,hTP,_,hD,_,hcases⟩ := d.changedSylow_action h hH c hd hz
  refine ⟨P,hTP,hD,?_⟩
  rcases hcases with he | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    exact Or.inl ⟨he,d.source_overcomponent_classical_exclusions h hH c hd hz hSyl⟩
  · exact Or.inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
