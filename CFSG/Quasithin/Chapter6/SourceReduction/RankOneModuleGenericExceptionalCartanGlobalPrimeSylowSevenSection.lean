module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowPrimeField
public import Theory.SpecificGroups.Alternating.SevenRankOneCover
public import CFSG.Quasithin.ChapterF.Section01.RankOneSmallTwoPart

/-!
# Both alternating-seven containers at the smaller changed Sylow

The source right factor has a nonsolvable genuine rank-one quotient. Its
order divides the literal containing quotient, so either A₇ covering row
bounds its two-part by eight. The source model calculation leaves PSL₂(4)
or PSL₂(8). Projecting the actual perfect subgroup through the central
cover preserves its properness and intrinsic two-core quotient; the
seven-point coset argument then forces the field to have order four.

Thus the existing Hall/actor argument applies without an assumed A₅
right marking. It makes the same escaping prime both cubic and quintic,
excluding both covering rows. The final theorem applies this to the
constructed source pair and changed Sylow, retaining all previous exclusions.

Marked zero-core recognition, other containing families, the larger-Sylow
branch, higher-field reduction and final normalization remain with the
original local-to-global owner. The authorized h513 input is unchanged.
Source: Aschbacher–Smith A.3.12,5.1.12–13 and5.2.2,
printed pp.47–48,635–638,648–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
open Chapter1.Section02.LocalModels

/-- Either alternating-seven cover forces the selected right factor's
literal two-core quotient to be PSL₂(4). -/
theorem LocalData.source_overcomponent_seven_right_section
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R < K)
    (hK : (K.subgroupOf X).IsCComponent)
    (hm : IsAlternating (K ⧸ pCore 2 K) 7 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 7) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map q
  let Kbar := (K.subgroupOf X).map q
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  have hlt : Rbar < Kbar := d.right_image_lt h hH hSyl hRX hKX hRK hK
  let r := q.subgroupMap (R.subgroupOf X)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eRX := (subgroupOfEquivOfLe hRX).symm
  let e₁ := QuotientGroup.congr _ _ eRX (pCore_map_iso 2 eRX)
  let e₂ := r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr
  let eR : (R ⧸ pCore 2 R) ≃* (Rbar ⧸ pCore 2 Rbar) := e₁.trans e₂
  have hsmall : ¬16 ∣ Nat.card (R ⧸ pCore 2 R) := by
    intro hdiv
    have hd : 16 ∣ Nat.card Kbar :=
      (hdiv.trans ((Nat.card_congr eR.toEquiv) ▸ (card_quotient_dvd_card (pCore 2 Rbar)))).trans
        (card_dvd_of_le hlt.le)
    rw [Nat.card_congr eK.toEquiv] at hd
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hd
      norm_num [Nat.factorial] at hd
    · obtain ⟨_,⟨a⟩,⟨e⟩⟩ := hm
      rw [card_eq_card_quotient_mul_card_subgroup (center (K ⧸ pCore 2 K)),
        Nat.card_congr e.toEquiv,Nat.card_congr a.toEquiv,
        nat_card_alternatingGroup,Nat.card_fin] at hd
      norm_num [Nat.factorial] at hd
  have hns : ¬Group.IsSolvable (R ⧸ pCore 2 R) := by
    intro hs
    let := hs
    let : Group.IsNilpotent (pCore 2 R) := pCore_isNilpotent
    exact d.right_nonsolvable (Group.isSolvable_of_ker_le_range (pCore 2 R).subtype
      (QuotientGroup.mk' (pCore 2 R)) (by simp))
  obtain ⟨f,hf,_,hmodel⟩ := d.right_quotient.binary_of_small_twoPart hns hsmall
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hmodel
  let U := Rbar.subgroupOf Kbar
  let u : U ≃* Rbar := subgroupOfEquivOfLe hlt.le
  let au := (QuotientGroup.congr _ _ u (pCore_map_iso 2 u)).trans (eR.symm.trans a)
  have hu : U ≠ ⊤ := fun he => hlt.not_ge (subgroupOf_eq_top.mp he)
  let : Group.IsPerfect R := Chapter1.mem_L_isPerfect (d.right_mem_local_family h hH)
  let : Group.IsPerfect (R.subgroupOf X) := Group.IsPerfect.ofSurjective
    (f := eRX.toMonoidHom) eRX.surjective
  let : Group.IsPerfect Rbar := Group.IsPerfect.map _
  let : Group.IsPerfect U := Group.IsPerfect.ofSurjective (f := u.symm.toMonoidHom) u.symm.surjective
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let : Group.IsPerfect Kbar := (hK.map_quotient (pCore 2 X)).perfect
  have he : Nonempty (((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃*
      alternatingGroup (Fin 7)) := by
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      have hc : center (K ⧸ pCore 2 K) = ⊥ := by
        apply eq_bot_iff.mpr
        intro x hx
        have hh := (centerCongr e ⟨x,hx⟩).property
        change e x ∈ center (alternatingGroup (Fin 7)) at hh
        rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
        exact e.map_eq_one_iff.mp hh
      exact ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e⟩
    · exact hm.2.2
  let eZ := QuotientGroup.congr _ _ eK (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr eK ⟨x,hx⟩).property
    · intro y hy
      exact ⟨eK.symm y,(centerCongr eK.symm ⟨y,hy⟩).property,eK.apply_symm_apply y⟩)
  have hf2 := alternatingGroup.SevenRankOneSection.degree_eq_two_of_central_cover
    (eZ.trans he.some) U hu hF hf au
  exact ⟨F,inferInstance,inferInstance,by simpa [hf2] using hF,⟨a⟩⟩

/-- The selected source rows exclude both A₇ covering alternatives without
an additional A₅ assumption on the right factor. -/
theorem LocalData.selected_source_not_alternating_seven_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hs : SelectedSourceModels H R)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ (IsAlternating (K ⧸ pCore 2 K) 7 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 7) := by
  intro hm
  have hA5 := d.source_overcomponent_seven_right_section h hH hSyl
    (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK hK hm
  exact d.selected_A5_not_alternating_seven_container h hH hgen c hd hz hs hthree
    hA5 hSyl hRK hKX hK hKn hm

/-- Construct the source pair and exclude both alternating-seven covers on
its actual smaller changed Sylow, retaining the earlier model exclusions. -/
theorem source_prime_pair_alternating_containing_exclusions
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
              (∀ q : ℕ, q.Prime → Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 q)) ∨
            ∃ U : Sylow 2 G, (U : Subgroup G) = T₁))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_odd_containing_exclusions h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,_,hprime⟩ | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    exact .inl ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,
      d.selected_source_not_alternating_seven_container h hH hgen c hd hz hs hthree
        hSyl hRK hKX hK hKn,hprime⟩
  · exact .inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
