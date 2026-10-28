module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowMathieuTwelve
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.Mathieu.QuinticSylowActors

/-!
# The actual prime actor in the larger Mathieu containing rows

Let T₀ be the normalizer of the selected right factor in the original
Sylow. The original left root group U is contained in T₀, the prime actor
D normalizes U, and T₀ normalizes UD. The product-order formula therefore
bounds the order of DT₀ by a power of two times the actual prime p.

At the smaller changed Sylow this bound descends through the literal
quotient X/O₂(X). The native M₂₂, M₂₃ and M₂₄ Sylow-overgroup obstructions
exclude a faithful quintic actor on the containing component. Thus p=3.
The original selected-source implication for an A₅ right quotient forces
p=5, so it also excludes that right quotient in all three Mathieu rows.
Both original Hall markings and every previous exclusion are retained.

The remaining cubic non-A₅ Mathieu rows, other containing families,
larger changed-Sylow assembly, compatible zero-core recognition and
higher-field normalization remain open. The authorized h513 input is
unchanged. Source: Aschbacher–Smith 5.1.5 and 5.2.2, printed pp.631–632
and648–649 (`refs/quasithin.pdf`); native geometry from GLS3 Table5.3c–e.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The original actor and normalizing Sylow have order supported only at
two and the actor prime, with the odd part dividing that prime itself. -/
theorem LocalData.actor_join_order
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ a : ℕ, Nat.card (D ⊔ normalizingSylow T R : Subgroup G) ∣ 2 ^ a * p := by
  let U := (T : Subgroup G) ⊓ L
  let T₀ := normalizingSylow T R
  have hUT₀ : U ≤ T₀ := by
    dsimp only [U]
    rw [← d.S_intersection_left]
    exact inf_le_left.trans (d.sourceS_le_normalizingSylow h hH)
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
      inf_normalizer_le_normalizer_inf
  have hTBorel : (T : Subgroup G) ≤ normalizer (localBorel T L : Set G) :=
    (le_inf h.sylow_normalizes
      (hTU.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hT₀UD : T₀ ≤ normalizer ((U ⊔ D : Subgroup G) : Set G) :=
    (inf_le_left.trans hTBorel).trans
      (cartan_subgroup_preimage_normalized c h.sylow_normalizes h.linear hd.le_cartan)
  have hDU : D ≤ normalizer (U : Set G) :=
    hd.le_cartan.trans (c.left_le.trans inf_le_right)
  obtain ⟨u,hu⟩ := (T.isPGroup'.to_le (show U ≤ (T : Subgroup G) from inf_le_left)).exists_card_eq
  obtain ⟨t,ht⟩ := (T.isPGroup'.to_le (show T₀ ≤ (T : Subgroup G) from inf_le_left)).exists_card_eq
  have hUD : Nat.card (U ⊔ D : Subgroup G) ∣ Nat.card U * Nat.card D := by
    rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes U D hDU]
    exact dvd_mul_left _ _
  have hj : Nat.card ((U ⊔ D) ⊔ T₀ : Subgroup G) ∣
      (Nat.card U * Nat.card D) * Nat.card T₀ := by
    apply dvd_trans ?_ (Nat.mul_dvd_mul hUD (dvd_refl (Nat.card T₀)))
    rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes (U ⊔ D) T₀ hT₀UD]
    exact dvd_mul_left _ _
  have he : (U ⊔ D) ⊔ T₀ = D ⊔ T₀ := by
    rw [sup_assoc, sup_eq_right.mpr (hUT₀.trans le_sup_right)]
  refine ⟨u+t,?_⟩
  rw [he,hu,ht,hd.card] at hj
  simpa only [pow_add,mul_assoc,mul_comm,mul_left_comm] using hj

/-- A containing M₂₂, M₂₃ or M₂₄ quotient forces the actual escaping actor to be cubic. -/
theorem LocalData.source_overcomponent_mathieu_prime
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
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24)) :
    p = 3 := by
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
  obtain ⟨a,ha⟩ := d.actor_join_order h hH c hd
  have hjoin : Dbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) =
      ((D ⊔ normalizingSylow T R).subgroupOf X).map q := by
    change Dbar ⊔ (S : Subgroup X).map q = _
    rw [heS,subgroupOf_sup hDX hTX,Subgroup.map_sup]
  have hdiv : Nat.card (Dbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) : Subgroup _) ∣
      2^a * 5 := by
    rw [hjoin]
    apply (((D ⊔ normalizingSylow T R).subgroupOf X).card_map_dvd q).trans
    rwa [Nat.card_congr (subgroupOfEquivOfLe (sup_le hDX hTX)).toEquiv]
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  apply Sporadic.Mathieu.QuinticSylowActors.no_five_actor Kbar Dbar P _ hc hdC hdiv
  exact hm.imp (fun he => he.map (fun e => eK.trans e))
    (fun he => he.imp (fun he => he.map (fun e => eK.trans e))
      (fun he => he.map (fun e => eK.trans e)))


open Chapter1.Section02.LocalModels

/-- In every remaining larger Mathieu container the source actor is cubic
and the original right quotient is not PSL₂(4). The same selected pair retains
all preceding exclusions, both Hall markings and the literal quotient maps. -/
theorem source_prime_pair_mathieu_actor_reduction
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
              ((Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) ∨
                Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) ∨
                Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24)) →
                p = 3 ∧ ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)) ∨
            ∃ U : Sylow 2 G, (U : Subgroup G) = T₁))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_mathieu_twelve_containing_exclusions h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,hseven,hprime,hbinary,hodd,hm11,hm12⟩ | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left
    refine .inl ⟨he,K,hRK,hKX,hK,hKn,hlt,hb,hsmall,hternary,hrank,hj,h25,hseven,hprime,hbinary,hodd,hm11,hm12,?_⟩
    intro hm
    have hp := d.source_overcomponent_mathieu_prime h hH c hd hz hSyl hRK.le hKX hK hKn hm
    refine ⟨hp,fun hfour => ?_⟩
    have hp5 := (hA5 hfour).1
    omega
  · exact .inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
