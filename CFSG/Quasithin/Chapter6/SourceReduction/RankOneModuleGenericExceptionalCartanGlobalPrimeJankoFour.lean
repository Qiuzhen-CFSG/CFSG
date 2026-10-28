module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeJankoFourLocal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeOddRadical
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeChangedSylowRemainder

/-!
# Excluding the smaller-Sylow A₅ branch

The original actor in a normal J₄ containing quotient must be cubic:
its faithful quotient action and the actor–Sylow order bound contradict
the native quintic exclusion. In the smaller-Sylow A₅ branch both original
Cartan markings instead force a quintic actor. The proved containing
catalogue leaves only J₄, so this entire A₅ branch is impossible.

The resulting source selection retains the same right factor, strict
quotient embedding, relative normality and full containing catalogue.
It preserves the larger-Sylow component/parabolic distinction and zero-core
branch. It neither equates the changed residual with the original residual
nor asserts full Cartan normalization. Those branches and higher-field
normalization remain obligations of the global argument.

Source: Aschbacher–Smith 5.1.12–13 and 5.2.2, printed pp.635–638,648–649
of refs/quasithin.pdf; the J₄ local structure is GLS3 Table 5.3i.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The genuine actor in a J₄ containing row must be cubic. -/
theorem LocalData.source_overcomponent_janko_four_prime
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
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
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
  exact JankoFourActors.no_five_actor Kbar Dbar P (eK.trans hm.some) hc hdC hdiv

open Chapter1.Section02 LocalModels

/-- The smaller changed Sylow cannot occur with an A₅ right quotient.
This applies to the selected parabolic as well as to an actual H-component. -/
theorem LocalData.changedSylow_A5_exclusion
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hs : SelectedSourceModels H R)
    (P : Sylow 2 (extension T L H B D R))
    (hP : (P : Subgroup (extension T L H B D R)).map
      (extension T L H B D R).subtype = normalizingSylow T R)
    (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R) (hRK : R ≤ K)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hm : RemainingSourceContainer (generated L H D R ⊔ normalizingSylow T R) K) : False := by
  obtain ⟨_,_,_,⟨eI⟩⟩ := d.changedSylow_A5_remaining_janko h hH hgen hthree c hd hz hs
    P hP hKX hRK hK hKn hA5 hm
  have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R) :=
    Chapter1.IsSylowIn.restrict ⟨P,hP⟩ le_sup_right le_sup_left
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  have hp3 := d.source_overcomponent_janko_four_prime h hH c hd hz hSyl hRK hKX hK hKn
    ⟨eK.symm.trans eI⟩
  have hp5 := d.selected_A5_actor_prime h hH hgen c hd hz hs hthree hA5
  omega

/-- On the actual selected prime pair, the remaining smaller-Sylow branch
has non-A₅ right quotient. Zero-core and larger-Sylow branches are retained. -/
theorem source_prime_pair_nonA5_containing_remainder
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
              RemainingSourceContainer X K ∧
              ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) ∨
            (∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
              normalizingSylow T R < T₁ ∧ RemainingLargerSource H R p n)))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_changedSylow_remainder h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hm⟩ | ha
  · refine .inl ⟨he,K,hRK,hKX,hK,hKn,hlt,hm,?_⟩
    intro hfour
    exact d.changedSylow_A5_exclusion h hH hgen hthree c hd hz hs P he
      hKX hRK.le hK hKn hfour hm
  · exact .inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
