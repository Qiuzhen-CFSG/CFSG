module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicPrimeReduction
public import CFSG.Quasithin.ChapterB.Section02.Thompson.NearMaximumAction
public import CFSG.Quasithin.ChapterD.Section02.ThompsonGeneration
public import Theory.GroupTheory.OddPrimeSectionCentralizers.ElementaryAction

/-!
# Actual elementary actors in the moved-prime cubic branch

For D = ⟨L₂,Y,T⟩ and W = ⟨V₁^D⟩, the identity [L₂,J₁(T)] = L₂
forces a near-maximum elementary subgroup A of the original T to move
every normal odd subgroup moved by L₂ in D/C_D(W). The literal action
of A on W has fixed codimension at most its image rank plus one.
A moving involution in that image has cyclic centralizer in the odd
subgroup and full p-centralizer rank at most one. The rank-two section
theorem is applied to the original SQTK cover D, retaining its quotient
map throughout. Coprime fixed-point generation then bounds the selected
actor's image on the actual supercritical subgroup by order four, using
the literal characteristic-restriction map from the preceding reduction.

The non-{2,3} alternative keeps the previously constructed supercritical
subgroup and its commutator identity. The order-four chief interval
supplies all the premises with the same Y, star kernel, and S₃ quotient.
The remaining representation exclusion of this alternative and the
subsequent solvable containment in 14.5.3(2) are not asserted here.

Source: Aschbacher–Smith 14.5.11, printed pp.1015–1016; its A.1.31(1)
and B.2.4(1) inputs; and the interval use in 14.7.20(2), printed p.1049,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open ChapterB Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Every moved normal odd subgroup in the original cubic action has a
near-maximum elementary actor with controlled codimension and cyclic
involution centralizer. The prime rank is taken before quotienting. -/
theorem cubic_generated_moved_prime_actor_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let U := W.subgroupOf D
    letI : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
    letI : IsElementaryAbelian 2 U :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (U : Set D)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∀ (p : ℕ) (_ : p.Prime) (R : Subgroup (D ⧸ C)), R.Normal → Odd p →
      IsPGroup p R → ¬ ((F.Li L 2).subgroupOf D).map q ≤ centralizer (R : Set (D ⧸ C)) →
      ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
        let B := (A.subgroupOf D).map q
        IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
        ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧ t ∉ centralizer (R : Set (D ⧸ C)) ∧
          IsCyclic (R ⊓ centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
          primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let U := W.subgroupOf D
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 U :=
    (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
  let C := centralizer (U : Set D)
  let q := QuotientGroup.mk' C
  dsimp only
  intro p hp R hnR ho hR hm
  let : R.Normal := hnR
  let : Fact p.Prime := ⟨hp⟩
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hUS : U ≤ (T : Subgroup G).subgroupOf D := by
    have hr := (cubic_generated_span_reduced h hab structural previous Y hYH he).le_pCore
    exact hr.trans (pCore_isPGroup.le_sylow_of_normal (T.subtype hTD))
  have hrank : primeRank p D ≤ 2 :=
    (cubic_generated_local_structure h hab structural previous Y hYH he).2.1.stronglyQuasithin p hp ho
  have hc := (cubic_generated_thompson_one_action_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he).1
  rw [←thompsonJ_subgroupOf D (T : Subgroup G) hTD 1] at hc
  obtain ⟨A,hA,helem,hcod,t,ht,ht2,htR,hcyc,hcr⟩ := near_maximum_prime_movement ((T : Subgroup G).subgroupOf D) U hUS q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    (((F.Li L 2).subgroupOf D).map q) R ho hrank hR hc hm
  have hAf : A.map D.subtype ∈ thompsonFamily (T : Subgroup G) 1 := by
    have hh := (thompsonFamily_map_iff_of_injective D.subtype D.subtype_injective
      ((T : Subgroup G).subgroupOf D) A 1).mpr hA
    rwa [map_subgroupOf_eq_of_le hTD] at hh
  have hAr : (A.map D.subtype).subgroupOf D = A := by
    exact comap_map_eq_self_of_injective D.subtype_injective A
  refine ⟨A.map D.subtype,hAf,?_⟩
  rw [hAr]
  exact ⟨helem,hcod,t,ht,ht2,htR,hcyc,hcr⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_moved_prime_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let U := W.subgroupOf D
    letI : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
    letI : IsElementaryAbelian 2 U :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (U : Set D)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∀ (p : ℕ) (_ : p.Prime) (R : Subgroup (D ⧸ C)), R.Normal → Odd p →
      IsPGroup p R → ¬ ((F.Li L 2).subgroupOf D).map q ≤ centralizer (R : Set (D ⧸ C)) →
      ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
        let B := (A.subgroupOf D).map q
        IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
        ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧ t ∉ centralizer (R : Set (D ⧸ C)) ∧
          IsCyclic (R ⊓ centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
          primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 := by
  apply cubic_generated_moved_prime_actor_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The non-{2,3} branch carries its actual near-maximum actor and the
rank-one involution centralizer, together with the original supercritical
subgroup and residual commutator identity. -/
theorem cubic_generated_action_prime_actors_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    let X := ((F.Li L 2).subgroupOf D).map q
    let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
    let ρ := NormalElementaryQuotient.representation (W.subgroupOf D) q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    IsPiGroup twoThreePrimes (D ⧸ C) ∨
      ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
        (hR : IsSupercriticalPSubgroup p R),
        3 < p ∧
        letI : R.Characteristic := hR.characteristic
        let a := (MulAut.characteristic R).comp
          (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
        (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
        ¬ IsCyclic R ∧
        ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
        X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a ∧
        ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
          let B := (A.subgroupOf D).map q
          IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
          Nat.card (B.map a) ≤ 4 ∧
          ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧
            t ∉ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
            IsCyclic (R.map (pCore p (D ⧸ C)).subtype ⊓
              centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
            primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 := by
  classical
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 (W.subgroupOf D) :=
    (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
  let C := centralizer (W.subgroupOf D : Set D)
  rcases cubic_generated_action_prime_reduction_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he with h23 | ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm⟩
  · exact Or.inl h23
  let : Fact p.Prime := ⟨hp⟩
  let : R.Characteristic := hR.characteristic
  let : (R.map (pCore p (D ⧸ C)).subtype).Characteristic := hchar
  refine Or.inr ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm,?_⟩
  obtain ⟨A,hA,hB,hcod,t,ht,ht2,htR,hcyc,hcr⟩ :=
    cubic_generated_moved_prime_actor_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he p hp (R.map (pCore p (D ⧸ C)).subtype) inferInstance
      (hp.odd_of_ne_two (by omega))
      ((pCore_isPGroup (p := p) (G := D ⧸ C)).to_subgroup R |>.map (pCore p (D ⧸ C)).subtype) hm
  let q := QuotientGroup.mk' C
  let B := (A.subgroupOf D).map q
  let : IsElementaryAbelian 2 B := hB.2
  refine ⟨A,hA,hB,hcod,?_,t,ht,ht2,htR,hcyc,hcr⟩
  exact characteristic_prime_core_action_card_le_four (hp.odd_of_ne_two (by omega)) q
    (QuotientGroup.mk'_surjective C)
    ((cubic_generated_local_structure h hab structural previous Y hYH he).2.1.stronglyQuasithin
      p hp (hp.odd_of_ne_two (by omega))) R B

/-- The original full point-normality interface. -/
theorem cubic_generated_action_prime_actors
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    let X := ((F.Li L 2).subgroupOf D).map q
    let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
    let ρ := NormalElementaryQuotient.representation (W.subgroupOf D) q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    IsPiGroup twoThreePrimes (D ⧸ C) ∨
      ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
        (hR : IsSupercriticalPSubgroup p R),
        3 < p ∧
        letI : R.Characteristic := hR.characteristic
        let a := (MulAut.characteristic R).comp
          (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
        (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
        ¬ IsCyclic R ∧
        ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
        X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a ∧
        ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
          let B := (A.subgroupOf D).map q
          IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
          Nat.card (B.map a) ≤ 4 ∧
          ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧
            t ∉ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
            IsCyclic (R.map (pCore p (D ⧸ C)).subtype ⊓
              centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
            primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 := by
  apply cubic_generated_action_prime_actors_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The actual order-four interval supplies the moved-prime actors on its
literal cubic quotient, retaining Y, its exact star kernel, and the S₃ quotient. -/
theorem extraspecial_four_interval_cubic_prime_actors
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      ∃ he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)),
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      Group.IsSolvable D ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) ∧
      elementaryAbelianMaxJ (D.pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      elementaryAbelianMaxJ ((F.P L).pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ F.Ri L 1 ∧
      ⁅F.Li L 2,thompsonJ (T : Subgroup G) 1⁆ = F.Li L 2 ∧
      ¬ thompsonJ (T : Subgroup G) 1 ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) ∧
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
        (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
      let C := centralizer (W.subgroupOf D : Set D)
      let q := QuotientGroup.mk' C
      let X := ((F.Li L 2).subgroupOf D).map q
      let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
      let ρ := NormalElementaryQuotient.representation (W.subgroupOf D) q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      IsPiGroup twoThreePrimes (D ⧸ C) ∨
        ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
          (hR : IsSupercriticalPSubgroup p R),
          3 < p ∧
          letI : R.Characteristic := hR.characteristic
          let a := (MulAut.characteristic R).comp
            (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
          (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
          ¬ IsCyclic R ∧
          ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
          X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a ∧
          ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
            let B := (A.subgroupOf D).map q
            IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
          Nat.card (B.map a) ≤ 4 ∧
            ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧
              t ∉ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
              IsCyclic (R.map (pCore p (D ⧸ C)).subtype ⊓
                centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
              primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
      hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove⟩ :=
    extraspecial_four_interval_cubic_thompson_one h hab structural previous faithful
      hex hcard hexp N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
    hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove,
    cubic_generated_action_prime_actors h hab structural previous faithful hn
      Y hYH hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
