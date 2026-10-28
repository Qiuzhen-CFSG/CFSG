module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicPrimeActors
public import CFSG.Quasithin.ChapterB.Section02.Thompson.FixedAction

/-!
# Removing the elementary actor kernel in the original cubic reduction

In the moved-prime branch of 14.5.11, let B be the image of the selected
near-maximum elementary subgroup of the original T, and put
K₀ = C_B(R), U₀ = C_W(K₀). Thompson A×B keeps the actual odd subgroup R
faithful on U₀. Its normality identifies C_B(U₀) exactly with K₀.
Counting elementary replacements in the original T bounds the fixed
codimension of B/K₀ by its rank plus one. Its order is at most four,
so the action is cubic, has fixed codimension at most three, and has
cubic ratio at most two.

The original order-four interval supplies every input with the same Y,
star kernel and S₃ quotient. These are the actual representation and
kernel reductions; the further prime exclusion and solvable containment
are not asserted here.

Source: Aschbacher–Smith 14.5.11, pp.1015–1016, its A.1.18 and B.2.4
inputs, and the interval application in 14.7.20(2), p.1049,
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

/-- The moved-prime alternative has a literal fixed-space action with its exact
kernel, a faithful odd subgroup, a cubic actor of order at most four, and
cubic ratio at most two. -/
theorem cubic_generated_action_prime_fixed_actors_of_normalizes_point
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
            primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 ∧
          let R₀ := R.map (pCore p (D ⧸ C)).subtype
          let K₀ := B ⊓ centralizer (R₀ : Set (D ⧸ C))
          let U₀ := fixedSpace ρ K₀
          let I := restrictedSubgroup ρ U₀ B
          subspaceKernel ρ U₀ R₀ = ⊥ ∧ subspaceKernel ρ U₀ B = K₀ ∧
            IsElementaryTwo I ∧ Nat.card I ≤ 4 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ rank I + 1 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ 3 ∧
            IsCubic (subspaceImageRepresentation ρ U₀) I ∧
            cubicRatio (subspaceImageRepresentation ρ U₀) ≤ 2 := by
  classical
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let U := W.subgroupOf D
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 U :=
    (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
  let C := centralizer (U : Set D)
  let q := QuotientGroup.mk' C
  rcases cubic_generated_action_prime_actors_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he with h23 |
    ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm,A,hA,hB,hcod,hcard,t,ht,ht2,htR,hcyc,hcr⟩
  · exact Or.inl h23
  let : Fact p.Prime := ⟨hp⟩
  let : R.Characteristic := hR.characteristic
  let R₀ := R.map (pCore p (D ⧸ C)).subtype
  let : R₀.Characteristic := hchar
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hAD : A ≤ D := hA.1.trans hTD
  have hA₀ : A.subgroupOf D ∈ thompsonFamily ((T : Subgroup G).subgroupOf D) 1 := by
    apply (thompsonFamily_map_iff_of_injective D.subtype D.subtype_injective
      ((T : Subgroup G).subgroupOf D) (A.subgroupOf D) 1).mp
    rw [map_subgroupOf_eq_of_le hTD,map_subgroupOf_eq_of_le hAD]
    exact hA
  have hUS : U ≤ (T : Subgroup G).subgroupOf D := by
    have hr := (cubic_generated_span_reduced h hab structural previous Y hYH he).le_pCore
    exact hr.trans (pCore_isPGroup.le_sylow_of_normal (T.subtype hTD))
  have ho := hp.odd_of_ne_two (by omega)
  have hfixed := near_maximum_prime_fixed_action ((T : Subgroup G).subgroupOf D) U
    hUS q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) hA₀ ho
    ((cubic_generated_local_structure h hab structural previous Y hYH he).2.1.stronglyQuasithin p hp ho)
    R₀ ((pCore_isPGroup (p := p) (G := D ⧸ C)).to_subgroup R |>.map (pCore p (D ⧸ C)).subtype)
    (fun hh => htR (hh ht))
  exact Or.inr ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm,A,hA,hB,hcod,hcard,
    t,ht,ht2,htR,hcyc,hcr,hfixed⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_action_prime_fixed_actors
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
            primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 ∧
          let R₀ := R.map (pCore p (D ⧸ C)).subtype
          let K₀ := B ⊓ centralizer (R₀ : Set (D ⧸ C))
          let U₀ := fixedSpace ρ K₀
          let I := restrictedSubgroup ρ U₀ B
          subspaceKernel ρ U₀ R₀ = ⊥ ∧ subspaceKernel ρ U₀ B = K₀ ∧
            IsElementaryTwo I ∧ Nat.card I ≤ 4 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ rank I + 1 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ 3 ∧
            IsCubic (subspaceImageRepresentation ρ U₀) I ∧
            cubicRatio (subspaceImageRepresentation ρ U₀) ≤ 2 := by
  apply cubic_generated_action_prime_fixed_actors_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The actual order-four interval supplies the moved-prime actors on its
literal cubic quotient, retaining Y, its exact star kernel, and the S₃ quotient. -/
theorem extraspecial_four_interval_cubic_prime_fixed_actors
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
              primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 ∧
          let R₀ := R.map (pCore p (D ⧸ C)).subtype
          let K₀ := B ⊓ centralizer (R₀ : Set (D ⧸ C))
          let U₀ := fixedSpace ρ K₀
          let I := restrictedSubgroup ρ U₀ B
          subspaceKernel ρ U₀ R₀ = ⊥ ∧ subspaceKernel ρ U₀ B = K₀ ∧
            IsElementaryTwo I ∧ Nat.card I ≤ 4 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ rank I + 1 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ 3 ∧
            IsCubic (subspaceImageRepresentation ρ U₀) I ∧
            cubicRatio (subspaceImageRepresentation ρ U₀) ≤ 2 := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
      hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove⟩ :=
    extraspecial_four_interval_cubic_thompson_one h hab structural previous faithful
      hex hcard hexp N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
    hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove,
    cubic_generated_action_prime_fixed_actors h hab structural previous faithful hn
      Y hYH hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
