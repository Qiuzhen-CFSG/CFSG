module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicPrimeFive
public import CFSG.Quasithin.ChapterB.Section02.Thompson.FixedSaturation
public import CFSG.Quasithin.ChapterD.Section02.QuinticPlaneExclusion
public import Theory.GroupTheory.TwoThreeCoreKernel

/-!
# The original cubic action quotient is a {2,3}-group

The only remaining moved odd-prime branch is a quintic plane. Equality in
the near-maximum fixed-space bound, together with J(T)'s centralization
of the literal point span, kills the restricted actor kernel. The resulting
involution has fixed codimension two on the whole span. Its canonical
order-five support is normalized by the two-perfect cubic image, forcing
that image to centralize the quintic plane and contradicting its movement.

Thus the actual quotient D/C_D(W) is a {2,3}-group. Its trivial two-core
places O_{3′}(D) in C_D(W), giving the compatible surjection from the original
prime-to-three core quotient. The order-four chief interval supplies all
premises while retaining Y, its exact star kernel and its S₃ quotient.

These are the two clauses of 14.5.11 in the original normal-point branch.
The later solvable containment and residual classification remain separate.
Source: Aschbacher–Smith 14.5.11, printed pp.1015–1016, and the
14.7.20(2) interval application, p.1049, refs/quasithin.pdf.
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
/-- Exclusion of the last moved-prime branch for the literal cubic action. -/
theorem cubic_generated_action_twoThree_of_normalizes_point
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
    IsPiGroup twoThreePrimes (D ⧸ C) := by
  classical
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let U := W.subgroupOf D
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 U :=
    (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
  let C := centralizer (U : Set D)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  rcases cubic_generated_action_prime_five_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he with h23 |
    ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm,A,hA,hB,hcod,hcard,t,ht,ht2,htR,hcyc,hcr,
      hkR,hkB,hI,hcardI,hcodI,hcod3,hcubI,hratio,
      hp5,hcR,helR,heR,hrI,hcI,hdI,hcomm5,hdim⟩
  · exact h23
  subst p
  let : R.Characteristic := hR.characteristic
  let R₀ := R.map (pCore 5 (D ⧸ C)).subtype
  let : R₀.Characteristic := hchar
  let : IsElementaryAbelian 5 R := helR
  let : IsElementaryAbelian 5 R₀ := IsElementaryAbelian.map _
  let B := (A.subgroupOf D).map q
  let K₀ := B ⊓ centralizer (R₀ : Set (D ⧸ C))
  let U₀ := fixedSpace ρ K₀
  let I := restrictedSubgroup ρ U₀ B
  let : IsElementaryAbelian 2 B := hB.2
  change rank I = 1 at hrI
  change Nat.card I = 2 at hcI
  change fixedCodim (subspaceImageRepresentation ρ U₀) I = 2 at hdI
  change subspaceKernel ρ U₀ B = K₀ at hkB
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
  have hJC : elementaryAbelianMaxJ ((T : Subgroup G).subgroupOf D) ≤ centralizer (U : Set D) := by
    have hh := cubic_generated_thompson_centralizes_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he
    intro a ha w hw
    have ha' : (a : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) := by
      have hm := mem_map_of_mem D.subtype ha
      rwa [←elementaryAbelianMaxJ_map_injective D.subtype D.subtype_injective,
        map_subgroupOf_eq_of_le hTD] at hm
    exact Subtype.ext (hh ha' w hw)
  have hkzero : K₀ = ⊥ := near_maximum_fixed_saturated_kernel
    ((T : Subgroup G).subgroupOf D) U hUS hJC q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) hA₀
    K₀ inf_le_left hkB (by change fixedCodim (subspaceImageRepresentation ρ U₀) I = rank I + 1; omega)
  have hBs : B ≤ subspaceStabilizer ρ U₀ :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ B K₀
      (commutator_eq_bot_iff_le_centralizer.mpr
        (B.le_centralizer.trans (centralizer_le inf_le_left)))
  have hcardB : Nat.card B = 2 := by
    have hh := card_subspaceKernel_mul_image ρ U₀ B hBs
    rw [hkB,hkzero,card_bot,one_mul] at hh
    exact hh.symm.trans hcI
  have hdB : fixedCodim ρ B = 2 := by
    have hh := fixedCodim_restrictedSubgroup ρ U₀ B hBs
    have hu : U₀ = ⊤ := by dsimp only [U₀]; rw [hkzero,fixedSpace_bot]
    rw [hu,top_inf_eq,finrank_top] at hh
    change fixedCodim (subspaceImageRepresentation ρ U₀) (restrictedSubgroup ρ U₀ B) = 2 at hdI
    rw [hu] at hdI
    have hd := hh.symm.trans hdI
    have htotal := fixedCodim_add_finrank ρ B
    omega
  have hBt : zpowers t = B := eq_of_le_of_card_ge (zpowers_le.mpr ht) (by
    rw [hcardB,Nat.card_zpowers,ht2])
  let X := ((F.Li L 2).subgroupOf D).map q
  let P := ((F.P L).subgroupOf D).map q
  have htriple := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  have hres : (pResidual 2 P).map P.subtype = X := by
    rw [←map_embedded_pResidual]
    exact congrArg (map q) (cubic_action_residuals (F := F) h structural Y hYp hYT).1
  have hX23 : IsPiGroup twoThreePrimes X :=
    (ChapterF.SourceAssembly.local_isTwoThreeGroup htriple.2.1).of_injective
      (inclusion (hres ▸ map_subtype_le (pResidual 2 P))) (inclusion_injective _)
  have hXp : IsPPerfect 2 X := by
    rw [←hres]
    exact (isPPerfect_pResidual (G := P) 2).of_surjective _ (P.subtype.subgroupMap_surjective _)
  have hR0 : Nat.card R₀ = 25 := by rw [card_map_of_injective (pCore 5 (D ⧸ C)).subtype_injective,hcR]
  have hcop : Nat.Coprime (Nat.card X) (Nat.card R₀) := by
    rw [hR0]
    change Nat.Coprime (Nat.card X) (5 ^ 2)
    apply Nat.Coprime.pow_right (n := 2)
    apply Nat.Coprime.symm
    apply Nat.prime_five.coprime_iff_not_dvd.mpr
    intro hh
    have hh := (IsPiGroup_iff _ _).mp hX23 ⟨5,Nat.prime_five⟩ hh
    change 5 = 2 ∨ 5 = 3 at hh
    omega
  exact False.elim (hm (ChapterD.quintic_plane_small_actor_centralizes ρ
    (NormalElementaryQuotient.representation_injective _ _ _ _) q
    (QuotientGroup.mk'_surjective C)
    ((cubic_generated_local_structure h hab structural previous Y hYH he).2.1.stronglyQuasithin
      5 Nat.prime_five (by decide)) R₀ B X hR0 hB hkzero t ht2 hBt hdB hXp hcop))

/-- The original full point-normality interface. -/
theorem cubic_generated_action_twoThree
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
    IsPiGroup twoThreePrimes (D ⧸ C) := by
  apply cubic_generated_action_twoThree_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- Both clauses of original 14.5.11, with the literal surjection from the prime-to-three core quotient. -/
theorem cubic_generated_action_core_kernel_of_normalizes_point
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
    IsPiGroup twoThreePrimes (D ⧸ C) ∧ pPrimeCore 3 D ≤ C ∧
      ∃ f : (D ⧸ pPrimeCore 3 D) →* (D ⧸ C), Function.Surjective f ∧
        f.comp (QuotientGroup.mk' (pPrimeCore 3 D)) = QuotientGroup.mk' C := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let U := W.subgroupOf D
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (U : Set D)
  have h23 := cubic_generated_action_twoThree_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he
  have ht := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  have hk : pPrimeCore 3 D ≤ C := by
    have hh := pPrimeCore_three_le_kernel_of_twoThree (QuotientGroup.mk' C)
      (QuotientGroup.mk'_surjective C) h23 ht.2.2
    rwa [QuotientGroup.ker_mk'] at hh
  let f := QuotientGroup.map (pPrimeCore 3 D) C (MonoidHom.id D) hk
  refine ⟨h23,hk,f,?_,?_⟩
  · exact QuotientGroup.map_surjective_of_surjective (pPrimeCore 3 D) C
      (MonoidHom.id D) (QuotientGroup.mk'_surjective C) hk
  · ext x
    rfl

/-- The original full point-normality interface. -/
theorem cubic_generated_action_core_kernel
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
    IsPiGroup twoThreePrimes (D ⧸ C) ∧ pPrimeCore 3 D ≤ C ∧
      ∃ f : (D ⧸ pPrimeCore 3 D) →* (D ⧸ C), Function.Surjective f ∧
        f.comp (QuotientGroup.mk' (pPrimeCore 3 D)) = QuotientGroup.mk' C := by
  apply cubic_generated_action_core_kernel_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- Original order-four interval application of 14.5.11, preserving Y,
its actual star kernel and its S₃ quotient. -/
theorem extraspecial_four_interval_cubic_twoThree
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
      IsPiGroup twoThreePrimes (D ⧸ C) ∧ pPrimeCore 3 D ≤ C ∧
        ∃ f : (D ⧸ pPrimeCore 3 D) →* (D ⧸ C), Function.Surjective f ∧
          f.comp (QuotientGroup.mk' (pPrimeCore 3 D)) = QuotientGroup.mk' C := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
      hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove⟩ :=
    extraspecial_four_interval_cubic_thompson_one h hab structural previous faithful
      hex hcard hexp N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
    hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove,
    cubic_generated_action_core_kernel h hab structural previous faithful hn
      Y hYH hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
