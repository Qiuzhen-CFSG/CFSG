module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicMovingThompson
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicTwoThree

/-!
# Odd-prime reduction for the moving cubic completion

The original J₁(T) commutator supplies a near-maximum elementary actor
on each moved odd prime core. Its fixed-space restriction retains the
literal quotient representation. The small-support classification forces
prime five, whose invariant cyclic factors contradict movement by L₂.
Thus D/C_D(⟨V₁^D⟩) is a {2,3}-group and the action factors through
D/O₃′(D). CubicMovingModels uses this exact factorization to keep the
original Goldschmidt intersection in the second quotient.

Source: Aschbacher–Smith, 14.5.11, printed pp.1015–1016,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open ChapterB Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u

private theorem exists_moved_prime_core
    {D E : Type u} [Group D] [Finite D] [Group E] [Finite E] {C : GroupClass.{u}}
    (hE : IsSQTK C E) (f : E →* D) (hf : Function.Surjective f)
    (hs : Group.IsSolvable D) {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B) (hc : pCore 2 D = ⊥)
    (hout : ¬ IsPiGroup twoThreePrimes D) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧
      ¬ (pResidual 2 A).map A.subtype ≤ centralizer (pCore p D : Set D) := by
  by_contra! hn
  apply hout
  apply ChapterF.SourceAssembly.isTwoThreeGroup_of_left_residual_centralizes_fitting_residual
    hE f hf hs ht
  apply le_centralizer_iff.mpr
  rw [fitting_pResidual_eq_sup_prime_cores]
  apply iSup_le
  intro p
  apply iSup_le
  intro hp3
  by_cases hp2 : p.1.1 = 2
  · rw [hp2,hc]
    exact bot_le
  have hprime : p.1.1.Prime := Fact.out
  have hpgt : 3 < p.1.1 := by
    have h2 := hprime.two_le
    omega
  exact le_centralizer_iff.mp (hn p.1.1 hprime hpgt)

private theorem coprime_card_of_twoThree {X : Type*} [Group X] [Finite X]
    (hX : IsPiGroup twoThreePrimes X) {p : ℕ} (hp : p.Prime) (hbig : 3 < p) :
    Nat.Coprime p (Nat.card X) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hh := (IsPiGroup_iff _ _).mp hX ⟨p,hp⟩ hd
  change p = 2 ∨ p = 3 at hh
  rcases hh with hh | hh <;> omega

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem cubic_generated_action_prime_reduction_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    let X := ((F.Li L 2).subgroupOf D).map q
    let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
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
        X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a := by
  classical
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  let X := ((F.Li L 2).subgroupOf D).map q
  let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
  change IsPiGroup twoThreePrimes (D ⧸ C) ∨ _
  by_cases h23 : IsPiGroup twoThreePrimes (D ⧸ C)
  · exact Or.inl h23
  apply Or.inr
  let A := ((F.P L).subgroupOf D).map q
  let B := ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q
  have ht := cubic_generated_action_triple_of_moving_plane h hab structural previous Y hYH hmovePlane hYp hYT he
  have hs := cubic_generated_solvable_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he
  let : Group.IsSolvable D := hs
  have hsq := (cubic_generated_local_structure h hab structural previous Y hYH he).2.1
  have hres : (pResidual 2 A).map A.subtype = X := by
    rw [←map_embedded_pResidual]
    exact congrArg (map q) (cubic_action_residuals (F := F) h structural Y hYp hYT).1
  obtain ⟨p,hp,hbig,hm⟩ := exists_moved_prime_core hsq q
    (QuotientGroup.mk'_surjective C) inferInstance ht.2.1 ht.2.2 h23
  rw [hres] at hm
  let : Fact p.Prime := ⟨hp⟩
  have hXA : X ≤ A := hres ▸ map_subtype_le (pResidual 2 A)
  have hX23 : IsPiGroup twoThreePrimes X :=
    (ChapterF.SourceAssembly.local_isTwoThreeGroup ht.2.1).of_injective
      (inclusion hXA) (inclusion_injective hXA)
  have hcomm : ⁅X,J⁆ = X := (cubic_generated_thompson_one_action_of_moving_plane
    h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he).1
  obtain ⟨R,hR,hnc,hr,heq⟩ := supercritical_commutator_movement X J (pCore p (D ⧸ C))
    (hp.odd_of_ne_two (by omega)) pCore_isPGroup
    (coprime_card_of_twoThree hX23 hp hbig) hcomm hm
  let : R.Characteristic := hR.characteristic
  refine ⟨p,hp,R,hR,hbig,inferInstance,hnc,?_,hr,heq⟩
  intro hz
  apply hr
  apply (Subgroup.map_eq_bot_iff _).mpr
  intro x hx
  apply MulEquiv.ext
  intro r
  apply Subtype.ext
  apply Subtype.ext
  change x * (r.val : D ⧸ C) * x⁻¹ = (r.val : D ⧸ C)
  have hc := hz hx (r.val : D ⧸ C) (mem_map_of_mem (pCore p (D ⧸ C)).subtype r.property)
  rw [←hc,mul_inv_cancel_right]

theorem cubic_generated_moved_prime_actor_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
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
  have hc := (cubic_generated_thompson_one_action_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he).1
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

theorem cubic_generated_action_prime_actors_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
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
  rcases cubic_generated_action_prime_reduction_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he with h23 | ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm⟩
  · exact Or.inl h23
  let : Fact p.Prime := ⟨hp⟩
  let : R.Characteristic := hR.characteristic
  let : (R.map (pCore p (D ⧸ C)).subtype).Characteristic := hchar
  refine Or.inr ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm,?_⟩
  obtain ⟨A,hA,hB,hcod,t,ht,ht2,htR,hcyc,hcr⟩ :=
    cubic_generated_moved_prime_actor_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he p hp (R.map (pCore p (D ⧸ C)).subtype) inferInstance
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

theorem cubic_generated_action_prime_fixed_actors_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
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
  rcases cubic_generated_action_prime_actors_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he with h23 |
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

theorem cubic_generated_action_prime_five_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
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
            cubicRatio (subspaceImageRepresentation ρ U₀) ≤ 2 ∧
            p = 5 ∧ Nat.card R = 25 ∧ IsElementaryAbelian 5 R ∧
            Nonempty (R ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 5))) ∧
            rank I = 1 ∧ Nat.card I = 2 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I = 2 ∧
            Nat.card (⁅R₀,B⁆ : Subgroup (D ⧸ C)) = 5 ∧
            Module.finrank (ZMod 2) (subspaceCommutator ρ U₀ ⁅R₀,B⁆) = 4 := by
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
  rcases cubic_generated_action_prime_fixed_actors_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he with h23 |
    ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm,A,hA,hB,hcod,hcard,t,ht,ht2,htR,hcyc,hcr,
      hkR,hkB,hI,hcardI,hcodI,hcod3,hcubI,hratio⟩
  · exact Or.inl h23
  let : Fact p.Prime := ⟨hp⟩
  let : R.Characteristic := hR.characteristic
  let R₀ := R.map (pCore p (D ⧸ C)).subtype
  let B := (A.subgroupOf D).map q
  let : R₀.Characteristic := hchar
  let : IsElementaryAbelian 2 B := hB.2
  have hRp : IsPGroup p R₀ :=
    (pCore_isPGroup (p := p) (G := D ⧸ C)).to_subgroup R |>.map (pCore p (D ⧸ C)).subtype
  obtain ⟨hp5,hrI,hcI,hdI,hcomm5,hdim⟩ := ChapterD.prime_fixed_small_actor ρ
    (NormalElementaryQuotient.representation_injective _ _ _ _) hbig R₀ B hRp hI hcubI hcodI
  let eR : R ≃* R₀ := R.equivMapOfInjective
    (pCore p (D ⧸ C)).subtype (pCore p (D ⧸ C)).subtype_injective
  have heR : Monoid.exponent R₀ ∣ p :=
    (Monoid.exponent_dvd_of_monoidHom eR.symm.toMonoidHom eR.symm.injective).trans hR.exponent_dvd_p
  have hnR : ¬ IsCyclic R₀ := by
    intro hc
    let : IsCyclic R₀ := hc
    exact hncyc (isCyclic_of_injective eR.toMonoidHom eR.injective)
  obtain ⟨hcR,helR⟩ := elementary_plane_of_prime_commutator_cyclic_fixed
    (by omega : p ≠ 2) R₀ B hRp (IsElementaryAbelian.isPGroup 2 B)
    heR hnR t ht hcyc (hcomm5.trans hp5.symm)
  have hcR' : Nat.card R = 25 := by
    rw [Nat.card_congr eR.toEquiv,hcR,hp5]
    rfl
  let : IsElementaryAbelian p R₀ := helR
  have heR' : IsElementaryAbelian 5 R := by
    rw [←hp5]
    exact IsElementaryAbelian.of_injective eR.toMonoidHom eR.injective
  let : IsElementaryAbelian 5 R := heR'
  have heqR := IsElementaryAbelian.nonempty_mulEquiv_plane_of_card
    (p := 5) (show Nat.card R = 5 ^ 2 from hcR')
  exact Or.inr ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm,A,hA,hB,hcod,hcard,
    t,ht,ht2,htR,hcyc,hcr,hkR,hkB,hI,hcardI,hcodI,hcod3,hcubI,hratio,
    hp5,hcR',heR',heqR,hrI,hcI,hdI,hcomm5,hdim⟩

theorem cubic_generated_action_twoThree_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
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
  rcases cubic_generated_action_prime_five_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he with h23 |
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
    have hh := cubic_generated_thompson_centralizes_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he
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
  have htriple := cubic_generated_action_triple_of_moving_plane h hab structural previous Y hYH hmovePlane hYp hYT he
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

theorem cubic_generated_action_core_kernel_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
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
  have h23 := cubic_generated_action_twoThree_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he
  have ht := cubic_generated_action_triple_of_moving_plane h hab structural previous Y hYH hmovePlane hYp hYT he
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


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
