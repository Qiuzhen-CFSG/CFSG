module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.AlternatingStarSource
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry
public import Theory.SpecificGroups.SL3.RadicalNormalizer
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSpecialLinear
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.SymplecticFour.SixSectionNormalizer
public import Theory.AtlasPort.LinearGroups.G2.SixSectionNormalizer

/-!
# Excluding the degree-five rank-two star components

For every large star component, the proved C.2.7 offender placement makes
its intersection with the original radical a nontrivial radical subgroup.
The actual point residual normalizes that intersection. Its perfect image
retains its L4(2) two-core quotient, hence has cubic rank at least two.

In SL3(q), Sp4(q), and G2(q), the literal radical normalizer places this
perfect image in a rank-one Levi extension, whose cubic rank is at most
one. The small SL3(2) row is excluded by its order. The SL3 scalar center
and the possible central star kernel are retained throughout. No full
Sylow placement in the ambient point centralizer is assumed.

`FiveRankTwoStarSource` applies this to the original nonsingular centralizer
and degree-five closure conclusions. The remaining SL5(2) star argument,
ordinary J4 exclusion, and later fusion/closure steps remain with
qt-d-double-natural-centralizers and its existing external producers.
Source: Aschbacher--Smith 12.1.1, printed pp.788--789, and C.2.7,
pp.145--147. The imported intrinsic model proofs retain their attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterC.C27Source Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem five_star_local_data
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        ∀ {X : Type*} [Group X] [Finite X], (starImage K Q K ≃* X) → 40320 < Nat.card X →
        ∃ P U : Subgroup X, Group.IsPerfect P ∧ 2 ≤ primeRank 3 P ∧
          IsPRadical 2 U ∧ P ≤ normalizer (U : Set X) := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hRK hi X _ _ e hlarge
  let R := B.pointResidual w
  let J := K ⊔ Q
  let C := starImage K Q K
  let A := starImage K Q R
  let U := (starImage K Q Q).subgroupOf C
  let E := A.subgroupOf C
  have hRJ : R ≤ J := hRK.trans le_sup_left
  have hRM : R ≤ B.localPointCentralizer w := le_inf (B.pointResidual_le_normalizer w)
    ((B.pointResidual_le w).trans inf_le_right)
  let := (S.nonsingular_residual_local_cComponent w hw.nonsingular).perfect
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRM).toMonoidHom) (subgroupOfEquivOfLe hRM).surjective
  let : Group.IsPerfect (R.subgroupOf J) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRJ).symm.toMonoidHom) (subgroupOfEquivOfLe hRJ).symm.surjective
  let : Group.IsPerfect A := Group.IsPerfect.map (QuotientGroup.mk' (starKernel K Q))
  have hAC : A ≤ C := map_mono (comap_mono hRK)
  let a := subgroupOfEquivOfLe hAC
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  have hr : 2 ≤ primeRank 3 E := by
    rw [primeRank_equiv 3 a]
    obtain ⟨_,⟨eA⟩⟩ := D.doubleNatural_adapted_C27_residual_marking h B S w hw K hRK hi
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 A) pCore_isPGroup,
      primeRank_equiv 3 (eA.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have hU : IsPRadical 2 U := (star_intersection_placement_from_source_of_large_order hi
    (by rwa [Nat.card_congr e.toEquiv])).1
  have hRQ : R ≤ normalizer (Q : Set G) :=
    ((B.pointResidual_le w).trans inf_le_left).trans
      (le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _
          (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))))
  have hn : E ≤ normalizer (U : Set C) := by
    intro x hx
    have hxQ : (x : StarQuotient K Q) ∈ normalizer (starImage K Q Q : Set _) := by
      obtain ⟨r,hr,he⟩ := hx
      change (QuotientGroup.mk' (starKernel K Q)) r = (x : StarQuotient K Q) at he
      rw [←he]
      apply (Q.subgroupOf J).le_normalizer_map (QuotientGroup.mk' (starKernel K Q))
      apply mem_map_of_mem
      rw [←subgroupOf_normalizer_eq (show Q ≤ J from le_sup_right)]
      exact hRQ hr
    exact fun z => hxQ z
  let b := E.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨E.map e.toMonoidHom,U.map e.toMonoidHom,
    Group.IsPerfect.ofSurjective (f := b.toMonoidHom) b.surjective,?_,hU.map_equiv e,?_⟩
  · rwa [←primeRank_equiv 3 b]
  · exact (map_mono hn).trans (le_normalizer_map e.toMonoidHom)


/-- The original degree-five residual excludes all rank-two star rows. -/
theorem doubleNatural_five_adapted_C27_star_linearFive
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        Nonempty (starImage K Q K ≃* SL(5,ZMod 2)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hRK hi
  cases D.doubleNatural_five_adapted_C27_star_models h B S w hw K hRK hi with
  | linearThree F e =>
    by_cases hd : F.degree = 1
    · let A := starImage K Q (B.pointResidual w)
      let C := starImage K Q K
      have hAC : A ≤ C := map_mono (comap_mono hRK)
      obtain ⟨_,⟨a⟩⟩ := D.doubleNatural_adapted_C27_residual_marking h B S w hw K hRK hi
      have h5 : 5 ∣ Nat.card (A ⧸ pCore 2 A) := by
        rw [Nat.card_congr (a.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).toEquiv,
          nat_card_alternatingGroup,Nat.card_fin]
        norm_num [Nat.factorial]
      have hh := h5.trans ((card_quotient_dvd_card (pCore 2 A)).trans (card_dvd_of_le hAC))
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,
        F.card_eq,hd] at hh
      norm_num at hh
    have hdeg : 1 < F.degree := by have := F.degree_pos; omega
    have hq : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hdeg
    have hlarge : 40320 < Nat.card SL(3,F.Carrier) := by
      rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
      apply lt_of_lt_of_le (by norm_num : 40320 < 4^3 * (4^3-1) * (4^2-1))
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    obtain ⟨P,U,hperf,hr,hU,hn⟩ := five_star_local_data h D B S w hw K hRK hi e hlarge
    let := hperf
    have hPn : P ≠ ⊥ := by
      intro he
      subst P
      have hz : primeRank 3 (⊥ : Subgroup SL(3,F.Carrier)) = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr (by simp)
      omega
    obtain ⟨a,ha⟩ := Matrix.PSL3.LinearThree.RadicalNormalizer.radical_normalizer_frame_of_perfect
      U P hU hPn hn hdeg F.card_eq
    let j := (Matrix.HigherLinear.SubspaceTransport.slConj a).toMonoidHom.comp P.subtype
    have hj : j.range ≤ (normalizer (U : Set _)).map
        (Matrix.HigherLinear.SubspaceTransport.slConj a).toMonoidHom := by
      rintro _ ⟨x,rfl⟩
      exact mem_map_of_mem _ (hn x.property)
    have hlocal : j.range ≤ Matrix.PSL3.LinearThree.pointParabolicSL F.Carrier ∨
        j.range ≤ Matrix.PSL3.LinearThree.lineParabolicSL F.Carrier := by
      rcases ha with ha | ha
      · exact .inl (ha ▸ hj)
      · exact .inr (ha ▸ hj)
    have hb := Matrix.PSL3.LinearThree.PerfectSubgroups.perfect_parabolicSL_rank
      (by decide : Odd 3) hq j
      ((Matrix.HigherLinear.SubspaceTransport.slConj a).injective.comp P.subtype_injective)
      hlocal
    omega
  | symplectic F hdeg e =>
    have hq : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hdeg
    have hlarge : 40320 < Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier) := by
      rw [Theory.SpecificGroups.SymplecticFour.card_sp]
      apply lt_of_lt_of_le (by norm_num : 40320 < 4^4 * (4^2-1) * (4^4-1))
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hq 4)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1)
    obtain ⟨P,U,hperf,hr,hU,hn⟩ := five_star_local_data h D B S w hw K hRK hi e hlarge
    let := hperf
    exact (hU.1 (Theory.SpecificGroups.SymplecticFour.two_subgroup_eq_bot_of_perfect_odd_rank_two
      P U (by decide : Odd 3) hr hU.isPGroup hn)).elim
  | g2 F hdeg e =>
    have hq : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hdeg
    have hlarge : 40320 < Nat.card (Atlas.G2.Model F.Carrier) := by
      rw [Atlas.G2.card_Model]
      apply lt_of_lt_of_le (by norm_num : 40320 < 4^6 * (4^6-1) * (4^2-1))
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    obtain ⟨P,U,hperf,hr,hU,hn⟩ := five_star_local_data h D B S w hw K hRK hi e hlarge
    let := hperf
    exact (hU.1 (Atlas.G2.two_subgroup_eq_bot_of_perfect_odd_rank_two
      (by omega) P U (by decide : Odd 3) hr hU.isPGroup hn)).elim
  | linearFiveTwo e => exact ⟨e⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
