module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.FourRankTwo
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.FourSylowMoving
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.Mathieu.M22.Properties.TwoRank

/-!
# The finite component shortlist in the nonsingular centralizer

In degree four the rank-two local obstruction eliminates every even
rank-two row. The moving elementary subgroup has rank six, excluding the
smaller Mathieu groups, J₁ and HS. Its normality in an actual component
Sylow subgroup excludes J₂ by the native normal-elementary bound.
Consequently only the actual central quotients L₅(2), M₂₄, He, Ru and J₄
remain. The earlier degree-five argument leaves only J₄.

The final chosen-module application supplies its compatible model and the
corrected L-conjugate, retaining the original residual and its relative
normal component. Excluding the displayed models and proving the normal
and parabolic branches remain with qt-d-double-natural-centralizers.
The pure-fusion family stays with qt-d-double-natural-pure-fusion, and
qt-d-1222-double-natural retains final source assembly.
Source: Aschbacher--Smith, 12.1.1 and A.2.3, printed pp.788 and32--33.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The degree-four sporadic obstruction has one of four actual central quotients. -/
theorem doubleNatural_four_adapted_component_sporadic_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ChapterA.Section02.IsTheoremCSporadicModel (K ⧸ center K) →
        Nonempty ((K ⧸ center K) ≃* Sporadic.Mathieu.M24) ∨
        Nonempty ((K ⧸ center K) ≃* Held.He) ∨
        Nonempty ((K ⧸ center K) ≃* Rudvalis.Model) ∨
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK hm
  have hr := D.doubleNatural_adapted_component_centralQuotient_rank h B S w hw K hK
  rcases hm with ⟨name,hne,⟨e⟩⟩ | ⟨e⟩
  · let : Finite name.Carrier := Finite.of_equiv (K ⧸ center K) e.toEquiv
    rw [primeRank_equiv 2 e] at hr
    cases name with
    | j4 => exact .inr (.inr (.inr ⟨e⟩))
    | j3 => exact (hne rfl).elim
    | m24 => exact .inl ⟨e⟩
    | he => exact .inr (.inl ⟨e⟩)
    | ru => exact .inr (.inr (.inl ⟨e⟩))
    | j2 => exact (D.doubleNatural_four_adapted_component_not_jankoTwo h B S w hw K hK ⟨e⟩).elim
    | m11 =>
      have hu : primeRank 2 Sporadic.Mathieu.M11 ≤ 5 :=
        primeRank_le_of_prime_pow_not_dvd (by rw [Sporadic.Mathieu.m11_order]; decide)
      change 2*(4-1) ≤ primeRank 2 Sporadic.Mathieu.M11 at hr
      omega
    | m12 =>
      have hu := Sporadic.Mathieu.m12_twoRank_le_three
      change 2*(4-1) ≤ primeRank 2 Sporadic.Mathieu.M12 at hr
      omega
    | m22 =>
      have hu := Sporadic.Mathieu.m22_twoRank_le_four
      change 2*(4-1) ≤ primeRank 2 Sporadic.Mathieu.M22 at hr
      omega
    | m23 =>
      have hu := Sporadic.Mathieu.m23_twoRank_le_four
      change 2*(4-1) ≤ primeRank 2 Sporadic.Mathieu.M23 at hr
      omega
    | hs =>
      have hu := Sporadic.LeechRelated.HS.twoRank_le_four
      change 2*(4-1) ≤ primeRank 2 Sporadic.LeechRelated.HS.Carrier at hr
      omega
  · obtain ⟨e⟩ := e
    rw [primeRank_equiv 2 e] at hr
    have hu : primeRank 2 Janko1.Model ≤ 5 :=
      primeRank_le_of_prime_pow_not_dvd (by rw [Janko1.card_model]; decide)
    omega

/-- Every component in degree four is one of the five remaining concrete models. -/
theorem doubleNatural_four_adapted_component_finite_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ClassicalGroup.IsPSL (K ⧸ center K) 5 2 ∨
        Nonempty ((K ⧸ center K) ≃* Sporadic.Mathieu.M24) ∨
        Nonempty ((K ⧸ center K) ≃* Held.He) ∨
        Nonempty ((K ⧸ center K) ≃* Rudvalis.Model) ∨
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK
  rcases D.doubleNatural_adapted_component_remaining_nonbender_models h B S w hw K hK with
    ⟨f,hf⟩ | ⟨_,hl⟩ | hs
  · exact (Nonsingular.four_component_not_rankTwo h D B S w hw K hK f hf).elim
  · exact .inl hl
  · exact .inr (D.doubleNatural_four_adapted_component_sporadic_models h B S w hw K hK hs)

/-- Both degrees now reduce to five concrete models, four of which require degree four. -/
theorem doubleNatural_adapted_component_finite_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (n = 4 ∧ (ClassicalGroup.IsPSL (K ⧸ center K) 5 2 ∨
          Nonempty ((K ⧸ center K) ≃* Sporadic.Mathieu.M24) ∨
          Nonempty ((K ⧸ center K) ≃* Held.He) ∨
          Nonempty ((K ⧸ center K) ≃* Rudvalis.Model))) ∨
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK
  rcases B.degree with hn | hn
  · subst n
    rcases D.doubleNatural_four_adapted_component_finite_models h B S w hw K hK with
      hl | hm | hh | hr | hj
    · exact .inl ⟨rfl,.inl hl⟩
    · exact .inl ⟨rfl,.inr (.inl hm)⟩
    · exact .inl ⟨rfl,.inr (.inr (.inl hh))⟩
    · exact .inl ⟨rfl,.inr (.inr (.inr hr))⟩
    · exact .inr hj
  · subst n
    exact .inr (D.doubleNatural_five_adapted_component_is_jankoFour h B S w hw K hK)

/-- The source characteristic-two obstruction retains its normal component and exact finite model. -/
theorem doubleNatural_adapted_characteristic_or_finite_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) ∨
      ∃ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) ∧
        (K.subgroupOf (B.pointCentralizer w)).Normal ∧ B.pointResidual w ≤ K ∧
        2*(n-1) ≤ primeRank 2 (K ⧸ center K) ∧
        ((n = 4 ∧ (ClassicalGroup.IsPSL (K ⧸ center K) 5 2 ∨
          Nonempty ((K ⧸ center K) ≃* Sporadic.Mathieu.M24) ∨
          Nonempty ((K ⧸ center K) ≃* Held.He) ∨
          Nonempty ((K ⧸ center K) ≃* Rudvalis.Model))) ∨
        Nonempty ((K ⧸ center K) ≃* Janko4.Model)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  rcases D.doubleNatural_adapted_characteristic_or_normal_component h B S w hw with
    hc | ⟨K,hK,hn,hRK,_⟩
  · exact .inl hc
  · exact .inr ⟨K,hK,hn,hRK,
      D.doubleNatural_adapted_component_centralQuotient_rank h B S w hw K hK,
      D.doubleNatural_adapted_component_finite_models h B S w hw K hK⟩

/-- The literal chosen-module application supplies the compatible model and corrected point marking. -/
theorem doubleNatural_nonsingular_characteristic_or_finite_models_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ w : componentOrbit V (T : Subgroup G), B.quadratic (Additive.ofMul w) = 1 →
      ∃ l : L, ∃ w' : componentOrbit V (T : Subgroup G),
        (w' : G) = (l : G) * (w : G) * (l : G)⁻¹ ∧ B.quadratic (Additive.ofMul w') = 1 ∧
        (generalizedFitting (B.pointCentralizer w') = pCore 2 (B.pointCentralizer w') ∨
        ∃ K : Subgroup G, IsComponentIn K (B.pointCentralizer w') ∧
          (K.subgroupOf (B.pointCentralizer w')).Normal ∧ B.pointResidual w' ≤ K ∧
          2*(n-1) ≤ primeRank 2 (K ⧸ center K) ∧
          ((n = 4 ∧ (ClassicalGroup.IsPSL (K ⧸ center K) 5 2 ∨
            Nonempty ((K ⧸ center K) ≃* Sporadic.Mathieu.M24) ∨
            Nonempty ((K ⧸ center K) ≃* Held.He) ∨
            Nonempty ((K ⧸ center K) ≃* Rudvalis.Model))) ∨
          Nonempty ((K ⧸ center K) ≃* Janko4.Model))) := by
  let := D.doubledOrbit_elementary h
  intro w hw
  obtain ⟨S⟩ := B.nonempty_sourceModel
  obtain ⟨l,w',he,hw'⟩ := D.doubleNatural_adaptedPoint h B S w hw
  exact ⟨l,w',he,hw'.nonsingular,
    D.doubleNatural_adapted_characteristic_or_finite_models h B S w' hw'⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
