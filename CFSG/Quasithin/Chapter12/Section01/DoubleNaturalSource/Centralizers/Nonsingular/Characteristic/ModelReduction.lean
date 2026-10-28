module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.BenderExclusion
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.FiveRankTwo
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.FiveSporadic

/-!
# Source reduction of the ordinary-component obstruction

The local markings exclude the Bender rows in both degrees. In degree
five the L₄(2) local section excludes every even rank-two row, and the
faithful moving subgroup excludes all sporadic rows except J₄. Hence a
failure of characteristic two in degree five produces an actual normal
ordinary component with central quotient J₄ and containing the original
point residual. The chosen-module application constructs its source model
and corrected L-conjugate.

The J₄ exclusion, the degree-four remaining models, and the normal and
parabolic branches of 12.1.1 remain with qt-d-double-natural-centralizers.
The pure-fusion family remains with qt-d-double-natural-pure-fusion and
final assembly with qt-d-1222-double-natural; no source premise is discharged
by this bookkeeping. Source: Aschbacher--Smith, 12.1.1, printed p.788.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In either degree the surviving models have no rank-one or odd-field row. -/
theorem doubleNatural_adapted_component_remaining_nonbender_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (∃ f, ChapterA.Section02.IsTheoremCRankTwoModel (K ⧸ center K) f) ∨
        (n = 4 ∧ ClassicalGroup.IsPSL (K ⧸ center K) 5 2) ∨
        ChapterA.Section02.IsTheoremCSporadicModel (K ⧸ center K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK
  exact (D.doubleNatural_adapted_component_remaining_models h B S w hw K hK).resolve_left
    (D.doubleNatural_adapted_component_not_bender h B S w hw K hK)

/-- Every surviving ordinary component in degree five has actual central quotient J₄. -/
theorem doubleNatural_five_adapted_component_is_jankoFour
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK
  rcases D.doubleNatural_adapted_component_remaining_nonbender_models h B S w hw K hK with
    ⟨f,hf⟩ | ⟨hn,_⟩ | hs
  · exact (D.doubleNatural_five_adapted_component_not_rankTwo h B S w hw K hK f hf).elim
  · omega
  · exact D.doubleNatural_five_adapted_component_sporadic_is_jankoFour h B S w hw K hK hs

/-- The degree-five characteristic-two obstruction is now a normal J₄ component with the original residual inside it. -/
theorem doubleNatural_five_adapted_characteristic_or_jankoFour
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) ∨
      ∃ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) ∧
        (K.subgroupOf (B.pointCentralizer w)).Normal ∧ B.pointResidual w ≤ K ∧
        8 ≤ primeRank 2 (K ⧸ center K) ∧
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  rcases D.doubleNatural_adapted_characteristic_or_normal_component h B S w hw with
    hc | ⟨K,hK,hn,hRK,_⟩
  · exact .inl hc
  · exact .inr ⟨K,hK,hn,hRK,
      D.doubleNatural_adapted_component_centralQuotient_rank h B S w hw K hK,
      D.doubleNatural_five_adapted_component_is_jankoFour h B S w hw K hK⟩

/-- The degree-five source application discharges SourceModel and the adapted-point choice. -/
theorem doubleNatural_five_nonsingular_characteristic_or_jankoFour_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ w : componentOrbit V (T : Subgroup G), B.quadratic (Additive.ofMul w) = 1 →
      ∃ l : L, ∃ w' : componentOrbit V (T : Subgroup G),
        (w' : G) = (l : G) * (w : G) * (l : G)⁻¹ ∧ B.quadratic (Additive.ofMul w') = 1 ∧
        (generalizedFitting (B.pointCentralizer w') = pCore 2 (B.pointCentralizer w') ∨
        ∃ K : Subgroup G, IsComponentIn K (B.pointCentralizer w') ∧
          (K.subgroupOf (B.pointCentralizer w')).Normal ∧ B.pointResidual w' ≤ K ∧
          8 ≤ primeRank 2 (K ⧸ center K) ∧
          Nonempty ((K ⧸ center K) ≃* Janko4.Model)) := by
  let := D.doubledOrbit_elementary h
  intro w hw
  obtain ⟨S⟩ := B.nonempty_sourceModel
  obtain ⟨l,w',he,hw'⟩ := D.doubleNatural_adaptedPoint h B S w hw
  exact ⟨l,w',he,hw'.nonsingular,
    D.doubleNatural_five_adapted_characteristic_or_jankoFour h B S w' hw'⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
