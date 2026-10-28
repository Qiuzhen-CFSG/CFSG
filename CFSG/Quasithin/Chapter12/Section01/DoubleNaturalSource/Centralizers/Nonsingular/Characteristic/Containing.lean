module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.FourComponents
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.FiveComponents

/-!
# Normal containing components for both doubled degrees

The degree-four Sylow argument and degree-five cubic-rank argument give
the same unique normal C-component containing the point residual. Every
ordinary component must equal it: otherwise it commutes with the residual,
contrary to the proved component movement. The moving subgroup lies in
the residual and has trivial centralizer there, so it acts faithfully on
any surviving ordinary component.

The chosen-module application removes the model and adapted-point premises.
The remaining ordinary-component exclusion and the normal/parabolic branches
of 12.1.1 remain with qt-d-double-natural-centralizers.
Source: Aschbacher--Smith, 12.1.1, printed p.788.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Both source degrees have a unique normal C-component containing L_w. -/
theorem doubleNatural_adapted_containing_cComponent
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∃! K : Subgroup G, K ∈ cComponentsIn (B.pointCentralizer w) ∧
        B.pointResidual w ≤ K ∧ (K.subgroupOf (B.pointCentralizer w)).Normal := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  rcases B.degree with hn | hn
  · subst n
    exact D.doubleNatural_four_adapted_containing_cComponent h B S w hw
  · subst n
    exact D.doubleNatural_five_nonsingular_containing_cComponent h B S w hw.nonsingular

/-- The original moving subgroup is contained in the actual point residual. -/
theorem doubleNatural_moving_le_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ w : componentOrbit V (T : Subgroup G),
      ⁅componentOrbit V (T : Subgroup G), B.pointResidual w⁆ ≤ B.pointResidual w := by
  let := D.doubledOrbit_elementary h
  intro w
  apply le_normalizer_iff_commutator_le_right.mp
  exact (le_inf ((D.doubledOrbit_E322 h).le_sylow.trans D.sylow_normalizes_component)
    (B.orbit_le_pointCentralizer w)).trans (B.localPointCentralizer_normalizes_residual w)

/-- Every surviving ordinary component is the containing C-component and hence is normal and contains the residual. -/
theorem doubleNatural_adapted_ordinary_component_contains_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        B.pointResidual w ≤ K ∧ (K.subgroupOf (B.pointCentralizer w)).Normal := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK
  let H := B.pointCentralizer w
  obtain ⟨J,⟨hJ,hRJ,hJn⟩,_⟩ := D.doubleNatural_adapted_containing_cComponent h B S w hw
  have he : K.subgroupOf H = J.subgroupOf H := by
    rcases hK.2.subnormal_dichotomy (J.subgroupOf H) hJ.2.subnormal with hle | hc
    · exact hK.2.isCComponent.eq_of_le hJ.2 hle
    · change ⁅K.subgroupOf H,J.subgroupOf H⁆ = ⊥ at hc
      have hc' : ⁅K,J⁆ = ⊥ := by
        simpa only [map_commutator,map_subgroupOf_eq_of_le (show K ≤ H from hK.1),
          map_subgroupOf_eq_of_le (show J ≤ H from hJ.1),Subgroup.map_bot] using congrArg (map H.subtype) hc
      have hmove := (D.doubleNatural_adapted_component_residual_action h B S w hw K hK).2
      have hbot : K = ⊥ := bot_unique (by
        rw [←hmove]
        exact (commutator_mono le_rfl hRJ).trans_eq hc')
      have hb' : K.subgroupOf H = ⊥ := by
        apply bot_unique
        intro x hx
        apply Subtype.ext
        exact mem_bot.mp (hbot ▸ hx)
      exact (hK.2.isCComponent.ne_bot hb').elim
  have he' : K = J := by
    simpa only [map_subgroupOf_eq_of_le (show K ≤ H from hK.1),map_subgroupOf_eq_of_le (show J ≤ H from hJ.1)] using
      congrArg (map H.subtype) he
  exact ⟨he'.symm ▸ hRJ,he.symm ▸ hJn⟩


/-- Any surviving ordinary component in either degree has the precise faithful moving subgroup of 12.1.1. -/
theorem doubleNatural_adapted_component_moving_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆ ⊓ centralizer (K : Set G) = ⊥ := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK
  have hRK := (D.doubleNatural_adapted_ordinary_component_contains_residual h B S w hw K hK).1
  apply bot_unique
  exact (inf_le_inf_left _ (centralizer_le hRK)).trans_eq
    (S.nonsingular_moving_centralizer_residual w hw.nonsingular)

/-- The characteristic-two reduction now supplies a normal ordinary component containing L_w, on which the actual moving subgroup acts faithfully. -/
theorem doubleNatural_adapted_characteristic_or_normal_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) ∨
      ∃ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) ∧
        (K.subgroupOf (B.pointCentralizer w)).Normal ∧ B.pointResidual w ≤ K ∧
        ⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆ ⊓ centralizer (K : Set G) = ⊥ := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  rcases D.doubleNatural_adapted_characteristic_or_component h B S w hw with hc | ⟨K,hK,_⟩
  · exact Or.inl hc
  · obtain ⟨hRK,hn⟩ := D.doubleNatural_adapted_ordinary_component_contains_residual h B S w hw K hK
    exact Or.inr ⟨K,hK,hn,hRK,D.doubleNatural_adapted_component_moving_centralizer h B S w hw K hK⟩


/-- The containing-component construction on an L-conjugate of every nonsingular point, with SourceModel discharged. -/
theorem doubleNatural_nonsingular_containing_component_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ w : componentOrbit V (T : Subgroup G), B.quadratic (Additive.ofMul w) = 1 →
      ∃ l : L, ∃ w' : componentOrbit V (T : Subgroup G),
        (w' : G) = (l : G) * (w : G) * (l : G)⁻¹ ∧
        B.quadratic (Additive.ofMul w') = 1 ∧
        (∃ K : Subgroup G, K ∈ cComponentsIn (B.pointCentralizer w') ∧
          B.pointResidual w' ≤ K ∧ (K.subgroupOf (B.pointCentralizer w')).Normal) ∧
        (∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w') →
          (K.subgroupOf (B.pointCentralizer w')).Normal ∧ B.pointResidual w' ≤ K ∧
          ⁅componentOrbit V (T : Subgroup G),B.pointResidual w'⁆ ⊓ centralizer (K : Set G) = ⊥) := by
  let := D.doubledOrbit_elementary h
  intro w hw
  obtain ⟨S⟩ := B.nonempty_sourceModel
  obtain ⟨l,w',he,hw'⟩ := D.doubleNatural_adaptedPoint h B S w hw
  obtain ⟨K,hK,_⟩ := D.doubleNatural_adapted_containing_cComponent h B S w' hw'
  refine ⟨l,w',he,hw'.nonsingular,⟨K,hK⟩,?_⟩
  intro J hJ
  obtain ⟨hRJ,hn⟩ := D.doubleNatural_adapted_ordinary_component_contains_residual h B S w' hw' J hJ
  exact ⟨hn,hRJ,D.doubleNatural_adapted_component_moving_centralizer h B S w' hw' J hJ⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
