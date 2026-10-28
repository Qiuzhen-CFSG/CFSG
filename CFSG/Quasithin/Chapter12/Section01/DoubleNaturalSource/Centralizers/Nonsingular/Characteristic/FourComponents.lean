module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.FourThompson
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.MovingFaithful
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.Components
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# The containing component in the degree-four nonsingular centralizer

The proved ambient Sylow placement supplies original 1.2.4: the point
residual lies in a unique normal C-component. An ordinary component that
commutes with this C-component would centralize the residual, contradicting
the established residual movement. Thus every ordinary component equals
the containing C-component. The actual moving subgroup meets the centralizer
of this component trivially, by the residual fixed-space calculation.

The chosen-module application constructs the compatible model and corrected
L-conjugate. The strengthened characteristic-two alternative retains the
ordinary-component exclusion as remaining mathematics for
qt-d-double-natural-centralizers; this does not finish 12.1.1.
Source: Aschbacher--Smith, 12.1.1, printed p.788, using 1.2.4, p.505.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The degree-four residual lies in a unique normal C-component of the actual point centralizer. -/
theorem doubleNatural_four_adapted_containing_cComponent
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∃! K : Subgroup G, K ∈ cComponentsIn (B.pointCentralizer w) ∧
        B.pointResidual w ≤ K ∧ (K.subgroupOf (B.pointCentralizer w)).Normal := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  let H := B.pointCentralizer w
  let R := B.pointResidual w
  have hRH : R ≤ H := (B.pointResidual_le w).trans inf_le_right
  have hPH : B.pointSylow w ≤ H := inf_le_right
  obtain ⟨P,hP⟩ := D.doubleNatural_four_adapted_ambientSylow h B S w hw
  have heP : (P : Subgroup H) = (B.pointSylow w).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hPH]
  have hR : R.subgroupOf H ∈ Chapter1.L H (P : Subgroup H) := by
    rw [heP]
    exact (mem_LIn_iff_subgroupOf hPH hRH).mp
      (D.doubleNatural_adapted_residual_mem_localFamily h B S w hw)
  have hn : (P : Subgroup H) ≤ normalizer (R.subgroupOf H : Set H) := by
    rw [heP, ← subgroupOf_normalizer_eq hRH]
    apply comap_mono
    exact (show B.pointSylow w ≤ B.localPointCentralizer w from
      le_inf (inf_le_left.trans D.sylow_normalizes_component) inf_le_right).trans
        (B.localPointCentralizer_normalizes_residual w)
  have hH : H ∈ Chapter1.H G := mem_H_of_isTwoLocal
    (isTwoLocal_involution_centralizer (D.doubleNatural_point_orderOf_two h B w hw.nonsingular))
  obtain ⟨K,⟨hK,hRK,hKn⟩,hu⟩ := Section02.lemma_1_2_4_containment_normality_source
    (Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hH) P hR hn
  have hm : (K.map H.subtype).subgroupOf H = K :=
    comap_map_eq_self_of_injective H.subtype_injective K
  refine ⟨K.map H.subtype,⟨⟨map_subtype_le _,hm.symm ▸ hK⟩,?_,hm.symm ▸ hKn⟩,?_⟩
  · simpa only [map_subgroupOf_eq_of_le hRH] using map_mono (f := H.subtype) hRK
  · intro J hJ
    have he := hu (J.subgroupOf H) ⟨hJ.1.2,comap_mono hJ.2.1,hJ.2.2⟩
    simpa only [map_subgroupOf_eq_of_le (show J ≤ H from hJ.1.1)] using congrArg (map H.subtype) he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Every surviving ordinary component is the containing C-component and hence is normal and contains the residual. -/
theorem doubleNatural_four_adapted_ordinary_component_contains_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        B.pointResidual w ≤ K ∧ (K.subgroupOf (B.pointCentralizer w)).Normal := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK
  let H := B.pointCentralizer w
  obtain ⟨J,⟨hJ,hRJ,hJn⟩,_⟩ := D.doubleNatural_four_adapted_containing_cComponent h B S w hw
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

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The degree-four source construction, with its compatible model discharged. -/
theorem doubleNatural_four_nonsingular_sylow_component_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ w : componentOrbit V (T : Subgroup G), B.quadratic (Additive.ofMul w) = 1 →
      ∃ l : L, ∃ w' : componentOrbit V (T : Subgroup G),
        (w' : G) = (l : G) * (w : G) * (l : G)⁻¹ ∧
        B.quadratic (Additive.ofMul w') = 1 ∧
        IsSylowIn 2 (B.pointSylow w') (B.pointCentralizer w') ∧
        ∃ K : Subgroup G, K ∈ cComponentsIn (B.pointCentralizer w') ∧
          B.pointResidual w' ≤ K ∧ (K.subgroupOf (B.pointCentralizer w')).Normal := by
  let := D.doubledOrbit_elementary h
  intro w hw
  obtain ⟨S⟩ := B.nonempty_sourceModel
  obtain ⟨l,w',he,hw'⟩ := D.doubleNatural_adaptedPoint h B S w hw
  obtain ⟨K,hK,_⟩ := D.doubleNatural_four_adapted_containing_cComponent h B S w' hw'
  exact ⟨l,w',he,hw'.nonsingular,D.doubleNatural_four_adapted_ambientSylow h B S w' hw',K,hK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule


namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Any surviving ordinary component in degree four has the precise faithful moving subgroup of 12.1.1. -/
theorem doubleNatural_four_adapted_component_moving_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆ ⊓ centralizer (K : Set G) = ⊥ := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK
  have hRK := (D.doubleNatural_four_adapted_ordinary_component_contains_residual h B S w hw K hK).1
  apply bot_unique
  exact (inf_le_inf_left _ (centralizer_le hRK)).trans_eq
    (S.nonsingular_moving_centralizer_residual w hw.nonsingular)

/-- The characteristic-two reduction now supplies a normal ordinary component containing L_w, on which the actual moving subgroup acts faithfully. -/
theorem doubleNatural_four_adapted_characteristic_or_normal_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
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
  · obtain ⟨hRK,hn⟩ := D.doubleNatural_four_adapted_ordinary_component_contains_residual h B S w hw K hK
    exact Or.inr ⟨K,hK,hn,hRK,D.doubleNatural_four_adapted_component_moving_centralizer h B S w hw K hK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
