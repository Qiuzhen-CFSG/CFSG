module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.Components
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.Residual
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Assembly
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ModelConstruction.Construction

/-!
# Source applications of the nonsingular odd-core argument

The constructed compatible model and corrected L-conjugation remove both
the model and adapted-point premises from odd-core triviality. The second
theorem feeds the proved characteristic-two/component alternative into the
existing 12.1.1 assembly. Ordinary-component exclusion and both the normal
and nonnormal ambient branches remain explicit obligations of
qt-d-double-natural-centralizers; this is not a proof of 12.1.1.

Source: Aschbacher--Smith, 12.1.1, printed pp.788--789.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Every nonsingular point has trivial ambient odd core, with the source model discharged. -/
theorem doubleNatural_nonsingular_oddCore_eq_bot_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ w : componentOrbit V (T : Subgroup G), B.quadratic (Additive.ofMul w) = 1 →
      pPrimeCore 2 (B.pointCentralizer w) = ⊥ := by
  let := D.doubledOrbit_elementary h
  intro w hw
  obtain ⟨S⟩ := B.nonempty_sourceModel
  obtain ⟨l,w',he,hw'⟩ := D.doubleNatural_adaptedPoint h B S w hw
  let e : G ≃* G := MulAut.conj (l : G)
  have he' : (w' : G) = e (w : G) := he
  have hmem (x : G) : x ∈ B.pointCentralizer w ↔ e x ∈ B.pointCentralizer w' := by
    simp only [DoubledBranch.pointCentralizer,mem_centralizer_singleton_iff,he',
      ←map_mul,e.injective.eq_iff]
  have hmap : (B.pointCentralizer w).map e.toMonoidHom = B.pointCentralizer w' := by
    ext x
    rw [mem_map_equiv]
    simpa only [e.apply_symm_apply] using hmem (e.symm x)
  let f := (e.subgroupMap (B.pointCentralizer w)).trans (MulEquiv.subgroupCongr hmap)
  apply map_injective (f := f.toMonoidHom) f.injective
  rw [pPrimeCore_map_iso,Subgroup.map_bot]
  exact D.doubleNatural_adapted_oddCore_eq_bot h B S w' hw'

/-- The literal 12.1.1 assembly now needs only ordinary-component exclusion in its characteristic-two branch. -/
theorem doubleNatural_nonsingularCentralizers_of_component_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel,
      (∀ w, B.AdaptedPoint S w → ∀ K : Subgroup G,
        IsComponentIn K (B.pointCentralizer w) →
        B.pointResidual w ≤ normalizer (K : Set G) →
        ⁅K,B.pointResidual w⁆ = K → ¬ K ≤ centralizer (B.fixedLine : Set G) → False) →
      (∀ w, B.AdaptedPoint S w →
        generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
        ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
        B.pointCentralizer w ≤ normalizer (L : Set G)) →
      (∀ w, B.AdaptedPoint S w →
        generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
        ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
        ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
        B.pointResidual w ≤ centralizer (B.fixedLine : Set G)) →
      B.NonsingularCentralizers := by
  let := D.doubledOrbit_elementary h
  intro S hcomponents hnormal hparabolic
  apply D.doubleNatural_nonsingularCentralizers_of_branches h B S _ hnormal hparabolic
  intro w hw
  rcases D.doubleNatural_adapted_characteristic_or_component h B S w hw with hc | hK
  · exact hc
  · obtain ⟨K,hK,hn,hcomm,hmove⟩ := hK
    exact (hcomponents w hw K hK hn hcomm hmove).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
