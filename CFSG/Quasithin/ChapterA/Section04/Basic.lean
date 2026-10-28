module

public import Theory.GroupTheory.PGroup.MutualNormalizerCommutator
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.PGroupCore
public import Theory.GroupTheory.PGroup.Omega

/-!
# Signalizers for groups with `X = O²(X)`

This file records the signalizer interface used in Appendix A.4 of
Aschbacher--Smith.  A signalizer is a 2-subgroup normalized by `X` and lying
in an ambient subgroup `M`.  The first lemma is the elementary commutator
criterion (A.4.2.1); subsequent constructions package the module `V(X,R)`
and its basic containment properties.
-/

open scoped commutatorElement

namespace CFSG.Quasithin.ChapterA.Section04

variable {G : Type*} [Group G]

/-- `R` is a 2-signalizer for `X` in `M`. -/
public def IsTwoSignalizer (X M R : Subgroup G) : Prop :=
  R ≤ M ∧ IsPGroup 2 R ∧ X ≤ Subgroup.normalizer (R : Set G)

/-- Maximal 2-signalizers for a fixed pair `(X,M)`. -/
public def IsMaximalTwoSignalizer (X M R : Subgroup G) : Prop :=
  Maximal (fun S : Subgroup G => IsTwoSignalizer X M S) R

/-- The commutator criterion for signalizers (A.4.2.1). -/
public theorem isTwoSignalizer_iff_commutator_le (X M R : Subgroup G)
    (hRM : R ≤ M) (hR2 : IsPGroup 2 R) :
    IsTwoSignalizer X M R ↔ ⁅X, R⁆ ≤ R := by
  constructor
  · intro h
    rw [Subgroup.commutator_le]
    intro x hx r hr
    have hnorm := (Subgroup.le_normalizer_iff.mp h.2.2) x hx r hr
    rw [commutatorElement_def]
    -- `x*r*x⁻¹` is in `R`; multiply by `r⁻¹` on the right.
    exact R.mul_mem hnorm (R.inv_mem hr)
  · intro h
    refine ⟨hRM, hR2, ?_⟩
    rw [Subgroup.le_normalizer_iff]
    intro x hx r hr
    have hc : ⁅x, r⁆ ∈ R := (Subgroup.commutator_le.mp h) x hx r hr
    rw [commutatorElement_def] at hc
    -- `x*r*x⁻¹ = ⁅x,r⁆*r`.
    have := R.mul_mem hc hr
    simpa [commutatorElement_def, mul_assoc] using this

/-! A normal 2-subgroup lies in the 2-core. This elementary bound is used
in A.4.2(3), after normality in the relevant ambient group is established. -/

public theorem le_pCore_of_isPGroup_of_normal
    (X : Subgroup G) (hX2 : IsPGroup 2 X) [X.Normal] :
    X ≤ pCore 2 G := by
  exact le_sSup ⟨inferInstance, hX2⟩

/-- The part of `V(X,R)` used in A.4.6: commutators of `X` with the
first omega subgroup of the centre of `R`. -/
public def signalizerModule (X R : Subgroup G) : Subgroup G :=
  let C : Subgroup (↥R) := Subgroup.center (↥R)
  let Ω : Subgroup (↥C) := omega₁ (G := (↥C)) (p := 2)
  ⁅X, (Ω.map C.subtype).map R.subtype⁆

/-- Every element of the signalizer module lies in `X` when the signalizer
subgroup normalizes `X`. -/
public theorem signalizerModule_le_left (X R : Subgroup G)
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) :
    signalizerModule X R ≤ X := by
  change ⁅X, ((omega₁ (G := (↥(Subgroup.center (↥R)))) (p := 2)).map
    (Subgroup.center (↥R)).subtype).map R.subtype⁆ ≤ X
  rw [Subgroup.commutator_le]
  intro x hx z hz
  have hzR : (z : G) ∈ R := by
    exact Subgroup.map_subtype_le
      ((omega₁ (G := (↥(Subgroup.center (↥R)))) (p := 2)).map
        (Subgroup.center (↥R)).subtype) hz
  have hnorm := (Subgroup.le_normalizer_iff.mp hRX) (z : G) hzR x⁻¹ (X.inv_mem hx)
  rw [commutatorElement_def]
  -- rewrite the commutator as `x * (z*x⁻¹*z⁻¹)`.
  have hzx : (z : G) * x⁻¹ * (z : G)⁻¹ ∈ X := hnorm
  simpa [mul_assoc] using X.mul_mem hx hzx

/-- A direct elementwise containment of the signalizer module in a normalized
2-subgroup.  This is the subgroup calculation behind A.4.6. -/
public theorem signalizerModule_le_right (X R : Subgroup G)
    (hXR : X ≤ Subgroup.normalizer (R : Set G)) :
    signalizerModule X R ≤ R := by
  rw [signalizerModule, Subgroup.commutator_le]
  intro x hx z hz
  have hzR : z ∈ R := by
    exact Subgroup.map_subtype_le
      ((omega₁ (G := (↥(Subgroup.center (↥R)))) (p := 2)).map
        (Subgroup.center (↥R)).subtype) hz
  have hnorm := (Subgroup.le_normalizer_iff.mp hXR) x hx (z : G) hzR
  rw [commutatorElement_def]
  exact R.mul_mem hnorm (R.inv_mem hzR)

/-- Under mutual normalization, `V(X,R)` is contained in `X ∩ R`. -/
public theorem signalizerModule_le_inf (X R : Subgroup G)
    (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) :
    signalizerModule X R ≤ X ⊓ R := by
  exact le_inf (signalizerModule_le_left X R hRX) (signalizerModule_le_right X R hXR)

end CFSG.Quasithin.ChapterA.Section04
