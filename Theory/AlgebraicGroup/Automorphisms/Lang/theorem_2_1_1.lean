module

public import Theory.AlgebraicGroup.Automorphisms.Steinberg
public import Theory.AlgebraicGroup.Instance.GL
public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.Tori.Maximal
public import Theory.AlgebraicGroup.Semisimple.Versions
public import Theory.AlgebraicGroup.Morphism.CodRestrict
public import Theory.AlgebraicGroup.Morphism.ClosedImage
public import Theory.AlgebraicGroup.ClosedSubgroup.Quotient
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
This module isolates `theorem_2_1_1` from `Theory.AlgebraicGroup.Automorphisms.Lang`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u v

set_option warningAsError false

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-! The σ-twisted conjugacy relation and the set denoted `H¹(σ,K)` in GLS3
§2.1.  These are the definitions used throughout the section. -/

@[expose]
public def sigmaTwistedConjugate
    {G : Type u} [Group G] (σ : G →* G) (x y : G) : Prop :=
  ∃ g : G, y = g * x * (σ g)⁻¹

public theorem sigmaTwistedConjugate_equivalence
    {G : Type u} [Group G] (σ : G →* G) :
    Equivalence (sigmaTwistedConjugate σ) := by
  constructor
  · intro x
    exact ⟨1, by simp⟩
  · intro x y h
    rcases h with ⟨g, rfl⟩
    refine ⟨g⁻¹, ?_⟩
    simp [σ.map_inv, mul_assoc]
  · intro x y z hxy hyz
    rcases hxy with ⟨g, rfl⟩
    rcases hyz with ⟨h, rfl⟩
    refine ⟨h * g, ?_⟩
    simp [σ.map_mul, mul_inv_rev, mul_assoc]

@[expose]
public def H1
    {G : Type u} [Group G] (σ : G →* G) : Type u :=
  Quotient (⟨sigmaTwistedConjugate σ, sigmaTwistedConjugate_equivalence σ⟩)

@[expose]
public def H1.mk
    {G : Type u} [Group G] (σ : G →* G) (x : G) : H1 σ :=
  Quotient.mk _ x

private theorem H1.mk_eq_mk_iff
    {G : Type u} [Group G] (σ : G →* G) (x y : G) :
    H1.mk σ x = H1.mk σ y ↔ sigmaTwistedConjugate σ x y := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    apply Quotient.sound
    exact h

/-! The definition in Remark 2.1.7. -/

@[expose]
public def IsSigmaSplitMaximalTorus
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) (T : ClosedSubgroup K) : Prop :=
  IsMaximalTorus T ∧
    σ.onPoints '' (T : Set (Variety.Point K)) = T ∧
    ∃ B : ClosedSubgroup K,
      IsBorelSubgroup B ∧ T ≤ B ∧
        σ.onPoints '' (B : Set (Variety.Point K)) = B

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! Matrix Frobenius maps used in Definition 2.1.9. -/

@[expose]
public def matrixQPower
    (n q : ℕ) (x : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k :=
  fun i j => x i j ^ q

@[expose]
public noncomputable def generalLinearFrobenius
    (n r a : ℕ) [Fact r.Prime] [CharP k r] :
    GL (Fin n) k →* GL (Fin n) k :=
  Matrix.GeneralLinearGroup.map (iterateFrobenius k r a)

/-! Definition 2.1.9, with the level written directly rather than through a
 witness structure.  A level `q₀` means that a positive iterate becomes the
 entrywise `r^a`-power map and `q₀^m = r^a`. -/

@[expose]
public def IsFrobeniusEndomorphismOfLevel
    {K : Variety k} [AlgebraicGroup K]
    {r : ℕ} [Fact r.Prime] [CharP k r]
    (q₀ : NNReal) (σ : AlgebraicGroup.Morphism K K) : Prop :=
  ∃ (m a n : ℕ) (H : ClosedSubgroup (glVariety n : Variety k)),
    0 < m ∧ 0 < a ∧ q₀ ^ m = (r ^ a : NNReal) ∧
    letI := H.carrierAlgebraicGroup
    ∃ e : AlgebraicGroup.Iso K H.carrierVariety,
      ∀ x : Variety.Point K,
        glPointEquiv n
            (H.inclusion.onPoints (e.hom.onPoints (σ.onPoints^[m] x))) =
          generalLinearFrobenius (k := k) n r a
            (glPointEquiv n (H.inclusion.onPoints (e.hom.onPoints x)))

@[expose]
public def IsFrobeniusEndomorphism
    {K : Variety k} [AlgebraicGroup K]
    {r : ℕ} [Fact r.Prime] [CharP k r]
    (σ : AlgebraicGroup.Morphism K K) : Prop :=
  ∃ q₀ : NNReal, IsFrobeniusEndomorphismOfLevel (r := r) q₀ σ

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! Lang--Steinberg theorem and the basic consequences collected as
Theorem 2.1.2.  The geometric statements remain open here; elementary
consequences are discharged from the existing algebraic-group interfaces. -/

public theorem theorem_2_1_1
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (hK : Variety.IsConnected K) :
    Function.Surjective (fun g : Variety.Point K => g * σ.onPoints g⁻¹) := by
  sorry

public theorem theorem_2_1_2_a
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : IsAlgebraicSteinbergEndomorphism σ) :
    Finite σ.kernel := by
  exact surjectiveEndomorphism_kernel_finite σ hσ.1

public theorem theorem_2_1_2_b
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (hK : IsSemisimpleAlgebraicGroup K) :
    Function.Bijective σ.onPoints := by
  refine ⟨?_, hσ.1⟩
  obtain ⟨a, ha, _⟩ :=
    existsUnique_algebraicAutomorphism_realizing_surjective_endomorphism
      σ hK hσ.1
  intro x y hxy
  apply a.injective
  calc
    a x = σ.onPoints x := ha x
    _ = σ.onPoints y := hxy
    _ = a y := (ha y).symm

public theorem theorem_2_1_2_c
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (H : ClosedSubgroup K)
    (hH : Variety.IsConnected H.carrierVariety) :
    let I := (σ.comp H.inclusion).imageClosedSubgroup
    (I ≤ H ↔ H ≤ I) ∧ (H ≤ I ↔ I = H) := by
  dsimp
  let I := (σ.comp H.inclusion).imageClosedSubgroup
  have hIconn : _root_.IsConnected (I : Set (Variety.Point K)) := by
    let f : AlgebraicGroup.Morphism H.carrierVariety K := σ.comp H.inclusion
    have hconnUniv : _root_.IsConnected
        (Set.univ : Set (Variety.Point H.carrierVariety)) := hH
    have hconnRange : _root_.IsConnected (Set.range f.onPoints) := by
      simpa [Set.range_comp] using
        hconnUniv.image f.onPoints f.toVariety.continuous.continuousOn
    change _root_.IsConnected (f.image : Set (Variety.Point K))
    exact hconnRange
  have hHconn : _root_.IsConnected (H : Set (Variety.Point K)) := by
    have himage := hH.image H.inclusion.onPoints
      H.inclusion.toVariety.continuous.continuousOn
    have hrange : H.inclusion.onPoints ''
        (Set.univ : Set (Variety.Point H.carrierVariety)) =
          (H : Set (Variety.Point K)) := by
      rw [Set.image_univ]
      exact H.range_inclusion
    rwa [hrange] at himage
  have hdim : Variety.dimension I.carrierVariety =
      Variety.dimension H.carrierVariety := by
    let : Finite σ.kernel := surjectiveEndomorphism_kernel_finite σ hσ.1
    let f : AlgebraicGroup.Morphism H.carrierVariety K := σ.comp H.inclusion
    let kernelToSigma : f.kernel → σ.kernel := fun x =>
      ⟨H.inclusion.onPoints x, by
        change σ.onPoints (H.inclusion.onPoints x) = 1
        exact x.property⟩
    have hkernelInjective : Function.Injective kernelToSigma := by
      intro x y hxy
      apply Subtype.ext
      have hxy' : H.inclusion.onPoints x = H.inclusion.onPoints y :=
        congrArg (fun z : σ.kernel => (z : Variety.Point K)) hxy
      exact H.inclusion_injective hxy'
    let : Finite f.kernel := Finite.of_injective kernelToSigma hkernelInjective
    have hkernelSubtype : Finite f.kernelClosedSubgroup.toSubgroup := by
      let e : f.kernelClosedSubgroup.toSubgroup ≃ f.kernel :=
        Equiv.setCongr (AlgebraicGroup.Morphism.kernelClosedSubgroup_carrier f)
      exact (Equiv.finite_iff e).2 inferInstance
    let : Finite (Variety.Point f.kernelClosedSubgroup.carrierVariety) :=
      (Equiv.finite_iff f.kernelClosedSubgroup.pointEquiv).2 hkernelSubtype
    have hkernelDimension :
        Variety.dimension f.kernelClosedSubgroup.carrierVariety = 0 :=
      (dimension_zero_iff_finite_points f.kernelClosedSubgroup.carrierVariety).2 inferInstance
    have hdimension := morphism_dimension_eq_kernel_add_image f
    rw [hkernelDimension, zero_add] at hdimension
    exact hdimension.symm
  have eq_of_I_le_H (hle : I ≤ H) : I = H := by
    by_contra hne
    have hlt := connected_closedSubgroup_dimension_lt_of_le_of_ne
      I H hle hne hIconn hHconn
    exact (not_lt_of_ge hdim.ge) hlt
  have eq_of_H_le_I (hle : H ≤ I) : I = H := by
    by_contra hne
    have hlt := connected_closedSubgroup_dimension_lt_of_le_of_ne
      H I hle (fun heq => hne heq.symm) hHconn hIconn
    exact (not_lt_of_ge hdim.le) hlt
  constructor
  · constructor
    · intro hle
      change I ≤ H at hle
      change H ≤ I
      rw [eq_of_I_le_H hle]
      exact fun x hx => hx
    · intro hle
      change H ≤ I at hle
      change I ≤ H
      rw [eq_of_H_le_I hle]
      exact fun x hx => hx
  · constructor
    · exact eq_of_H_le_I
    · intro heq
      change H ≤ I
      change I = H at heq
      rw [heq]
      exact fun x hx => hx

end

end Theory.AlgebraicGroup
