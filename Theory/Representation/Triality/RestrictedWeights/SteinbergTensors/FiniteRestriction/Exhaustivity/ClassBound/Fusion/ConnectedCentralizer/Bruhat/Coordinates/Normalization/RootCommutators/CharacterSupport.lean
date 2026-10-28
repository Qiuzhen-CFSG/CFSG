module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.Closure
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.CharacterSupport.Contracts
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.CharacterSupport.WordMaps
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.CharacterSupport.Eigenfunction
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.CharacterSupport.PolynomialSupport

/-!
Mixed character support in the actual root-pair commutator closure.
An equivariant lift of the target root parameter
is nonzero on the closure. Density detects it on a finite commutator word; the
word map supplies a nonzero polynomial vanishing when either parameter family
is erased. Strict mixed-degree character support gives the desired exponents.

The conditional reduction is retained, and the final theorem discharges its
equivariant-extension and polynomial-support inputs using the realized root
action and the supplied maximal torus. The identities use inverse conjugation
and remain valid in characteristic two. No positive-root coordinates or root
generation of the commutator closure are used.

Source: GLS3, 1.12.1(b) and 1.12.7(b), `refs/KGroup/GLS3/Chapter1.tex`.
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
namespace ConnectedCentralizer.Bruhat.Coordinates.Normalization
noncomputable section
universe u
variable {k : Type u} [Field k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

/-- Conditional assembly of mixed support from equivariant root-parameter
extension and strict mixed polynomial support. The affine-word construction and
passage from the actual Zariski closure are proved in `WordMaps`. -/
public theorem mixedCommutatorCharacterSupport_of_function_inputs (S : Geometry K)
    (hext : RootParameterEigenfunctionExtension S.roots)
    (hsupport : MixedPolynomialCharacterSupport S.torus.carrierVariety)
    (a b c : S.roots.Root)
    (hle : (S.roots.rootSubgroup c).toSubgroup ≤ (closedPairCommutator S a b).toSubgroup) :
    ∃ i j : ℕ, 0 < i ∧ 0 < j ∧
      S.roots.rootWeight c = S.roots.rootWeight a ^ i * S.roots.rootWeight b ^ j := by
  obtain ⟨F, hFparameter, hFscale⟩ := hext c (S.rootParameter c)
  have hFone : F 1 = 0 := by
    have hzero : (S.roots.rootSubgroup c).includePoint ((S.rootParameter c).value 0) = 1 := by
      change (S.roots.rootSubgroup c).inclusion.onPoints
        ((S.rootParameter c).hom.onPoints (kPlusPoint 0)) = 1
      rw [show kPlusPoint (0 : k) = 1 by rfl]
      simp
    simpa only [hzero] using hFparameter 0
  let g := (S.roots.rootSubgroup c).includePoint ((S.rootParameter c).value 1)
  have hg : g ∈ closedPairCommutator S a b :=
    hle ((S.roots.rootSubgroup c).pointEquiv ((S.rootParameter c).value 1)).property
  have hFg : F g ≠ 0 := by
    change F ((S.roots.rootSubgroup c).includePoint ((S.rootParameter c).value 1)) ≠ 0
    rw [hFparameter]
    exact one_ne_zero
  obtain ⟨sigma, hfinite, side, P, hnonzero, hscale, herase⟩ :=
    exists_mixedCommutatorPolynomial S a b (S.roots.rootWeight c) F hFone hFscale g hg hFg
  let : Finite sigma := hfinite
  exact hsupport sigma side (S.roots.rootWeight a) (S.roots.rootWeight b)
    (S.roots.rootWeight c) P hnonzero hscale herase

/-- Every root subgroup contained in the actual commutator closure of two
distinct positive root subgroups has a character involving positive powers of
both input characters. The regular-function inputs are discharged from the
realized root action and the actual torus. -/
public theorem mixedCommutatorCharacterSupport [IsAlgClosed k] (S : Geometry K)
    (a : S.roots.Root) (_ha : a ∈ S.roots.positive)
    (b : S.roots.Root) (_hb : b ∈ S.roots.positive) (_hab : a ≠ b)
    (c : S.roots.Root)
    (hle : (S.roots.rootSubgroup c).toSubgroup ≤ (closedPairCommutator S a b).toSubgroup) :
    ∃ i j : ℕ, 0 < i ∧ 0 < j ∧
      S.roots.rootWeight c = S.roots.rootWeight a ^ i * S.roots.rootWeight b ^ j := by
  exact mixedCommutatorCharacterSupport_of_function_inputs S
    (rootParameterEigenfunctionExtension_of_realization S.maximalTorus.1 S.roots S.realized)
    (mixedPolynomialCharacterSupport_of_isTorus S.torus.carrierVariety S.maximalTorus.1)
    a b c hle

end
end ConnectedCentralizer.Bruhat.Coordinates.Normalization
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
