module

public import Theory.AlgebraicGroup.RootSystems.EvenOrthogonalRootSubgroups
public import Theory.AlgebraicGroup.Representations.Algebraic.Irreducible
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Irreducibility of the natural split Omega representation

For a split nondegenerate quadratic form, this module equips the closed Spin
action image with its natural rational action on the quadratic space and proves
that action irreducible in hyperbolic rank at least four.  Its pointwise action
formula identifies the representation with
`evenSpinActionImageClosedSubgroup_linear_points`, so later structural results
can read off faithfulness and preservation of the quadratic form.

The proof is direct and characteristic-free.  It reuses the elementary
orthogonal transformations and their single-commutator certificates from
`EvenOrthogonalRootSubgroups`; transporting these through the supplied split
isometry makes every invariant submodule stable under them.  Two successive
root differences isolate a standard coordinate vector from any nonzero vector,
and further root actions propagate it through both halves of the hyperbolic
basis.  This is the classical elementary-matrix proof and uses neither the
type-D classification nor the numbered classification theorem.
-/

universe u

open scoped commutatorElement

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private noncomputable def splitTransportIsometryHom
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q) :
    quadraticIsometrySubgroup (hyperbolicForm (k := k) s.rank) →*
      quadraticIsometrySubgroup Q where
  toFun g :=
    ⟨s.isometry.toLinearEquiv.trans
        (g.1.trans s.isometry.symm.toLinearEquiv),
      (mem_quadraticIsometrySubgroup Q _).2 fun v => by
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
        change Q (s.isometry.symm (g.1 (s.isometry v))) = Q v
        rw [
          s.isometry.symm.map_app, (mem_quadraticIsometrySubgroup _ _).1 g.2,
          s.isometry.map_app]⟩
  map_one' := by
    apply Subtype.ext
    ext v
    exact s.isometry.symm_apply_apply v
  map_mul' g h := by
    apply Subtype.ext
    ext v
    simp [LinearEquiv.mul_apply]

public noncomputable def evenOrthogonalNaturalRepresentation
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q) :
    RationalRepresentation
      (evenSpinActionImageClosedSubgroup Q s).carrierVariety V :=
  naturalClosedLinearSubgroupRepresentation
    (Module.finBasis k V) (evenSpinActionImageClosedSubgroup Q s)
    (AlgebraicGroup.Iso.id _)

public theorem evenOrthogonalNaturalRepresentation_isRational
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q) :
    IsRationalRepresentation (evenOrthogonalNaturalRepresentation s) :=
  naturalClosedLinearSubgroupRepresentation_isRational
    (Module.finBasis k V) (evenSpinActionImageClosedSubgroup Q s)
    (AlgebraicGroup.Iso.id _)

public theorem evenOrthogonalNaturalRepresentation_action
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (g : Variety.Point
      (evenSpinActionImageClosedSubgroup Q s).carrierVariety) :
    (evenOrthogonalNaturalRepresentation s).action g =
      glPointEquivOf k V (Module.finBasis k V)
        ((evenSpinActionImageClosedSubgroup Q s).inclusion.onPoints g) := by
  rfl

public theorem evenOrthogonalNaturalRepresentation_action_linear_points
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (hrank : 4 ≤ s.rank)
    (g : Variety.Point
      (evenSpinActionImageClosedSubgroup Q s).carrierVariety) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv k V
        ((evenOrthogonalNaturalRepresentation s).action g) =
      (evenSpinActionImageClosedSubgroupPoints Q s hrank g).1.1 := by
  rw [evenOrthogonalNaturalRepresentation_action]
  exact evenSpinActionImageClosedSubgroup_linear_points Q s hrank g

private lemma evenOrthogonalNatural_mapped_invariant_under_commutator
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (hrank : 4 ≤ s.rank)
    (W : Submodule k V)
    (hW : IsInvariantSubmodule (evenOrthogonalNaturalRepresentation s) W)
    (r : quadraticIsometrySubgroup (hyperbolicForm (k := k) s.rank))
    (hr : ∃ g h : quadraticIsometrySubgroup (hyperbolicForm (k := k) s.rank),
      r = ⁅g, h⁆)
    {z : HyperbolicSpace k s.rank}
    (hz : z ∈ W.map s.isometry.toLinearEquiv.toLinearMap) :
    r.1 z ∈ W.map s.isometry.toLinearEquiv.toLinearMap := by
  rcases hz with ⟨v, hv, rfl⟩
  let transport := splitTransportIsometryHom s
  have hrOmega : transport r ∈ commutator (quadraticIsometrySubgroup Q) := by
    obtain ⟨g, h, rfl⟩ := hr
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
      (Subgroup.mem_top _)
  let omega : commutator (quadraticIsometrySubgroup Q) :=
    ⟨transport r, hrOmega⟩
  let p := (evenSpinActionImageClosedSubgroupPoints Q s hrank).symm omega
  have hv' := hW p v hv
  refine ⟨((evenOrthogonalNaturalRepresentation s).action p).1 v, hv', ?_⟩
  have hp := evenOrthogonalNaturalRepresentation_action_linear_points s hrank p
  have hpApply := congrArg (fun e : V ≃ₗ[k] V => e v) hp
  have hpApply' :
      ((evenOrthogonalNaturalRepresentation s).action p).1 v =
        (evenSpinActionImageClosedSubgroupPoints Q s hrank p).1.1 v :=
    hpApply
  change s.isometry
      (((evenOrthogonalNaturalRepresentation s).action p).1 v) =
    r.1 (s.isometry v)
  rw [hpApply']
  rw [show evenSpinActionImageClosedSubgroupPoints Q s hrank p = omega by
    exact (evenSpinActionImageClosedSubgroupPoints Q s hrank).apply_symm_apply omega]
  exact s.isometry.apply_symm_apply (r.1 (s.isometry v))

private lemma evenOrthogonalNatural_mapped_invariant_under_upperRoot
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (hrank : 4 ≤ s.rank)
    (W : Submodule k V)
    (hW : IsInvariantSubmodule (evenOrthogonalNaturalRepresentation s) W)
    (i j : Fin s.rank) (hij : i ≠ j) (a : k)
    {z : HyperbolicSpace k s.rank}
    (hz : z ∈ W.map s.isometry.toLinearEquiv.toLinearMap) :
    (hyperbolicUpperRootPoint s.rank i j hij a).1 z ∈
      W.map s.isometry.toLinearEquiv.toLinearMap :=
  evenOrthogonalNatural_mapped_invariant_under_commutator s hrank W hW _
    (hyperbolicUpperRootPoint_is_commutator s.rank i j hij a) hz

private lemma evenOrthogonalNatural_mapped_invariant_under_lowerRoot
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (hrank : 4 ≤ s.rank)
    (W : Submodule k V)
    (hW : IsInvariantSubmodule (evenOrthogonalNaturalRepresentation s) W)
    (i j : Fin s.rank) (hij : i ≠ j) (a : k)
    {z : HyperbolicSpace k s.rank}
    (hz : z ∈ W.map s.isometry.toLinearEquiv.toLinearMap) :
    (hyperbolicLowerRootPoint s.rank i j hij a).1 z ∈
      W.map s.isometry.toLinearEquiv.toLinearMap :=
  evenOrthogonalNatural_mapped_invariant_under_commutator s hrank W hW _
    (hyperbolicLowerRootPoint_is_commutator s.rank i j hij a) hz

private lemma evenOrthogonalNatural_mapped_invariant_under_skewUpperRoot
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (hrank : 4 ≤ s.rank)
    (W : Submodule k V)
    (hW : IsInvariantSubmodule (evenOrthogonalNaturalRepresentation s) W)
    (i j : Fin s.rank) (hij : i ≠ j) (a : k)
    {z : HyperbolicSpace k s.rank}
    (hz : z ∈ W.map s.isometry.toLinearEquiv.toLinearMap) :
    (hyperbolicSkewUpperRootPoint s.rank i j hij a).1 z ∈
      W.map s.isometry.toLinearEquiv.toLinearMap :=
  evenOrthogonalNatural_mapped_invariant_under_commutator s hrank W hW _
    (hyperbolicSkewUpperRootPoint_is_commutator s.rank i j hij a) hz

private def hyperbolicUpperBasisVector (n : Nat) (i : Fin n) :
    HyperbolicSpace k n := (Pi.single i 1, 0)

private def hyperbolicLowerBasisVector (n : Nat) (i : Fin n) :
    HyperbolicSpace k n := (0, Pi.single i 1)

private lemma hyperbolicUpperRootPoint_sub_apply (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) (z : HyperbolicSpace k n) :
    (hyperbolicUpperRootPoint n i j hij a).1 z - z =
      ((a * z.1 j) • Pi.single i 1,
        -(a * z.2 i) • Pi.single j 1) := by
  apply Prod.ext <;> funext p <;>
    simp [hyperbolicUpperRootPoint, hyperbolicUpperRoot,
      hyperbolicUpperRootLinearEquiv]

private lemma hyperbolicLowerRootPoint_sub_apply (n : Nat) (i j : Fin n)
    (hij : i ≠ j) (a : k) (z : HyperbolicSpace k n) :
    (hyperbolicLowerRootPoint n i j hij a).1 z - z =
      (0, (a * z.1 j) • Pi.single i 1 -
        (a * z.1 i) • Pi.single j 1) := by
  apply Prod.ext
  · funext p
    simp [hyperbolicLowerRootPoint, hyperbolicLowerRoot,
      hyperbolicLowerRootLinearEquiv]
  · funext p
    simp [hyperbolicLowerRootPoint, hyperbolicLowerRoot,
      hyperbolicLowerRootLinearEquiv]
    ring

private lemma hyperbolicSkewUpperRootPoint_sub_apply
    (n : Nat) (i j : Fin n) (hij : i ≠ j) (a : k)
    (z : HyperbolicSpace k n) :
    (hyperbolicSkewUpperRootPoint n i j hij a).1 z - z =
      ((a * z.2 j) • Pi.single i 1 -
        (a * z.2 i) • Pi.single j 1, 0) := by
  apply Prod.ext
  · funext p
    simp [hyperbolicSkewUpperRootPoint, hyperbolicSkewUpperRoot,
      hyperbolicSkewUpperRootLinearEquiv]
    ring
  · funext p
    simp [hyperbolicSkewUpperRootPoint, hyperbolicSkewUpperRoot,
      hyperbolicSkewUpperRootLinearEquiv]

private lemma evenOrthogonalNatural_upper_propagate
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (hrank : 4 ≤ s.rank)
    (W : Submodule k V)
    (hW : IsInvariantSubmodule (evenOrthogonalNaturalRepresentation s) W)
    (i : Fin s.rank)
    (hi : hyperbolicUpperBasisVector (k := k) s.rank i ∈
      W.map s.isometry.toLinearEquiv.toLinearMap) :
    ∀ j : Fin s.rank,
      hyperbolicUpperBasisVector (k := k) s.rank j ∈
        W.map s.isometry.toLinearEquiv.toLinearMap := by
  intro j
  by_cases hij : j = i
  · simpa [hij] using hi
  · have hroot := evenOrthogonalNatural_mapped_invariant_under_upperRoot
      s hrank W hW j i hij 1 hi
    have hdiff := (W.map s.isometry.toLinearEquiv.toLinearMap).sub_mem hroot hi
    rw [hyperbolicUpperRootPoint_sub_apply] at hdiff
    simpa [hyperbolicUpperBasisVector, hij] using hdiff

private lemma evenOrthogonalNatural_lower_propagate
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (hrank : 4 ≤ s.rank)
    (W : Submodule k V)
    (hW : IsInvariantSubmodule (evenOrthogonalNaturalRepresentation s) W)
    (i : Fin s.rank)
    (hi : hyperbolicLowerBasisVector (k := k) s.rank i ∈
      W.map s.isometry.toLinearEquiv.toLinearMap) :
    ∀ j : Fin s.rank,
      hyperbolicLowerBasisVector (k := k) s.rank j ∈
        W.map s.isometry.toLinearEquiv.toLinearMap := by
  intro j
  by_cases hij : i = j
  · simpa [hij] using hi
  · have hroot := evenOrthogonalNatural_mapped_invariant_under_upperRoot
      s hrank W hW i j hij 1 hi
    have hdiff := (W.map s.isometry.toLinearEquiv.toLinearMap).sub_mem hroot hi
    rw [hyperbolicUpperRootPoint_sub_apply] at hdiff
    have hneg := (W.map s.isometry.toLinearEquiv.toLinearMap).neg_mem hdiff
    simpa [hyperbolicLowerBasisVector, hij] using hneg

private lemma evenOrthogonalNatural_upper_to_lower
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (hrank : 4 ≤ s.rank)
    (W : Submodule k V)
    (hW : IsInvariantSubmodule (evenOrthogonalNaturalRepresentation s) W)
    (i j : Fin s.rank) (hij : j ≠ i)
    (hi : hyperbolicUpperBasisVector (k := k) s.rank i ∈
      W.map s.isometry.toLinearEquiv.toLinearMap) :
    hyperbolicLowerBasisVector (k := k) s.rank j ∈
      W.map s.isometry.toLinearEquiv.toLinearMap := by
  have hroot := evenOrthogonalNatural_mapped_invariant_under_lowerRoot
    s hrank W hW j i hij 1 hi
  have hdiff := (W.map s.isometry.toLinearEquiv.toLinearMap).sub_mem hroot hi
  rw [hyperbolicLowerRootPoint_sub_apply] at hdiff
  simpa [hyperbolicUpperBasisVector, hyperbolicLowerBasisVector, hij] using hdiff

private lemma evenOrthogonalNatural_lower_to_upper
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (hrank : 4 ≤ s.rank)
    (W : Submodule k V)
    (hW : IsInvariantSubmodule (evenOrthogonalNaturalRepresentation s) W)
    (i j : Fin s.rank) (hij : j ≠ i)
    (hi : hyperbolicLowerBasisVector (k := k) s.rank i ∈
      W.map s.isometry.toLinearEquiv.toLinearMap) :
    hyperbolicUpperBasisVector (k := k) s.rank j ∈
      W.map s.isometry.toLinearEquiv.toLinearMap := by
  have hroot := evenOrthogonalNatural_mapped_invariant_under_skewUpperRoot
    s hrank W hW j i hij 1 hi
  have hdiff := (W.map s.isometry.toLinearEquiv.toLinearMap).sub_mem hroot hi
  rw [hyperbolicSkewUpperRootPoint_sub_apply] at hdiff
  simpa [hyperbolicUpperBasisVector, hyperbolicLowerBasisVector, hij] using hdiff

private lemma evenOrthogonalNatural_detect_upperBasis
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (hrank : 4 ≤ s.rank)
    (W : Submodule k V)
    (hW : IsInvariantSubmodule (evenOrthogonalNaturalRepresentation s) W)
    (z : HyperbolicSpace k s.rank)
    (hz : z ∈ W.map s.isometry.toLinearEquiv.toLinearMap) (hz0 : z ≠ 0) :
    ∃ i : Fin s.rank,
      hyperbolicUpperBasisVector (k := k) s.rank i ∈
        W.map s.isometry.toLinearEquiv.toLinearMap := by
  classical
  have hn : 2 < s.rank := by omega
  by_cases hx : ∃ p : Fin s.rank, z.1 p ≠ 0
  · obtain ⟨p, hp⟩ := hx
    obtain ⟨i, hip, _⟩ := Fin.exists_ne_and_ne_of_two_lt p p hn
    obtain ⟨r, hri, hrp⟩ := Fin.exists_ne_and_ne_of_two_lt i p hn
    have hroot₁ := evenOrthogonalNatural_mapped_invariant_under_upperRoot
      s hrank W hW i p hip 1 hz
    have hdiff₁ :=
      (W.map s.isometry.toLinearEquiv.toLinearMap).sub_mem hroot₁ hz
    rw [hyperbolicUpperRootPoint_sub_apply] at hdiff₁
    have hroot₂ := evenOrthogonalNatural_mapped_invariant_under_upperRoot
      s hrank W hW r i hri 1 hdiff₁
    have hdiff₂ :=
      (W.map s.isometry.toLinearEquiv.toLinearMap).sub_mem hroot₂ hdiff₁
    rw [hyperbolicUpperRootPoint_sub_apply] at hdiff₂
    have hnormalized :=
      (W.map s.isometry.toLinearEquiv.toLinearMap).smul_mem (z.1 p)⁻¹ hdiff₂
    refine ⟨r, ?_⟩
    simpa [hyperbolicUpperBasisVector, hip, hri, hrp, hp,
      inv_mul_cancel₀] using hnormalized
  · push Not at hx
    have hy : ∃ p : Fin s.rank, z.2 p ≠ 0 := by
      by_contra hy
      push Not at hy
      apply hz0
      apply Prod.ext <;> funext p
      · exact hx p
      · exact hy p
    obtain ⟨p, hp⟩ := hy
    obtain ⟨i, hip, _⟩ := Fin.exists_ne_and_ne_of_two_lt p p hn
    obtain ⟨r, hri, hrp⟩ := Fin.exists_ne_and_ne_of_two_lt i p hn
    have hroot₁ :=
      evenOrthogonalNatural_mapped_invariant_under_skewUpperRoot
        s hrank W hW i p hip 1 hz
    have hdiff₁ :=
      (W.map s.isometry.toLinearEquiv.toLinearMap).sub_mem hroot₁ hz
    rw [hyperbolicSkewUpperRootPoint_sub_apply] at hdiff₁
    have hroot₂ := evenOrthogonalNatural_mapped_invariant_under_upperRoot
      s hrank W hW r i hri 1 hdiff₁
    have hdiff₂ :=
      (W.map s.isometry.toLinearEquiv.toLinearMap).sub_mem hroot₂ hdiff₁
    rw [hyperbolicUpperRootPoint_sub_apply] at hdiff₂
    have hnormalized :=
      (W.map s.isometry.toLinearEquiv.toLinearMap).smul_mem (z.2 p)⁻¹ hdiff₂
    refine ⟨r, ?_⟩
    simpa [hyperbolicUpperBasisVector, hip, hri, hrp, hp,
      inv_mul_cancel₀] using hnormalized

public theorem evenOrthogonalNaturalRepresentation_isAlgebraicallyIrreducible
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (hrank : 4 ≤ s.rank) :
    IsAlgebraicallyIrreducibleRepresentation
      (evenOrthogonalNaturalRepresentation s) := by
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    have hWne : ∃ v : V, v ∈ W ∧ v ≠ 0 := by
      by_contra h
      push Not at h
      apply hbot
      apply bot_unique
      intro v hv
      exact h v hv
    obtain ⟨v, hv, hv0⟩ := hWne
    have hsv : s.isometry v ∈ W.map s.isometry.toLinearEquiv.toLinearMap :=
      ⟨v, hv, rfl⟩
    have hsv0 : s.isometry v ≠ 0 := by
      intro h
      apply hv0
      apply s.isometry.injective
      simpa using h
    obtain ⟨i, hi⟩ :=
      evenOrthogonalNatural_detect_upperBasis s hrank W hW
        (s.isometry v) hsv hsv0
    have hallUpper := evenOrthogonalNatural_upper_propagate
      s hrank W hW i hi
    have hn : 2 < s.rank := by omega
    obtain ⟨j, hji, _⟩ := Fin.exists_ne_and_ne_of_two_lt i i hn
    have hjLower := evenOrthogonalNatural_upper_to_lower
      s hrank W hW i j hji hi
    have hallLower := evenOrthogonalNatural_lower_propagate
      s hrank W hW j hjLower
    have hmapTop : W.map s.isometry.toLinearEquiv.toLinearMap = ⊤ := by
      apply (Submodule.eq_top_iff_forall_basis_mem
        ((Pi.basisFun k (Fin s.rank)).prod
          (Pi.basisFun k (Fin s.rank)))).2
      intro q
      cases q with
      | inl i =>
          simpa [hyperbolicUpperBasisVector] using hallUpper i
      | inr i =>
          simpa [hyperbolicLowerBasisVector] using hallLower i
    apply top_unique
    intro x
    have hsx : s.isometry x ∈ W.map s.isometry.toLinearEquiv.toLinearMap := by
      rw [hmapTop]
      exact Submodule.mem_top
    obtain ⟨w, hw, hwx⟩ := hsx
    have hwx' : w = x := s.isometry.injective hwx
    simpa [hwx'] using hw

public theorem evenOrthogonalNaturalRepresentation_isIrreducible
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} (s : SplitQuadraticForm Q)
    (hrank : 4 ≤ s.rank) :
    IsIrreducibleRepresentation (evenOrthogonalNaturalRepresentation s) :=
  ⟨evenOrthogonalNaturalRepresentation_isRational s,
    evenOrthogonalNaturalRepresentation_isAlgebraicallyIrreducible s hrank⟩

end Theory.AlgebraicGroup
