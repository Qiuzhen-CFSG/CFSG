module

public import Theory.Representation.BinaryNaturalDual.FourActors.NaturalMarking
public import Theory.Representation.BinaryNaturalDual.FourActors.A1Module
public import Theory.Representation.BinaryNaturalDual.FourActors.A2Module
public import Theory.Representation.BinaryNaturalDual.FourActors.PermutationCatalogue.Representatives

/-!
# Fixed spaces and cores of the three marked four-dimensional actors

The exceptional comparison identifies natural transvections with four-pair
permutations and identifies the two-block actor with the radical of the
explicit plane `A0Plane`. The elementary orders and these marking theorems
discharge every premise in the three module calculations. The only remaining
input is the natural-plus-dual coordinate action itself.

The mixed actor retains its three actual transvections, their distinct
hyperplane axes, and the common fixed planes on both summands. Its corank-two
core is the sum of the inner and outer fixed spaces, independently of the
chosen outer element, and equals the displacement span of the whole actor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3(4–6)
and its proof, printed pp.391–392, PDF pp.402–403.
-/

public section

namespace BinaryNaturalDual.FourActors.Parameters
open BinaryLinear.OuterCyclic PermutationCatalogue
open Representation.RegularCyclicNormalClosure

private theorem fixedSpace_dimension_eq (g : G) :
    Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace g) =
      Module.finrank (ZMod 2) g.fixedSubmodule :=
  congrArg (fun U : Submodule (ZMod 2) X => Module.finrank (ZMod 2) U)
    (LinearMap.fixedSubmodule_eq_ker g.toLinearMap).symm

private theorem transvection_dimension (g : G) (hg : IsTransvection g) :
    Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace g) = 3 :=
  (fixedSpace_dimension_eq g).trans (transvection_fixed_finrank hg)

private theorem other_dimension (g : G) (h2 : g ^ 2 = 1) (h1 : g ≠ 1)
    (ht : ¬ IsTransvection g) :
    Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace g) = 2 :=
  (fixedSpace_dimension_eq g).trans (nontransvection_involution_fixed_finrank g h1 h2 ht)

/-- The actual two-block representative is the radical of the marked plane. -/
theorem A0_radical : A0 = radicalImage A0Plane := A0_eq_radicalImage A0_card

/-- The literal fixed module, including the marked natural plane and its dual. -/
theorem A0_fixed (d : CoordinateAction 4) :
    actorFixed d A0 = A0Plane.prod A0Plane.dualAnnihilator := by
  rw [A0_radical]
  apply actorFixed_radicalImage
  · intro h
    have hd := A0Plane_finrank
    rw [h, finrank_bot] at hd
    contradiction
  · intro h
    have hd := A0Plane_finrank
    rw [h, finrank_top] at hd
    simp [X, BinaryLinear.OuterCyclic.Space] at hd

theorem A0_parameters (d : CoordinateAction 4) :
    Module.finrank (ZMod 2) (actorFixed d A0) = 4 ∧ actorCore d A0 2 = ⊤ := by
  rw [A0_radical]
  exact radicalImage_parameters d A0Plane A0Plane_finrank

/-- The distinguished actor is induced by a unique natural transvection in A₁. -/
theorem A1_transvection :
    ∃ g : G, MulAut.conj g = r ∧ IsTransvection g ∧
      ∀ h : G, MulAut.conj h ∈ A1 → IsTransvection h → h = g :=
  ⟨A1Module.linear 7, A1Module.distinguished_transvection isTransvection_iff_cycleType⟩

theorem A1_parameters (d : CoordinateAction 4) :
    Module.finrank (ZMod 2) (actorFixed d A1) = 1 ∧
      actorCore d A1 2 = BinaryNaturalDual.fixedSpace (action d r) ∧
      Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace (action d r)) = 6 :=
  A1Module.parameters d A1_elementary A1_card

/-- The one-dimensional fixed space is the specified diagonal line. -/
theorem A1_fixed_line (d : CoordinateAction 4) :
    actorFixed d A1 = Submodule.span (ZMod 2)
      {((![1,1,0,0] : X), 0) +
        d.representation transposition ((![1,1,0,0] : X), 0)} :=
  A1Module.actor_fixed_span d A1_elementary

/-- These are exactly the three natural transvections in the mixed inner actor,
with pairwise distinct three-dimensional fixed hyperplanes. -/
theorem A2_three_transvections :
    (∀ i : Fin 3, MulAut.conj (A2Module.axisLinear i) ∈ B2 ∧
      IsTransvection (A2Module.axisLinear i) ∧
      Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace (A2Module.axisLinear i)) = 3) ∧
    Function.Injective (fun i : Fin 3 =>
      BinaryNaturalDual.fixedSpace (A2Module.axisLinear i)) ∧
    (∀ g : G, g ∈ innerPreimage B2 →
      (IsTransvection g ↔ ∃ i : Fin 3, g = A2Module.axisLinear i)) :=
  ⟨fun i => ⟨A2Module.conj_axisLinear_mem i,
      A2Module.axisLinear_isTransvection isTransvection_iff_cycleType i,
      A2Module.axisLinear_fixedSpace_finrank isTransvection_iff_cycleType
        transvection_dimension i⟩,
    A2Module.axisLinear_fixedSpace_injective isTransvection_iff_cycleType,
    fun _ hg => A2Module.isTransvection_iff_axisLinear isTransvection_iff_cycleType hg⟩

/-- Any two of the actual axes generate the natural module. -/
theorem A2_axes_span {i j : Fin 3} (hij : i ≠ j) :
    BinaryNaturalDual.fixedSpace (A2Module.axisLinear i) ⊔
      BinaryNaturalDual.fixedSpace (A2Module.axisLinear j) = ⊤ :=
  A2Module.axisLinear_fixedSpace_sup isTransvection_iff_cycleType transvection_dimension hij

/-- The two inner fixed planes are annihilators, with their actual marked action. -/
theorem A2_fixed_planes :
    Module.finrank (ZMod 2) (naturalFixed B2) = 2 ∧
      A2Module.dualFixed B2 = (naturalFixed B2).dualAnnihilator ∧
      Module.finrank (ZMod 2) (A2Module.dualFixed B2) = 2 :=
  ⟨A2Module.naturalFixed_B2_finrank isTransvection_iff_cycleType other_dimension,
    A2Module.dualFixed_B2_eq_dualAnnihilator isTransvection_iff_cycleType
      transvection_dimension other_dimension,
    A2Module.dualFixed_B2_finrank isTransvection_iff_cycleType
      transvection_dimension other_dimension⟩

/-- Every other nonidentity inner element fixes exactly these planes. -/
theorem A2_other_fixed {g : G} (hg : g ∈ innerPreimage B2) (h1 : g ≠ 1)
    (ht : ¬ IsTransvection g) :
    BinaryNaturalDual.fixedSpace g = naturalFixed B2 ∧
      BinaryNaturalDual.fixedSpace g.symm.dualMap = A2Module.dualFixed B2 :=
  A2Module.other_fixedSpaces_eq_common isTransvection_iff_cycleType
    transvection_dimension other_dimension hg h1 ht

theorem A2_parameters (d : CoordinateAction 4) {a : M} (ha : a ∈ A2) (haB : a ∉ B2) :
    (∀ v : V, v ∈ actorFixed d A2 ↔ ∃ x ∈ naturalFixed B2,
      (x, 0) + d.representation a (x, 0) = v) ∧
    Module.finrank (ZMod 2) (actorFixed d A2) = 2 ∧
    actorCore d A2 2 = actorFixed d B2 ⊔ BinaryNaturalDual.fixedSpace (action d a) ∧
    Module.finrank (ZMod 2) (actorCore d A2 2) = 6 :=
  A2Module.parameters isTransvection_iff_cycleType transvection_dimension other_dimension
    A2_card d ha haB

/-- The mixed fixed sum is the actual commutator module [V,A₂]. -/
theorem A2_mixed_eq_displacement (d : CoordinateAction 4) {a : M}
    (ha : a ∈ A2) (haB : a ∉ B2) :
    actorFixed d B2 ⊔ BinaryNaturalDual.fixedSpace (action d a) =
      displacementSpan d.representation A2 ⊤ :=
  A2Module.mixed_fixed_sum_eq_displacement isTransvection_iff_cycleType
    transvection_dimension other_dimension d ha haB

/-- The source's displayed sum does not depend on the outer representative. -/
theorem A2_mixed_independent (d : CoordinateAction 4) {a a' : M}
    (ha : a ∈ A2) (haB : a ∉ B2) (ha' : a' ∈ A2) (haB' : a' ∉ B2) :
    actorFixed d B2 ⊔ BinaryNaturalDual.fixedSpace (action d a) =
      actorFixed d B2 ⊔ BinaryNaturalDual.fixedSpace (action d a') :=
  (A2_mixed_eq_displacement d ha haB).trans (A2_mixed_eq_displacement d ha' haB').symm

/-- The corank-two core is the commutator module of the whole mixed actor. -/
theorem A2_core_eq_displacement (d : CoordinateAction 4) :
    actorCore d A2 2 = displacementSpan d.representation A2 ⊤ :=
  A2Module.actorCore_eq_displacement isTransvection_iff_cycleType
    transvection_dimension other_dimension A2_card d

end BinaryNaturalDual.FourActors.Parameters
