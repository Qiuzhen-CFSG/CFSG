module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Basic
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Co3Witness
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Co3Kernel
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound

/-!
# Assembly of the binary symplectic universal double cover

The covering group, its projection to the literal Sp₆(2) matrix group,
finiteness, quasisimplicity and universality are constructed in `Basic`.
The concrete Co₃ commutator supplies the lower-bound witness, and the checked
presentation and two-graph calculations discharge the upper and lower kernel
bounds. The resulting cover and binary kernel equivalence are exported below.

Source: Aschbacher–Smith A.2.2(4), printed p.33, includes Sp₆(2), whereas
I.1.4, printed p.408, omits its multiplier row. The ATLAS S₆(2) page reports
multiplier 2: https://brauer.maths.qmul.ac.uk/Atlas/v3/clas/S62/ . This source
observation is not used as a Lean proof input.
-/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover
open Theory.GroupTheory

universe u w

/-- The concrete nontrivial commutator gives the lower bound once centrality
of the actual Co₃ quotient kernel has been established. -/
theorem kernel_nontrivial_of_co3_kernel_central
    (hc : Co3Witness.matrixProjection.ker ≤ Subgroup.center Co3Witness.ExtensionGroup) :
    Nontrivial projection.ker :=
  kernel_nontrivial_of_central_extension Co3Witness.matrixProjection
    Co3Witness.matrixProjection_surjective hc Co3Witness.z
    Co3Witness.z_mem_kernel Co3Witness.z_mem_commutator Co3Witness.z_ne_one

/-- Assembly of the independent upper bound and concrete lower-bound witness. -/
theorem kernel_card_two_of_upper_bound_and_co3
    (hupper : Nat.card projection.ker ≤ 2)
    (hc : Co3Witness.matrixProjection.ker ≤ Subgroup.center Co3Witness.ExtensionGroup) :
    Nat.card projection.ker = 2 := by
  let : Nontrivial projection.ker := kernel_nontrivial_of_co3_kernel_central hc
  exact Nat.le_antisymm hupper Finite.one_lt_card

/-- The precise canonical kernel equivalence, conditional on the two remaining
kernel calculations. -/
noncomputable def kernelEquiv_of_upper_bound_and_co3
    (hupper : Nat.card projection.ker ≤ 2)
    (hc : Co3Witness.matrixProjection.ker ≤ Subgroup.center Co3Witness.ExtensionGroup) :
    projection.ker ≃* Multiplicative (ZMod 2) :=
  kernelEquiv_of_card_two (kernel_card_two_of_upper_bound_and_co3 hupper hc)

/-- The full universal-cover statement after discharging both kernel
calculations. -/
theorem universalDoubleCover_of_upper_bound_and_co3
    (hupper : Nat.card projection.ker ≤ 2)
    (hc : Co3Witness.matrixProjection.ker ≤ Subgroup.center Co3Witness.ExtensionGroup) :
    Covering.IsUniversal.{0, 0, w} cover ∧
      Nonempty (projection.ker ≃* Multiplicative (ZMod 2)) :=
  ⟨cover_isUniversal, ⟨kernelEquiv_of_upper_bound_and_co3 hupper hc⟩⟩

/-- The canonical universal kernel has exactly two elements. -/
theorem kernel_card_two : Nat.card projection.ker = 2 :=
  kernel_card_two_of_upper_bound_and_co3 kernel_card_le_two
    Co3Witness.matrixProjection_ker_le_center

/-- An explicit multiplicative identification of the canonical universal
kernel with the binary cyclic group. -/
noncomputable def kernelEquiv : projection.ker ≃* Multiplicative (ZMod 2) :=
  kernelEquiv_of_card_two kernel_card_two

/-- The canonical finite quasisimple cover is universal and has binary kernel. -/
theorem universalDoubleCover :
    Covering.IsUniversal.{0, 0, w} cover ∧
      Nonempty (projection.ker ≃* Multiplicative (ZMod 2)) :=
  ⟨cover_isUniversal, ⟨kernelEquiv⟩⟩

/-- Transfer the eventual calculation to any chosen universal cover, using
its actual homomorphism to the same literal matrix model. -/
noncomputable def chosenKernelEquiv_of_upper_bound_and_co3
    {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L Base) (hf : Covering.IsUniversal.{0, u, 0} f)
    (hupper : Nat.card projection.ker ≤ 2)
    (hc : Co3Witness.matrixProjection.ker ≤ Subgroup.center Co3Witness.ExtensionGroup) :
    f.toMonoidHom.ker ≃* Multiplicative (ZMod 2) :=
  (chosenKernelEquiv f hf).trans (kernelEquiv_of_upper_bound_and_co3 hupper hc)

/-- Transfer the explicit binary-kernel calculation to any chosen universal
cover of the same literal matrix group. -/
noncomputable def chosenKernelEquiv_final
    {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L Base) (hf : Covering.IsUniversal.{0, u, 0} f) :
    f.toMonoidHom.ker ≃* Multiplicative (ZMod 2) :=
  (chosenKernelEquiv f hf).trans kernelEquiv

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover
