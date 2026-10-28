module

public import Theory.SpecificGroups.Rudvalis.Multiplier.OddPrimary
public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary
public import Theory.GroupTheory.CoveringKernelEquiv
public import Theory.GroupTheory.CoveringKernelTwo
public import Theory.GroupTheory.PerfectCentralCoverRank
public import Theory.GroupTheory.UniversalCoverKernelTransport

/-!
# Rudvalis covering kernels

The Schur multiplier of the actual Rudvalis model is cyclic of order two.
The odd-primary calculation and the max4 covering calculation bound every
finite perfect central kernel by two. Universality gives a surjective lift
onto the constructed perfect double cover, so its kernel order divides the
universal kernel order. The two bounds force equality and identify the kernel
as a group. This canonical calculation needs no simplicity hypothesis.

For the quasisimple covering interface, `kernel_equiv_two` applies to any
chosen universal covering under the explicit source-domain quasisimplicity
hypothesis. The final transport theorem uses an actual isomorphism from a
source quasisimple group. The earlier conditional comparison and odd-central-
kernel source applications are preserved.

Source: Aschbacher–Smith I.1.3(1), printed p.407, with universal coverings as
in I.1.1. Final I.1.3 table assembly remains with `qt-i-01-multipliers-altspor`.
-/

namespace Rudvalis.Multiplier
open PerfectCentralCovering Theory.GroupTheory

/-- The odd-primary result and the two-primary bound give the full kernel upper bound. -/
public theorem universal_kernel_card_le_two_of_not_four_dvd
    (hfour : ¬ 4 ∣ Nat.card (universalProjection Model).ker) :
    Nat.card (universalProjection Model).ker ≤ 2 := by
  have hp := kernel_isPGroup (universalProjection Model)
    (universalProjection_surjective Model) (universalProjection_ker_le_center Model)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! h
    apply hfour
    rw [hn]
    exact pow_dvd_pow 2 h
  rw [hn]
  calc
    2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hnle
    _ = 2 := by norm_num

/-- Upper/lower-bound assembly for any chosen universal covering of the source model.
The double cover need not initially be known universal. -/
public theorem kernel_equiv_two_of_primary_bound_and_double_cover
    [IsQuasisimple Model]
    {U E : Type} [Group U] [Finite U] [IsQuasisimple U]
    [Group E] [Finite E]
    (f : Covering U Model) (hf : Covering.IsUniversal.{0,0,0} f)
    (hfour : ¬ 4 ∣ Nat.card (universalProjection Model).ker)
    (c : Cover E Model) (hc : Nat.card c.toMonoidHom.ker = 2) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 2)) := by
  let : IsQuasisimple E := c.isQuasisimple
  have hne : c.toCovering.toMonoidHom.ker ≠ ⊥ := by
    intro h
    have he : Nat.card c.toMonoidHom.ker = 1 := Subgroup.card_eq_one.mpr h
    omega
  obtain ⟨hu, he⟩ := Covering.isUniversal_and_kernel_equiv_two_of_bound
    c.toCovering hne (universal_kernel_card_le_two_of_not_four_dvd hfour)
  obtain ⟨e⟩ := he
  exact ⟨(hf.kerMulEquiv hu (MulEquiv.refl Model)).trans e⟩

/-- The upper bound and the surjective universal lift onto the concrete double
cover force the canonical universal kernel to have order exactly two. -/
public theorem universal_kernel_card_two :
    Nat.card (universalProjection Model).ker = 2 := by
  obtain ⟨h, hh, _⟩ := universalProjection_existsUnique_lift
    DoubleCover.covering.toMonoidHom DoubleCover.covering.surjective
    DoubleCover.covering.ker_le_center
  have hs : Function.Surjective h :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      DoubleCover.covering.toMonoidHom h
      (hh ▸ universalProjection_surjective Model) DoubleCover.covering.ker_le_center
  have hd := kernel_card_dvd_of_surjective_factor (universalProjection Model)
    DoubleCover.covering.toMonoidHom h hs hh
  rw [DoubleCover.kernel_card_two] at hd
  exact le_antisymm (kernel_card_le_two (universalCover Model))
    (Nat.le_of_dvd Nat.card_pos hd)

/-- I.1.3(1), Ru: the canonical Schur multiplier is cyclic of order two.
Perfectness of the actual model suffices; no simplicity premise is used. -/
public theorem schurMultiplier_equiv_two
    : Nonempty (PerfectCentralCovering.schurMultiplier Model ≃*
      Multiplicative (ZMod 2)) :=
  ⟨mulEquivOfPrimeCardEq universal_kernel_card_two (by simp)⟩

/-- The source-domain formulation for any chosen universal quasisimple covering.
Both multiplier bounds are discharged on the actual Rudvalis model. -/
public theorem kernel_equiv_two
    [IsQuasisimple Model]
    {U : Type} [Group U] [Finite U] [IsQuasisimple U]
    (f : Covering U Model) (hf : Covering.IsUniversal.{0, 0, 0} f) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 2)) := by
  exact kernel_equiv_two_of_primary_bound_and_double_cover f hf
    universal_kernel_not_four_dvd
    DoubleCover.covering DoubleCover.kernel_card_two

/-- Transport the Ru row to the source group's literal canonical multiplier.
Quasisimplicity is inherited through the supplied model isomorphism. -/
public theorem schurMultiplier_equiv_two_of_model
    {S : Type*} [Group S] [Finite S] [IsQuasisimple S]
    (hS : Nonempty (S ≃* Model)) :
    Nonempty (PerfectCentralCovering.schurMultiplier S ≃* Multiplicative (ZMod 2)) := by
  obtain ⟨e⟩ := hS
  let : IsQuasisimple Model := IsQuasisimple.of_mulEquiv e
  obtain ⟨k⟩ := schurMultiplier_equiv_two
  exact ⟨(schurMultiplierCongr e).trans k⟩

end Rudvalis.Multiplier
