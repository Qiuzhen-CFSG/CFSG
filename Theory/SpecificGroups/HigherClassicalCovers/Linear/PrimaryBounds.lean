module

public import Theory.SpecificGroups.HigherClassicalCovers.Linear.Projection
public import Theory.SpecificGroups.PSL4.OddCentralKernels
public import Theory.GroupTheory.CoveringKernelBound
public import Theory.GroupTheory.CoveringKernelEquiv

/-!
# Assembling the primary bounds for the degree-four linear cover

Exclude the defining prime and the other odd primes from the canonical
universal kernel. It is then a two-group, so a bound for its Sylow two-subgroup
bounds the whole kernel. The scalar covering attains that bound. The resulting
isomorphism from the canonical universal group to SL₄ supplies the actual
unique-lifting property, in every target universe, and identifies the universal
kernel multiplicatively.

Source: Aschbacher–Smith I.1.1 and I.1.4(1),(3), printed pp.407–408,
citing GLS98 §6.1. The defining-prime exclusion and the Sylow two-bound remain
explicit here. They are independent mathematical obligations; this conditional
assembly does not assert the completed source rows. At field order three,
the other-prime exclusion is already proved by cyclic-Sylow transfer.
-/

@[expose] public section

namespace Theory.SpecificGroups.HigherClassicalCovers.Linear

open Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups

universe u w

variable (F : Type u) [Field F] [Finite F]

/-- The kernel of the existing constructed universal perfect central cover. -/
abbrev UniversalKernel := (universalProjection PSL(4, F)).ker

/-- The independent nondefining-prime input. It concerns every finite perfect
central cover of this literal projective group in its universe. -/
def NondefiningKernelExclusion (p : ℕ) : Prop :=
  ∀ {E : Type u} [Group E] [Finite E] (f : PerfectCentralCovering.Cover E PSL(4, F))
    (r : ℕ), r.Prime → r ≠ 2 → r ≠ p → ¬ r ∣ Nat.card f.toMonoidHom.ker

/-- Cyclic-Sylow transfer already proves the independent input at p = 3. -/
theorem nondefiningKernelExclusion_three (hF : Nat.card F = 3) :
    NondefiningKernelExclusion F 3 := by
  intro E _ _ f r hr hr2 hr3 hd
  rcases Matrix.PSL4.OddCentralKernels.prime_dvd_kernel_eq_two_or_three hF f hr hd
    with h | h
  · exact hr2 h
  · exact hr3 h

/-- Removing the odd primes makes the actual universal kernel a two-group. -/
theorem universalKernel_isTwoGroup_of_odd_exclusions {p : ℕ}
    (hnondef : NondefiningKernelExclusion F p)
    (hdef : ¬ p ∣ Nat.card (UniversalKernel F)) :
    IsPGroup 2 (UniversalKernel F) := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro r hr
  obtain ⟨hrprime, hrdvd, _⟩ := Nat.mem_primeFactors.mp hr
  have hr2 : r = 2 := by
    by_contra hr2
    by_cases hrp : r = p
    · exact hdef (hrp ▸ hrdvd)
    · exact hnondef (universalCover PSL(4, F)) r hrprime hr2 hrp hrdvd
  subst r
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_rfl, by decide⟩

/-- The Sylow two-bound and the two independent odd-prime exclusions give
the numerical hypothesis of `Covering.isUniversal_of_kernel_card_le`. -/
theorem universalKernel_card_le_of_primary_bounds {p : ℕ}
    (hnondef : NondefiningKernelExclusion F p)
    (hdef : ¬ p ∣ Nat.card (UniversalKernel F))
    (htwo : ∀ P : Sylow 2 (UniversalKernel F),
      Nat.card P ≤ Nat.gcd 4 (Nat.card F - 1)) :
    Nat.card (UniversalKernel F) ≤ Nat.gcd 4 (Nat.card F - 1) := by
  have hK := universalKernel_isTwoGroup_of_odd_exclusions F hnondef hdef
  let P : Sylow 2 (UniversalKernel F) :=
    (hK.to_subgroup ⊤).toSylow (by simp)
  have h := htwo P
  change Nat.card (⊤ : Subgroup (UniversalKernel F)) ≤ _ at h
  simpa only [Subgroup.card_top] using h

/-- The exact unique-lifting property of the literal projection follows from
the primary calculations, not just its scalar kernel computation. -/
theorem projection_isUniversal_of_primary_bounds {p : ℕ}
    (hnondef : NondefiningKernelExclusion F p)
    (hdef : ¬ p ∣ Nat.card (UniversalKernel F))
    (htwo : ∀ P : Sylow 2 (UniversalKernel F),
      Nat.card P ≤ Nat.gcd 4 (Nat.card F - 1)) :
    Theory.GroupTheory.Covering.IsUniversal.{u, u, w} (projectionCovering F) := by
  apply Theory.GroupTheory.Covering.isUniversal_of_kernel_card_le
  rw [projectionCovering_toMonoidHom, card_projectionKernel]
  exact universalKernel_card_le_of_primary_bounds F hnondef hdef htwo

/-- The same primary calculation identifies the kernel of the constructed
universal cover with the scalar kernel, preserving multiplication. -/
noncomputable def universalKernelEquivCyclic_of_primary_bounds {p : ℕ}
    (hnondef : NondefiningKernelExclusion F p)
    (hdef : ¬ p ∣ Nat.card (UniversalKernel F))
    (htwo : ∀ P : Sylow 2 (UniversalKernel F),
      Nat.card P ≤ Nat.gcd 4 (Nat.card F - 1)) :
    UniversalKernel F ≃* Multiplicative (ZMod (Nat.gcd 4 (Nat.card F - 1))) :=
  ((universalQuasisimpleCover_isUniversal PSL(4, F)).kerMulEquiv
    (projection_isUniversal_of_primary_bounds F hnondef hdef htwo)
    (MulEquiv.refl PSL(4, F))).trans (projectionKernelEquivCyclic F)

/-- The ternary source row reduces to precisely its defining and two-primary
calculations. Its other-prime exclusion is discharged. -/
theorem projection_three_isUniversal_of_primary_bounds (hF : Nat.card F = 3)
    (hdef : ¬ 3 ∣ Nat.card (UniversalKernel F))
    (htwo : ∀ P : Sylow 2 (UniversalKernel F), Nat.card P ≤ 2) :
    Theory.GroupTheory.Covering.IsUniversal.{u, u, w} (projectionCovering F) := by
  apply projection_isUniversal_of_primary_bounds F
    (nondefiningKernelExclusion_three F hF) hdef
  intro P
  norm_num [hF]
  exact htwo P

/-- The Fermat source row uses the actual prime-field size. Only the
independent nondefining input may remain in the completed source theorem. -/
theorem projection_fermat_isUniversal_of_primary_bounds {p : ℕ}
    (hF : Nat.card F = p) (hp : 3 < p)
    (hfermat : ∃ m : ℕ, p = 2 ^ (2 ^ m) + 1)
    (hnondef : NondefiningKernelExclusion F p)
    (hdef : ¬ p ∣ Nat.card (UniversalKernel F))
    (htwo : ∀ P : Sylow 2 (UniversalKernel F), Nat.card P ≤ 4) :
    Theory.GroupTheory.Covering.IsUniversal.{u, u, w} (projectionCovering F) := by
  have hcard : Nat.gcd 4 (Nat.card F - 1) = 4 := by
    rw [← card_projectionKernel]
    exact card_projectionKernel_four F (hF ▸ fermat_mod_four hp hfermat)
  apply projection_isUniversal_of_primary_bounds F hnondef hdef
  intro P
  rw [hcard]
  exact htwo P

end Theory.SpecificGroups.HigherClassicalCovers.Linear
