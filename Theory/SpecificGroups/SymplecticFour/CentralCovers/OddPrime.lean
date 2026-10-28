module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Assembly
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TransvectionLifts
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection

/-!
# Odd-prime symplectic covering calculation

For every odd prime p and finite field F of cardinality p, the literal map
Sp₄(F) → Sp₄(F)/Z(Sp₄(F)) is the universal covering, with kernel C₂.
`LargeSections` and `TernarySection` prove central closure over the prime
fields, including p = 3. The entrywise field isomorphism in `Assembly`
transports those results to F and discharges the universal-property premise.

The canonical universal group is identified with the actual matrix group by
an isomorphism commuting with the projections. This also gives unique lifting
through arbitrary central extensions, without finiteness or perfectness of
the extension group. `CoveringKernelEquiv` transports the explicit C₂ kernel
calculation to the canonical universal projection.

Source: Aschbacher–Smith A.2.2(2), printed p.33, and I.1.1–I.1.4,
printed pp.407–408; GLS3 §6.1. The displayed I.1.4 list omits the ordinary
odd-prime symplectic row. The ternary case is proved directly on Sp₄(3),
without assuming its projective comparison with U₄(2).
-/

public section
noncomputable section

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime

open Theory.GroupTheory

universe u v
variable {F : Type u} [Field F] [Finite F]
variable {p : ℕ} [Fact p.Prime]

section CardinalBound
variable [Fact (2 < Nat.card F)]

/-- The actual central quotient of Sp₄(F) is universal for every odd prime
field cardinality, including three, in every target universe. -/
theorem quotientCover_isUniversal (hp2 : p ≠ 2) (hcard : Nat.card F = p) :
    Covering.IsUniversal.{u, u, v} (quotientCover F) := by
  apply isUniversal_of_prime_field_sections (p := p) hcard
  intro E _ _ f
  by_cases h3 : p = 3
  · cases h3
    exact TernarySection.exists_section f
  · have hp := (Fact.out : p.Prime).two_le
    exact LargeSections.exists_section (by omega) f

/-- The canonical universal group is the literal symplectic matrix group. -/
def canonicalEquiv (hp2 : p ≠ 2) (hcard : Nat.card F = p) :
    PerfectCentralCovering.UniversalGroup (PSp F) ≃* Sp F :=
  Classical.choose (Covering.existsUnique_mulEquiv_of_isUniversal Covering.id
    (PerfectCentralCovering.universalQuasisimpleCover (PSp F)) (quotientCover F)
    (PerfectCentralCovering.universalQuasisimpleCover_isUniversal (PSp F))
    (quotientCover_isUniversal hp2 hcard))

/-- The comparison isomorphism respects the specified quotient map. -/
theorem canonicalEquiv_projection (hp2 : p ≠ 2) (hcard : Nat.card F = p)
    (x : PerfectCentralCovering.UniversalGroup (PSp F)) :
    QuotientGroup.mk' (Subgroup.center (Sp F)) (canonicalEquiv hp2 hcard x) =
      PerfectCentralCovering.universalProjection (PSp F) x := by
  have h := (Classical.choose_spec
    (Covering.existsUnique_mulEquiv_of_isUniversal Covering.id
      (PerfectCentralCovering.universalQuasisimpleCover (PSp F)) (quotientCover F)
      (PerfectCentralCovering.universalQuasisimpleCover_isUniversal (PSp F))
      (quotientCover_isUniversal hp2 hcard))).1
  exact congrArg (fun q : Covering _ (PSp F) => q x) h

/-- Strong universality of the literal quotient homomorphism: every central
extension admits a unique compatible homomorphism from Sp₄(F). -/
theorem quotient_existsUnique_lift (hp2 : p ≠ 2) (hcard : Nat.card F = p)
    {E : Type v} [Group E] (f : E →* PSp F) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center E) :
    ∃! s : Sp F →* E,
      f.comp s = QuotientGroup.mk' (Subgroup.center (Sp F)) := by
  let e := canonicalEquiv hp2 hcard
  obtain ⟨s, hs, _⟩ :=
    PerfectCentralCovering.universalProjection_existsUnique_lift f hf hc
  have ht : f.comp (s.comp e.symm.toMonoidHom) =
      QuotientGroup.mk' (Subgroup.center (Sp F)) := by
    apply MonoidHom.ext
    intro x
    have hx := canonicalEquiv_projection hp2 hcard (e.symm x)
    change QuotientGroup.mk' (Subgroup.center (Sp F)) (e (e.symm x)) = _ at hx
    rw [e.apply_symm_apply] at hx
    exact (DFunLike.congr_fun hs (e.symm x)).trans hx.symm
  refine ⟨s.comp e.symm.toMonoidHom, ht, ?_⟩
  intro t ht'
  exact PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq f hc
    t (s.comp e.symm.toMonoidHom) (ht'.trans ht.symm)

/-- The canonical Schur multiplier is C₂, with all central-closure premises
discharged. This uses the comparison of kernels of universal coverings. -/
def primeUniversalKernelEquivC2 (hp2 : p ≠ 2) (hcard : Nat.card F = p) :
    (PerfectCentralCovering.universalProjection (PSp F)).ker ≃*
      Multiplicative (ZMod 2) :=
  universalKernelEquivC2 (two_ne_zero (Fact.out : p.Prime) hp2 hcard)
    (quotientCover_isUniversal hp2 hcard)

/-- The order of the canonical Schur multiplier is exactly two. -/
theorem card_universalKernel (hp2 : p ≠ 2) (hcard : Nat.card F = p) :
    Nat.card (PerfectCentralCovering.universalProjection (PSp F)).ker = 2 := by
  rw [Nat.card_congr (primeUniversalKernelEquivC2 hp2 hcard).toEquiv]
  simp

end CardinalBound

/-- The universal double cover, requiring only the prime cardinality and its
oddness. The carrier and projection are the literal central quotient of Sp₄. -/
theorem universal_double_cover (hp2 : p ≠ 2) (hcard : Nat.card F = p) :
    letI : Fact (2 < Nat.card F) := ⟨card_gt_two (Fact.out : p.Prime) hp2 hcard⟩
    Covering.IsUniversal.{u, u, v} (quotientCover F) ∧
      Nonempty ((quotientCover F).toMonoidHom.ker ≃* Multiplicative (ZMod 2)) ∧
      Nonempty ((PerfectCentralCovering.universalProjection (PSp F)).ker ≃*
        Multiplicative (ZMod 2)) := by
  let : Fact (2 < Nat.card F) := ⟨card_gt_two (Fact.out : p.Prime) hp2 hcard⟩
  exact ⟨quotientCover_isUniversal hp2 hcard,
    ⟨kernelEquivC2 (two_ne_zero (Fact.out : p.Prime) hp2 hcard)⟩,
    ⟨primeUniversalKernelEquivC2 hp2 hcard⟩⟩

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
