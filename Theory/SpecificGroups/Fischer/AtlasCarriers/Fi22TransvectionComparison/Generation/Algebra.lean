module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.RootWords

/-!
# Algebraic consequences of the Fi22 Schreier edges

Membership of every forward Schreier edge in the commuting-conjugate subgroup
implies equivariance of the shared conjugate words: the edge centralizes A.
Equivariance extends from the two generators to the whole actual carrier.
A singleton distinguished fiber then implies injectivity of the labeling,
and the fixed labels cover exactly the conjugates commuting with A.

These are conditional deductions for the finite certificates, not an assumed
centralizer description. `Generation` applies them to its checked distinguished
fiber and retains the edge-membership obligation explicitly.

Source: the conjugation-action paragraph after GLS3 Table 5.3t in
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

@[expose] public section

namespace Sporadic.Fischer.Fi22.TransvectionComparison

theorem conjugateAt_equivariant_of_edges
    (hedge : ∀ s ∈ atlasGenerators, ∀ x,
      (pointTransport (inclusion s x))⁻¹ * s * pointTransport x ∈
        commutingConjugateSubgroup)
    (s : Carrier) (hs : s ∈ atlasGenerators) (x : Fin 3510) :
    conjugateAt (inclusion s x) = s * conjugateAt x * s⁻¹ := by
  let e := (pointTransport (inclusion s x))⁻¹ * s * pointTransport x
  have hc : e * atlasA * e⁻¹ = atlasA := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp
      (commutingConjugateSubgroup_le (hedge s hs x)), mul_inv_cancel_right]
  calc
    conjugateAt (inclusion s x) =
        pointTransport (inclusion s x) * (e * atlasA * e⁻¹) *
          (pointTransport (inclusion s x))⁻¹ := by rw [hc]; rfl
    _ = s * conjugateAt x * s⁻¹ := by
      simp only [e, conjugateAt, mul_inv_rev, inv_inv, mul_assoc,
        mul_inv_cancel_left, mul_inv_cancel, mul_one]

theorem conjugateAt_equivariant_of_generators
    (hroot : ∀ s ∈ atlasGenerators, ∀ x,
      conjugateAt (inclusion s x) = s * conjugateAt x * s⁻¹)
    (g : Carrier) (x : Fin 3510) :
    conjugateAt (inclusion g x) = g * conjugateAt x * g⁻¹ :=
  Theory.GroupAction.SchreierActionCertificate.conjugation_equivariant_of_generators
    inclusion atlasGenerators atlasGenerators_closure conjugateAt hroot g x

theorem conjugateAt_injective_of_fiber
    (hfiber : ∀ x, conjugateAt x = atlasA → x = rootBase)
    (hroot : ∀ s ∈ atlasGenerators, ∀ x,
      conjugateAt (inclusion s x) = s * conjugateAt x * s⁻¹) :
    Function.Injective conjugateAt := by
  intro x y hxy
  have hx : conjugateAt (inclusion (pointTransport x)⁻¹ x) = atlasA := by
    rw [conjugateAt_equivariant_of_generators hroot]
    simp only [conjugateAt, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one]
  have hy : conjugateAt (inclusion (pointTransport x)⁻¹ y) = atlasA := by
    rw [conjugateAt_equivariant_of_generators hroot, ← hxy]
    simp only [conjugateAt, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one]
  exact (inclusion (pointTransport x)⁻¹).injective
    ((hfiber _ hx).trans (hfiber _ hy).symm)

theorem conjugateAt_centralizes_of_equivariant
    (hroot : ∀ s ∈ atlasGenerators, ∀ x,
      conjugateAt (inclusion s x) = s * conjugateAt x * s⁻¹)
    (i : FixedPointsA) : conjugateAt i.val ∈ centralizerA := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have h := conjugateAt_equivariant_of_generators hroot atlasA i.val
  rw [i.property] at h
  exact eq_mul_inv_iff_mul_eq.mp h

theorem fixedPointRoot_range_of_fiber
    (hfiber : ∀ x, conjugateAt x = atlasA → x = rootBase)
    (hroot : ∀ s ∈ atlasGenerators, ∀ x,
      conjugateAt (inclusion s x) = s * conjugateAt x * s⁻¹)
    (hc : ∀ i : FixedPointsA, conjugateAt i.val ∈ centralizerA) :
    Set.range (fixedPointRoot hc) = commutingConjugates := by
  apply Set.Subset.antisymm
  · rintro t ⟨i, rfl⟩
    exact fixedPointRoot_mem hc i
  · intro t ht
    obtain ⟨g, hg⟩ := isConj_iff.mp ht
    have hx : conjugateAt (inclusion g rootBase) = t.val := by
      rw [conjugateAt_equivariant_of_generators hroot, conjugateAt_base, hg]
    have hfix : inclusion atlasA (inclusion g rootBase) = inclusion g rootBase := by
      apply conjugateAt_injective_of_fiber hfiber hroot
      rw [conjugateAt_equivariant_of_generators hroot, hx,
        ← Subgroup.mem_centralizer_singleton_iff.mp t.property, mul_inv_cancel_right]
    exact ⟨⟨inclusion g rootBase, hfix⟩, Subtype.ext hx⟩

end Sporadic.Fischer.Fi22.TransvectionComparison
