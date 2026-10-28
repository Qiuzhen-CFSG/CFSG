module

public import Theory.AlgebraicGroup.Bor1.BorelHomogeneousSpace

/-!
# Conjugacy saturation and homogeneous-space fixed points

The union of conjugates of a closed subgroup is identified with the elements
fixing a point of its actual Plücker homogeneous space. The conventions are
left translation on `G / H` and membership tested by `g⁻¹ * x * g ∈ H`.
The construction works for every closed subgroup; no Borel hypothesis or
completeness is asserted here.

Source: Borel, *Linear Algebraic Groups*, §11.9,
`refs/KGroup/Bor1/Chapter4.tex`.
-/

namespace Theory.AlgebraicGroup.BorelElementCoverage

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- The union of the conjugates of a closed subgroup, on actual group points. -/
@[expose] public def conjugacySaturation (H : ClosedSubgroup G) : Set (Variety.Point G) :=
  {x | ∃ g : Variety.Point G, g⁻¹ * x * g ∈ H.toSubgroup}

omit [IsAlgClosed k] in
/-- Subgroup containment gives containment of conjugacy saturations. -/
public theorem conjugacySaturation_mono {H K : ClosedSubgroup G} (hHK : H ≤ K) :
    conjugacySaturation H ⊆ conjugacySaturation K := by
  rintro x ⟨g, hg⟩
  exact ⟨g, hHK hg⟩

omit [IsAlgClosed k] in
/-- Conjugate subgroups have the same conjugacy saturation. -/
public theorem conjugacySaturation_conjugate (H : ClosedSubgroup G) (t : Variety.Point G) :
    conjugacySaturation (H.conjugate t) = conjugacySaturation H := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g * t, ?_⟩
    have h := (H.mem_conjugate_iff t _).mp hg
    simpa only [mul_inv_rev, mul_assoc] using h
  · rintro ⟨g, hg⟩
    refine ⟨g * t⁻¹, (H.mem_conjugate_iff t _).mpr ?_⟩
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel_right, inv_mul_cancel, mul_one] using hg

/-- An element lies in a conjugate precisely when it fixes a point of the actual Plücker homogeneous space. -/
public theorem mem_conjugacySaturation_iff_homogeneousSpace_fixed
    (H : ClosedSubgroup G) (x : Variety.Point G) :
    x ∈ conjugacySaturation H ↔
      ∃ q : Bor1.borelHomogeneousSpace H, x • q = q := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨Bor1.borelHomogeneousSpace.projection H g, ?_⟩
    apply Subtype.ext
    exact (Bor1.projectivization_fixed_iff_mem_conjugate H g x).mpr
      ((H.mem_conjugate_iff g x).mpr hg)
  · rintro ⟨q, hq⟩
    obtain ⟨g, rfl⟩ := Bor1.borelHomogeneousSpace.projection_surjective H q
    exact ⟨g, (H.mem_conjugate_iff g x).mp
      ((Bor1.projectivization_fixed_iff_mem_conjugate H g x).mp
        (congrArg Subtype.val hq))⟩

end Theory.AlgebraicGroup.BorelElementCoverage
