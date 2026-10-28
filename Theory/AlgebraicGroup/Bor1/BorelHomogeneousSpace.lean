module

public import Theory.AlgebraicGroup.Bor1.OrbitAction
public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation
public import Theory.AlgebraicGroup.Borel.Defs

universe u

/-!
The projective Pluecker model of a Borel homogeneous space.

For a closed subgroup `H`, the right-translation construction supplies a
nonzero exterior vector whose projective stabilizer is exactly `H`.  We use
that construction for a Borel subgroup `B`: the orbit of its Pluecker point is
the point-level model of `G / B`, with the action induced by the exterior
representation.  The projective variety and its completeness belong to the
non-affine geometry layer; this module keeps the carrier, action, base point,
and stabilizer/containment interfaces independent of that layer.  In
particular, no numbered Borel-conjugacy or maximal-torus theorem is used.

The final lemmas are the fixed-point bridge used in Bor1 11.1: a subgroup
fixing a point of the Pluecker orbit is contained in the corresponding
conjugate of `B`.
-/

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

open scoped ExteriorAlgebra LinearAlgebra.Projectivization

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {k : Type u} [Field k] [IsAlgClosed k]

section

variable {G : Variety k} [AlgebraicGroup G]

/-- The projective ambient space used for the Pluecker model of `G / B`. -/
public abbrev borelPluckerAmbient (B : ClosedSubgroup G) : Type u :=
  ℙ k (⋀[k]^B.rightTranslateVanishingTopWedgeData.degree
    B.rightTranslateVanishingSpan)

/-- The algebraic action of `G` on the Pluecker ambient space. -/
public noncomputable abbrev borelPluckerAction (B : ClosedSubgroup G) :
    MulAction (Variety.Point G) (borelPluckerAmbient B) :=
  MulAction.compHom _ B.rightTranslateVanishingExteriorGeneralLinear

public noncomputable instance borelPluckerAmbient.mulAction
    (B : ClosedSubgroup G) :
    MulAction (Variety.Point G) (borelPluckerAmbient B) :=
  borelPluckerAction B

/-- The point of the Pluecker ambient space represented by `B`. -/
@[expose]
public noncomputable def borelPluckerBasePoint (B : ClosedSubgroup G) :
    borelPluckerAmbient B :=
  B.rightTranslateVanishingPluckerPoint

/-- The point-level homogeneous space `G / B`, represented by the Pluecker
orbit of the base point. -/
public abbrev borelHomogeneousSpace (B : ClosedSubgroup G) : Type u :=
  {x : borelPluckerAmbient B //
    x ∈ Set.range (fun g : Variety.Point G => g • borelPluckerBasePoint B)}

/-- The induced action on the point-level homogeneous space. -/
public noncomputable instance borelHomogeneousSpace.mulAction
    (B : ClosedSubgroup G) :
    MulAction (Variety.Point G) (borelHomogeneousSpace B) := by
  letI : MulAction (Variety.Point G) (borelPluckerAmbient B) :=
    borelPluckerAction B
  have hmap (g : Variety.Point G) :
      Set.MapsTo (fun x => g • x)
        (Set.range (fun h : Variety.Point G => h • borelPluckerBasePoint B))
        (Set.range (fun h : Variety.Point G => h • borelPluckerBasePoint B)) := by
    rintro x ⟨h, rfl⟩
    exact ⟨g * h, mul_smul g h (borelPluckerBasePoint B)⟩
  exact
    { smul := fun g x => ⟨g • (x : borelPluckerAmbient B), hmap g x.property⟩
      one_smul := by
        intro x
        apply Subtype.ext
        exact one_smul (Variety.Point G) (x : borelPluckerAmbient B)
      mul_smul := by
        intro g h x
        apply Subtype.ext
        exact mul_smul g h (x : borelPluckerAmbient B) }

/-- The distinguished coset represented by the identity of `G`. -/
@[expose]
public noncomputable def borelHomogeneousSpace.basePoint
    (B : ClosedSubgroup G) : borelHomogeneousSpace B :=
  ⟨borelPluckerBasePoint B, ⟨1, by simp⟩⟩

/-- The orbit projection, at the level of rational points. -/
@[expose]
public noncomputable def borelHomogeneousSpace.projection
    (B : ClosedSubgroup G) : Variety.Point G → borelHomogeneousSpace B :=
  fun g => ⟨g • borelPluckerBasePoint B, ⟨g, rfl⟩⟩

public lemma borelHomogeneousSpace.projection_coe
    (B : ClosedSubgroup G) (g : Variety.Point G) :
    (borelHomogeneousSpace.projection B g : borelPluckerAmbient B) =
      g • borelPluckerBasePoint B := by
  change ((g • borelHomogeneousSpace.basePoint B :
    borelHomogeneousSpace B) : borelPluckerAmbient B) = _
  rfl

@[simp]
public lemma borelHomogeneousSpace.projection_one
    (B : ClosedSubgroup G) :
    borelHomogeneousSpace.projection B 1 = borelHomogeneousSpace.basePoint B := by
  apply Subtype.ext
  change (1 : Variety.Point G) • borelPluckerBasePoint B =
    borelPluckerBasePoint B
  simp

@[simp]
public lemma borelHomogeneousSpace.projection_mul
    (B : ClosedSubgroup G) (g h : Variety.Point G) :
    borelHomogeneousSpace.projection B (g * h) =
      g • borelHomogeneousSpace.projection B h := by
  apply Subtype.ext
  change (g * h) • borelPluckerBasePoint B =
    g • (h • borelPluckerBasePoint B)
  exact mul_smul g h (borelPluckerBasePoint B)

public lemma borelHomogeneousSpace.nonempty (B : ClosedSubgroup G) :
    Nonempty (borelHomogeneousSpace B) :=
  ⟨borelHomogeneousSpace.basePoint B⟩

public lemma borelHomogeneousSpace.projection_surjective (B : ClosedSubgroup G) :
    Function.Surjective (borelHomogeneousSpace.projection B) := by
  intro x
  obtain ⟨g, hg⟩ := x.property
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change g • (borelPluckerBasePoint B) = (x : borelPluckerAmbient B)
  exact hg

/-! The projection has the expected right-`B` fibres.  This is the concrete
quotient comparison used by closed-image arguments once a complete variety
structure is supplied. -/
public theorem borelHomogeneousSpace.projection_eq_iff
    (B : ClosedSubgroup G) (g h : Variety.Point G) :
    borelHomogeneousSpace.projection B g =
        borelHomogeneousSpace.projection B h ↔
      ∃ b : Variety.Point G, b ∈ B.toSubgroup ∧ h = g * b := by
  letI : MulAction (Variety.Point G) (borelPluckerAmbient B) :=
    borelPluckerAction B
  constructor
  · intro heq
    have hfix : (g⁻¹ * h) • borelPluckerBasePoint B =
        borelPluckerBasePoint B := by
      have hpoint : g • borelPluckerBasePoint B =
          h • borelPluckerBasePoint B := by
        exact congrArg (fun x : borelHomogeneousSpace B =>
          (x : borelPluckerAmbient B)) heq
      have hback := congrArg (fun q => g⁻¹ • q) hpoint
      simpa [smul_smul, mul_assoc] using hback.symm
    have hb' : g⁻¹ * h ∈
        MulAction.stabilizer (Variety.Point G) (borelPluckerBasePoint B) := hfix
    change g⁻¹ * h ∈ MulAction.stabilizer (Variety.Point G)
      B.rightTranslateVanishingPluckerPoint at hb'
    rw [chevalleyPluckerPoint_stabilizer B] at hb'
    have hb : g⁻¹ * h ∈ B.toSubgroup := hb'
    exact ⟨g⁻¹ * h, hb, by group⟩
  · rintro ⟨b, hb, rfl⟩
    apply Subtype.ext
    change g • borelPluckerBasePoint B =
      (g * b) • borelPluckerBasePoint B
    rw [mul_smul]
    have hfix : b • borelPluckerBasePoint B =
        borelPluckerBasePoint B := by
      have hb' : b ∈
          MulAction.stabilizer (Variety.Point G) (borelPluckerBasePoint B) := by
        change b ∈ MulAction.stabilizer (Variety.Point G)
          B.rightTranslateVanishingPluckerPoint
        rw [chevalleyPluckerPoint_stabilizer B]
        exact hb
      exact hb'
    rw [hfix]

/-- In the affine layer, completeness of the projective orbit is represented
by an explicit certificate.  The certificate is deliberately separate from
the point-level orbit data: proving that the orbit is a projective (hence
complete) variety requires the non-affine geometry layer. -/
public structure CompleteBorelHomogeneousSpace (B : ClosedSubgroup G) where
  isComplete : Prop
  complete : isComplete

public lemma CompleteBorelHomogeneousSpace.nonempty
    (B : ClosedSubgroup G) (_X : CompleteBorelHomogeneousSpace B) :
    Nonempty (borelHomogeneousSpace B) :=
  borelHomogeneousSpace.nonempty B

end

section

variable {G : Variety k} [AlgebraicGroup G]

/-- The point stabilizer of the distinguished Pluecker point is exactly `B`.
This is the quotient-kernel statement for the homogeneous-space model. -/
public lemma borelHomogeneousSpace.basePoint_stabilizer
    (B : ClosedSubgroup G) :
    MulAction.stabilizer (Variety.Point G) (borelPluckerBasePoint B) =
      B.toSubgroup := by
  letI : MulAction (Variety.Point G) (borelPluckerAmbient B) :=
    borelPluckerAction B
  exact chevalleyPluckerPoint_stabilizer B

/-! The pointwise form is convenient when the stabilizer is used as a fixed
projective point rather than as a subgroup. -/
public theorem closedSubgroup_chevalleyPluckerPoint_fixed_iff
    (B : ClosedSubgroup G) (g : Variety.Point G) :
    letI : MulAction (Variety.Point G) (borelPluckerAmbient B) :=
      borelPluckerAction B
    (g • borelPluckerBasePoint B = borelPluckerBasePoint B) ↔
      g ∈ B.toSubgroup := by
  letI : MulAction (Variety.Point G) (borelPluckerAmbient B) :=
    borelPluckerAction B
  change g ∈ MulAction.stabilizer (Variety.Point G)
      (borelPluckerBasePoint B) ↔ g ∈ B.toSubgroup
  rw [borelHomogeneousSpace.basePoint_stabilizer B]

/-- A subgroup fixes a translated Pluecker point exactly when it is contained
in the corresponding conjugate of `B`. -/
public theorem projectivization_fixed_iff_mem_conjugate
    (B : ClosedSubgroup G) (g s : Variety.Point G) :
    letI : MulAction (Variety.Point G) (borelPluckerAmbient B) :=
      borelPluckerAction B
    (s • (g • borelPluckerBasePoint B) =
      g • borelPluckerBasePoint B) ↔
      s ∈ (B.conjugate g).toSubgroup := by
  letI : MulAction (Variety.Point G) (borelPluckerAmbient B) :=
    borelPluckerAction B
  constructor
  · intro hfix
    have hback : (g⁻¹ * s * g) • borelPluckerBasePoint B =
        borelPluckerBasePoint B := by
      have h := congrArg (fun q => g⁻¹ • q) hfix
      simpa [smul_smul, mul_assoc] using h
    have hmem' : g⁻¹ * s * g ∈
        MulAction.stabilizer (Variety.Point G) (borelPluckerBasePoint B) := hback
    have hmem : g⁻¹ * s * g ∈ B.toSubgroup := by
      rw [borelHomogeneousSpace.basePoint_stabilizer B] at hmem'
      exact hmem'
    exact (ClosedSubgroup.mem_conjugate_iff B g s).mpr hmem
  · intro hmem
    have hback : g⁻¹ * s * g ∈ B.toSubgroup :=
      (ClosedSubgroup.mem_conjugate_iff B g s).mp hmem
    have hfix : (g⁻¹ * s * g) • borelPluckerBasePoint B =
        borelPluckerBasePoint B := by
      have hmem' : g⁻¹ * s * g ∈
          MulAction.stabilizer (Variety.Point G) (borelPluckerBasePoint B) := by
        rw [borelHomogeneousSpace.basePoint_stabilizer B]
        exact hback
      exact hmem'
    have hrewrite : s * g = g * (g⁻¹ * s * g) := by group
    calc
      s • (g • borelPluckerBasePoint B) =
          (s * g) • borelPluckerBasePoint B :=
        (mul_smul s g (borelPluckerBasePoint B)).symm
      _ = (g * (g⁻¹ * s * g)) • borelPluckerBasePoint B := by
        rw [hrewrite]
      _ = g • ((g⁻¹ * s * g) • borelPluckerBasePoint B) :=
        mul_smul g (g⁻¹ * s * g) (borelPluckerBasePoint B)
      _ = g • borelPluckerBasePoint B := by rw [hfix]

/-- Fixed-point containment for the Pluecker model. -/
public theorem subgroup_le_conjugate_of_borel_homogeneousSpace_fixed
    (B : ClosedSubgroup G) (S : Subgroup (Variety.Point G))
    (g : Variety.Point G)
    (hfix : ∀ s : Variety.Point G, s ∈ S →
      letI : MulAction (Variety.Point G) (borelPluckerAmbient B) :=
        borelPluckerAction B
      s • (g • borelPluckerBasePoint B) =
        g • borelPluckerBasePoint B) :
    S ≤ (B.conjugate g).toSubgroup := by
  intro s hs
  letI : MulAction (Variety.Point G) (borelPluckerAmbient B) :=
    borelPluckerAction B
  exact (projectivization_fixed_iff_mem_conjugate B g s).mp (hfix s hs)

/-! Compatibility spelling used by the original Bor1 proof. -/
public theorem subgroup_le_conjugate_of_projectivization_fixed
    (B : ClosedSubgroup G) (S : Subgroup (Variety.Point G))
    (g : Variety.Point G)
    (hfix : ∀ s : Variety.Point G, s ∈ S →
      letI : MulAction (Variety.Point G) (borelPluckerAmbient B) :=
        borelPluckerAction B
      s • (g • borelPluckerBasePoint B) =
        g • borelPluckerBasePoint B) :
    S ≤ (B.conjugate g).toSubgroup := by
  exact subgroup_le_conjugate_of_borel_homogeneousSpace_fixed B S g hfix

/-- The same fixed-point bridge phrased on the homogeneous-space carrier. -/
public theorem subgroup_le_conjugate_of_homogeneousSpace_fixed
    (B : ClosedSubgroup G) (S : Subgroup (Variety.Point G))
    (x : borelHomogeneousSpace B)
    (hfix : ∀ s : Variety.Point G, s ∈ S → s • x = x) :
    ∃ g : Variety.Point G, S ≤ (B.conjugate g).toSubgroup := by
  obtain ⟨g, hg⟩ := x.property
  refine ⟨g, ?_⟩
  intro s hs
  apply (projectivization_fixed_iff_mem_conjugate B g s).mp
  have h := hfix s hs
  apply congrArg (fun y : borelHomogeneousSpace B =>
    (y : borelPluckerAmbient B)) at h
  change s • (x : borelPluckerAmbient B) = (x : borelPluckerAmbient B) at h
  rw [← hg] at h
  exact h

end

end Theory.AlgebraicGroup.Bor1
