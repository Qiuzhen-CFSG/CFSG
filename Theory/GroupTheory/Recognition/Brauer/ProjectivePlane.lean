module
public import Theory.GroupTheory.Recognition.Brauer.CommonPointTransfer
public import Theory.GroupTheory.Recognition.Brauer.PlaneCounts
public import Theory.Combinatorics.RegularConfiguration
public import Theory.Combinatorics.RegularConfigurationConfig

/-!
# Brauer's projective plane

The actual conjugates of `jM` and `jMstar`, with disjointness as incidence,
form a projective plane under Brauer's five original postulates. This is
Brauer, *On finite Desarguesian planes I*, Theorem (3B), pp. 121-122.
The construction supplies Mathlib's `Configuration.ProjectivePlane` on
the original point and line types, retaining their membership instance.

The exact counts (3A) and `q > 1` leave a point off any two lines. The
postulate (V) transfer then gives a common incident point, proving (3B)(a).
Counting incident pairs gives intersection uniqueness and nondegeneracy
via `nondegenerate_of_regular_counts`, the source's step (b). Mathlib's
`HasPoints.hasLines` uses equal finite point and line counts to give the
dual existence assertion of (c). Finally, `exists_config_of_regular_counts`
supplies the required nondegenerate configuration by finite counting,
as in (d). No projective-plane axiom is assumed in any of these inputs.
-/

namespace Theory.GroupTheory.BrauerPlaneData

/-- Brauer I (3B): the original involution geometry is a projective plane. -/
@[instance_reducible] public noncomputable def projectivePlane
    {G : Type*} [Group G] [Finite G] (D : BrauerPlaneData G) :
    Configuration.ProjectivePlane D.Point D.Line := by
  classical
  obtain ⟨hq, hP, hL, hpoints', hlines'⟩ := D.plane_counts
  have hpoints (l : D.Line) : Configuration.pointCount D.Point l = D.q + 1 := hpoints' l
  have hlines (p : D.Point) : Configuration.lineCount D.Line p = D.q + 1 := hlines' p
  let : Fintype D.Point := Fintype.ofFinite _
  let : Fintype D.Line := Fintype.ofFinite _
  have hinter (l1 l2 : D.Line) (_hne : l1 ≠ l2) :
      ∃ p : D.Point, p ∈ l1 ∧ p ∈ l2 := by
    have hoff : ∃ p : D.Point, p ∉ l1 ∧ p ∉ l2 := by
      by_contra h
      have hcover : ∀ p : D.Point, p ∈ l1 ∨ p ∈ l2 := by
        intro p
        by_contra hp
        exact h ⟨p, (not_or.mp hp).1, (not_or.mp hp).2⟩
      have heq : Nat.card {p : D.Point // p ∈ l1 ∨ p ∈ l2} = Nat.card D.Point :=
        Nat.card_congr (Equiv.subtypeUnivEquiv hcover)
      have hle : Nat.card D.Point ≤ Configuration.pointCount D.Point l1 +
          Configuration.pointCount D.Point l2 := by
        rw [← heq]
        simpa only [Configuration.pointCount, Nat.card_eq_fintype_card] using
          Fintype.card_subtype_or (fun p : D.Point => p ∈ l1) (fun p : D.Point => p ∈ l2)
      rw [hP, hpoints, hpoints] at hle
      nlinarith
    obtain ⟨p, h1, h2⟩ := hoff
    exact D.exists_common_point_of_nonincident p l1 l2 h1 h2
  letI : Configuration.Nondegenerate D.Point D.Line :=
    Configuration.nondegenerate_of_regular_counts D.q hq hP hL hpoints hlines hinter
  letI : Configuration.HasPoints D.Point D.Line :=
    { ‹Configuration.Nondegenerate D.Point D.Line› with
      mkPoint := fun {l1 l2} h => (hinter l1 l2 h).choose
      mkPoint_ax := fun {l1 l2} h => (hinter l1 l2 h).choose_spec }
  letI : Configuration.HasLines D.Point D.Line := Configuration.HasPoints.hasLines
    (by simpa only [Nat.card_eq_fintype_card] using hP.trans hL.symm)
  exact
    { ‹Configuration.HasPoints D.Point D.Line›,
      ‹Configuration.HasLines D.Point D.Line› with
      exists_config := Configuration.exists_config_of_regular_counts D.q hq hP hpoints hlines }

end Theory.GroupTheory.BrauerPlaneData
