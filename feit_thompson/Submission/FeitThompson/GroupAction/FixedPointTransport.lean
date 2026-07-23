/-
Authors: Tianjiao Nie
-/

module

public import Submission.FeitThompson.GroupAction.Quotient

open scoped Pointwise

section FixedPointTransport

variable {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]

/-- Triviality on a subgroup is equivalent to subgroup containment in fixed points. -/
public theorem actsTriviallyOnSubgroup_iff_le_fixedPointSubgroup (H : Subgroup G) :
    ActsTriviallyOnSubgroup (A := A) (G := G) H ↔ H ≤ fixedPointSubgroup A G := by
  constructor
  · intro htriv x hx
    change ∀ a : A, a • x = x
    intro a
    exact htriv a x hx
  · intro hle a x hx
    have hxfix : x ∈ fixedPointSubgroup A G := hle hx
    have hxfix' : ∀ b : A, b • x = x := by
      simpa [fixedPointSubgroup] using hxfix
    exact hxfix' a

/-- A subgroup contained in fixed points is fixed pointwise. -/
public theorem actsTriviallyOnSubgroup_of_le_fixedPointSubgroup {H : Subgroup G}
    (hle : H ≤ fixedPointSubgroup A G) :
    ActsTriviallyOnSubgroup (A := A) (G := G) H :=
  (actsTriviallyOnSubgroup_iff_le_fixedPointSubgroup (A := A) (G := G) H).2 hle

/-- Pointwise triviality implies containment in fixed points. -/
public theorem le_fixedPointSubgroup_of_actsTriviallyOnSubgroup {H : Subgroup G}
    (htriv : ActsTriviallyOnSubgroup (A := A) (G := G) H) :
    H ≤ fixedPointSubgroup A G :=
  (actsTriviallyOnSubgroup_iff_le_fixedPointSubgroup (A := A) (G := G) H).1 htriv

/-- Triviality on a larger subgroup restricts to any smaller subgroup. -/
public theorem actsTriviallyOnSubgroup_mono {H K : Subgroup G} (hHK : H ≤ K)
    (htriv : ActsTriviallyOnSubgroup (A := A) (G := G) K) :
    ActsTriviallyOnSubgroup (A := A) (G := G) H := by
  intro a x hx
  exact htriv a x (hHK hx)

/-- If the action is trivial on `H` and on `K`, then it is trivial on `H ⊔ K`. -/
public theorem actsTriviallyOnSubgroup_sup {H K : Subgroup G}
    (hH : ActsTriviallyOnSubgroup (A := A) (G := G) H)
    (hK : ActsTriviallyOnSubgroup (A := A) (G := G) K) :
    ActsTriviallyOnSubgroup (A := A) (G := G) (H ⊔ K) := by
  have hHle : H ≤ fixedPointSubgroup A G :=
    le_fixedPointSubgroup_of_actsTriviallyOnSubgroup (A := A) (G := G) hH
  have hKle : K ≤ fixedPointSubgroup A G :=
    le_fixedPointSubgroup_of_actsTriviallyOnSubgroup (A := A) (G := G) hK
  exact
    actsTriviallyOnSubgroup_of_le_fixedPointSubgroup (A := A) (G := G)
      (sup_le hHle hKle)

/-- Pointwise triviality on `H ≤ G` descends to pointwise triviality on its image in `G ⧸ N`. -/
public theorem actsTriviallyOnSubgroup_map_quotient_of_actsTriviallyOnSubgroup
    (N H : Subgroup G) [N.Normal] (hNinv : IsInvariantSubgroup A G N)
    (htriv : ActsTriviallyOnSubgroup (A := A) (G := G) H) :
    letI : MulDistribMulAction A (G ⧸ N) :=
      quotientMulDistribMulAction (A := A) (G := G) N hNinv
    ActsTriviallyOnSubgroup (A := A) (G := G ⧸ N) (H.map (QuotientGroup.mk' N)) := by
  letI : MulDistribMulAction A (G ⧸ N) :=
    quotientMulDistribMulAction (A := A) (G := G) N hNinv
  letI : MulAction.QuotientAction A N := quotientAction_of_isInvariant (A := A) N hNinv
  intro a q hq
  rcases hq with ⟨g, hg, rfl⟩
  have hgfix : a • g = g := htriv a g hg
  calc
    a • ((g : G) : G ⧸ N) = ((a • g : G) : G ⧸ N) := by
      exact MulAction.Quotient.smul_coe (H := N) a g
    _ = ((g : G) : G ⧸ N) := by
      simp [hgfix]

end FixedPointTransport
