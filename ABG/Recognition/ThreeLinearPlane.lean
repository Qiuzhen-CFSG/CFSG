module
public import ABG.Recognition.ThreeLinearPermutationCharacter
public import ABG.Recognition.ThreeLinearFixedSetFibers

/-!
# Wong's projective plane from the linear-branch hypotheses

Lines are the thirteen cosets of the constructed subgroup `K`; points are
its distinct four-line fixed sets for order-three elements with centralizer
order 54. Conjugation transports these sets and preserves incidence.

For each defining element, a centralizing Sylow subgroup of order 27 acts
on the four fixed lines. Its kernel supplies at least eight defining elements
for the same point. The class has 104 elements, so there are at most thirteen
points. Double transitivity supplies a point on every pair of distinct lines;
counting pairs forces uniqueness. The resulting incidence relation is a
projective plane with four points on each line and four lines on each point.
This is a counting form of Wong's centralizer action argument, using the
proved permutation character and no assumed incidence postulates.

The shared fixed-set geometry is re-exported through `ThreeLinearFixedSetFibers`.
`exists_threeLinearPlane` derives the whole construction from the original
finite simple group, semidihedral Sylow-two, GL₂(3) involution-centralizer,
and order-5616 hypotheses.

Source: W. J. Wong, *On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2* (1964), Theorem 6(b), pp.110–111,
DOI: 10.1017/S1446788700022771.
-/

namespace ABG
noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- Each point element has a centralizing subgroup of order 27 and exponent three. -/
public theorem ThreeLinearLocalData.pointElement_subgroup
    (c : ThreeLinearLocalData G) (g : G) (hg : ThreeLinearPlane.IsPointElement G g) :
    ∃ P : Subgroup G, Nat.card P = 27 ∧
      P ≤ Subgroup.centralizer ({g} : Set G) ∧
      ∀ x : G, x ∈ P → x ≠ 1 → orderOf x = 3 := by
  obtain ⟨P, _, hcentral, _⟩ := Theory.GroupTheory.exists_normalized_sylow_three
    g hg.1 hg.2 c.sylow_three_card
  refine ⟨P, c.sylow_three_card P, hcentral, ?_⟩
  intro x hx hne
  have hp : x ^ 3 = 1 := by
    simpa only [c.sylow_three_exponent P] using Subgroup.pow_exponent_eq_one hx
  exact orderOf_eq_prime hp hne

namespace ThreeLinearPermutationData
variable (c : ThreeLinearPermutationData G) [IsSimpleGroup G]

/-- The actual four-line fixed sets form a projective plane with thirteen
points, four points per line, and four lines per point. -/
public theorem plane_and_counts :
    Nonempty (Configuration.ProjectivePlane
      (ThreeLinearPlane.Point G (G ⧸ c.subgroup))
      (ThreeLinearPlane.Line G (G ⧸ c.subgroup))) ∧
    Nat.card (ThreeLinearPlane.Point G (G ⧸ c.subgroup)) = 13 ∧
    (∀ l : ThreeLinearPlane.Line G (G ⧸ c.subgroup),
      Configuration.pointCount (ThreeLinearPlane.Point G (G ⧸ c.subgroup)) l = 4) ∧
    (∀ p : ThreeLinearPlane.Point G (G ⧸ c.subgroup),
      Configuration.lineCount (ThreeLinearPlane.Line G (G ⧸ c.subgroup)) p = 4) := by
  let := c.two_pretransitive
  exact ThreeLinearPlane.plane_and_counts_of_fibers G (G ⧸ c.subgroup)
    c.coset_card c.eligible_card c.fixedPoint_count_pointElement
    (ThreeLinearPlane.eight_le_card_pointOf_fiber G (G ⧸ c.subgroup)
      c.fixedPoint_count_pointElement c.fixedPoint_count_other_order_three
      c.toThreeLinearLocalData.pointElement_subgroup)

/-- The projective plane structure on the actual fixed-set incidence relation. -/
@[instance_reducible] public noncomputable def projectivePlane : Configuration.ProjectivePlane
    (ThreeLinearPlane.Point G (G ⧸ c.subgroup))
    (ThreeLinearPlane.Line G (G ⧸ c.subgroup)) :=
  Classical.choice c.plane_and_counts.1

/-- Every two distinct coset lines belong to exactly one fixed-set point. -/
public theorem existsUnique_point (l m : ThreeLinearPlane.Line G (G ⧸ c.subgroup))
    (hne : l ≠ m) : ∃! p : ThreeLinearPlane.Point G (G ⧸ c.subgroup), p ∈ l ∧ p ∈ m := by
  let := c.projectivePlane
  exact Configuration.HasPoints.existsUnique_point
    (ThreeLinearPlane.Point G (G ⧸ c.subgroup))
    (ThreeLinearPlane.Line G (G ⧸ c.subgroup)) l m hne

/-- There are thirteen distinct fixed-set points. -/
public theorem plane_card_points :
    Nat.card (ThreeLinearPlane.Point G (G ⧸ c.subgroup)) = 13 := c.plane_and_counts.2.1

/-- Each coset line contains four fixed-set points. -/
public theorem plane_pointCount (l : ThreeLinearPlane.Line G (G ⧸ c.subgroup)) :
    Configuration.pointCount (ThreeLinearPlane.Point G (G ⧸ c.subgroup)) l = 4 :=
  c.plane_and_counts.2.2.1 l

/-- Each fixed-set point lies on four coset lines. -/
public theorem plane_lineCount (p : ThreeLinearPlane.Point G (G ⧸ c.subgroup)) :
    Configuration.lineCount (ThreeLinearPlane.Line G (G ⧸ c.subgroup)) p = 4 :=
  c.plane_and_counts.2.2.2 p

/-- The inherited action on the plane's tagged lines is faithful. -/
public theorem plane_faithful :
    FaithfulSMul G (ThreeLinearPlane.Line G (G ⧸ c.subgroup)) := c.faithful

end ThreeLinearPermutationData

/-- Wong's original linear-branch hypotheses construct the actual projective
plane and faithful collineation action on thirteen coset lines. -/
public theorem exists_threeLinearPlane [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 → Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (hG : Nat.card G = 5616) :
    ∃ c : ThreeLinearPermutationData G,
      Nonempty (Configuration.ProjectivePlane
        (ThreeLinearPlane.Point G (G ⧸ c.subgroup))
        (ThreeLinearPlane.Line G (G ⧸ c.subgroup))) ∧
      FaithfulSMul G (ThreeLinearPlane.Line G (G ⧸ c.subgroup)) ∧
      Configuration.IsCollineationAction G
        (ThreeLinearPlane.Point G (G ⧸ c.subgroup))
        (ThreeLinearPlane.Line G (G ⧸ c.subgroup)) ∧
      Nat.card (ThreeLinearPlane.Line G (G ⧸ c.subgroup)) = 13 ∧
      Nat.card (ThreeLinearPlane.Point G (G ⧸ c.subgroup)) = 13 ∧
      (∀ l : ThreeLinearPlane.Line G (G ⧸ c.subgroup),
        Configuration.pointCount (ThreeLinearPlane.Point G (G ⧸ c.subgroup)) l = 4) ∧
      (∀ p : ThreeLinearPlane.Point G (G ⧸ c.subgroup),
        Configuration.lineCount (ThreeLinearPlane.Line G (G ⧸ c.subgroup)) p = 4) := by
  obtain ⟨c⟩ := exists_threeLinearPermutationData S hS hcard hC hG
  exact ⟨c, c.plane_and_counts.1, c.plane_faithful, inferInstance, c.coset_card,
    c.plane_card_points, c.plane_pointCount, c.plane_lineCount⟩

end
end ABG
