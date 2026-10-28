module
public import Theory.GroupAction.RankTwoCosetGeometry.FourPathMiddleKernel
public import Theory.GroupTheory.BinaryCentralCommutatorQuotient

/-!
# The middle core of a four-edge path

If the two cubic kernels each cut an index-two subgroup out of the middle
kernel, their intersection has relative index at most four. Equality with
the independently counted path fixer puts that entire fixer in the middle
kernel, as a normal subgroup of index four. Squaring into the second-ball
kernel then gives an elementary quotient of the path fixer.

Only the middle vertex stabilizer must be finite; the graph and the ambient
group may be infinite. The original cubic--quintic application supplies the
cardinality from four-path transitivity, not from an assumed model order.
Source: Aschbacher--Smith F.3.2--4 and F.7.3, pp.270,311--312;
14.2.20--21, pp.988--989.
-/

public section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- Two index-two restrictions attain the middle core's index-four bound. -/
theorem four_path_middle_core
    {a : Vertex F} (p : BasedWalk (graph F) 4 a) (hp : p.Nonbacktracking)
    [Finite (stabilizer F (p.2.1 : Vertex F))]
    (hb : Nat.card ((graph F).neighborSet (p.1 : Vertex F)) = 3)
    (hd : Nat.card ((graph F).neighborSet (p.2.2.1 : Vertex F)) = 3)
    (hib : (ballKernel F (p.1 : Vertex F) 1).relIndex
      (ballKernel F (p.2.1 : Vertex F) 1) ≤ 2)
    (hid : (ballKernel F (p.2.2.1 : Vertex F) 1).relIndex
      (ballKernel F (p.2.1 : Vertex F) 1) ≤ 2)
    (hc : Nat.card (ballKernel F (p.2.1 : Vertex F) 1) =
      4 * Nat.card (pathStabilizer F p)) :
    pathStabilizer F p ≤ ballKernel F (p.2.1 : Vertex F) 1 ∧
      ((pathStabilizer F p).subgroupOf (ballKernel F (p.2.1 : Vertex F) 1)).Normal ∧
      (pathStabilizer F p).relIndex (ballKernel F (p.2.1 : Vertex F) 1) = 4 := by
  let Q := ballKernel F (p.2.1 : Vertex F) 1
  let P := pathStabilizer F p
  have hPm : P ≤ stabilizer F (p.2.1 : Vertex F) := by
    intro g hg
    exact hg _ (by
      change (p.2.1 : Vertex F) ∈ a :: (p.1 : Vertex F) :: p.2.2.vertices
      simp only [List.mem_cons]
      exact Or.inr (Or.inr (origin_mem_vertices F p.2.2)))
  let : Finite P := Finite.of_injective (inclusion hPm) (inclusion_injective hPm)
  let : Finite Q := Finite.of_injective (inclusion (ballKernel_le_stabilizer F _ 1))
    (inclusion_injective _)
  let : Finite (Q ⊓ P : Subgroup G) :=
    Finite.of_injective (inclusion inf_le_left : (Q ⊓ P : Subgroup G) → Q)
      (inclusion_injective _)
  have hP : P = ballKernel F (p.1 : Vertex F) 1 ⊓
      ballKernel F (p.2.2.1 : Vertex F) 1 :=
    pathStabilizer_four_eq_cubic_kernels F p hp hb hd
  have hi : P.relIndex Q ≤ 4 := by
    rw [hP]
    exact relIndex_inf_le.trans (Nat.mul_le_mul hib hid)
  have hcount := ((Q ⊓ P).subgroupOf Q).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (show Q ⊓ P ≤ Q from inf_le_left)).toEquiv] at hcount
  change (Q ⊓ P).relIndex Q * Nat.card (Q ⊓ P : Subgroup G) = Nat.card Q at hcount
  rw [inf_relIndex_left] at hcount
  have he : Q ⊓ P = P := eq_of_le_of_card_ge inf_le_right (by
    change Nat.card Q = 4 * Nat.card P at hc
    nlinarith)
  have hPQ : P ≤ Q := he ▸ (inf_le_left : Q ⊓ P ≤ Q)
  refine ⟨hPQ, normal_subgroupOf_of_le_normalizer ?_, ?_⟩
  · change Q ≤ normalizer (P : Set G)
    rw [hP]
    apply (le_inf ?_ ?_).trans inf_normalizer_le_normalizer_inf
    · exact (ballKernel_one_le_edge F p.2.1.property.symm).trans inf_le_right |>.trans
        (stabilizer_le_normalizer_ballKernel F _ 1)
    · exact (ballKernel_one_le_edge F p.2.2.1.property).trans inf_le_right |>.trans
        (stabilizer_le_normalizer_ballKernel F _ 1)
  · rw [he] at hcount
    have hp0 : 0 < Nat.card P := Nat.card_pos
    change Nat.card Q = 4 * Nat.card P at hc
    nlinarith

/-- Squaring in the middle core induces an elementary quotient of the path fixer. -/
theorem four_path_middle_quotient_elementary
    {a : Vertex F} (p : BasedWalk (graph F) 4 a)
    (hPQ : pathStabilizer F p ≤ ballKernel F (p.2.1 : Vertex F) 1)
    (hsq : ∀ x ∈ ballKernel F (p.2.1 : Vertex F) 1,
      x ^ 2 ∈ ballKernel F (p.2.1 : Vertex F) 2) :
    let hC := middle_ballKernel_normal_four_path_stabilizer F p
    let _ := hC
    IsElementaryAbelian 2 (pathStabilizer F p ⧸
      (ballKernel F (p.2.1 : Vertex F) 2).subgroupOf (pathStabilizer F p)) := by
  let hC := middle_ballKernel_normal_four_path_stabilizer F p
  let _ := hC
  let C := (ballKernel F (p.2.1 : Vertex F) 2).subgroupOf (pathStabilizer F p)
  have hsquare : ∀ x : pathStabilizer F p ⧸ C, x ^ 2 = 1 := by
    intro x
    obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective C x
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hsq q (hPQ q.property))
  exact {
    is_comm := ⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun a => orderOf_dvd_of_pow_eq_one (hsquare a)) x y).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }
end Subgroup.CosetGeometry.RankTwo
