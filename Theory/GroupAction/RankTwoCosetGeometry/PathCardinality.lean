module

public import Theory.GroupAction.RankTwoCosetCover.RootPathTransitivity
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# Rooted path transitivity from a literal stabilizer bound

Orbit–stabilizer turns an upper bound for one ordered path fixer into
transitivity when the full root order equals that bound times the number
of nonbacktracking paths. The intrinsic action on the subtype of such
paths retains the original pointwise vertex fixer.

Source application: the concrete binary unitary five-path action in
Aschbacher–Smith F.4.5–6, printed pp.275–277.
-/
@[expose] public noncomputable section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon

private theorem pretransitive_of_stabilizer_bound
    {H X : Type*} [Group H] [Finite H] [Finite X] [MulAction H X]
    (x : X) {d : ℕ} (hd : 0 < d)
    (hs : Nat.card (MulAction.stabilizer H x) ≤ d)
    (hc : Nat.card H = Nat.card X * d) : MulAction.IsPretransitive H X := by
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H x)
  rw [Nat.card_prod, hc] at he
  have ho : Nat.card X ≤ Nat.card (MulAction.orbit H x) := by
    have hm := Nat.mul_le_mul_left (Nat.card (MulAction.orbit H x)) hs
    rw [he] at hm
    exact Nat.le_of_mul_le_mul_right hm hd
  have hsur : Function.Surjective (Subtype.val : MulAction.orbit H x → X) :=
    (Subtype.val_injective.bijective_of_nat_card_le ho).2
  apply (MulAction.isPretransitive_iff_orbit_eq_univ (G := H) x).mpr
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨z, rfl⟩ := hsur y
  exact z.property

variable {G : Type*} [Group G] (F : Bool → Subgroup G)
variable {n : ℕ} {v : Vertex F}

theorem rootPathTransitive_of_pathStabilizer_card_le
    [Finite (stabilizer F v)] [Finite {p : BasedWalk (graph F) n v // p.Nonbacktracking}]
    (p : BasedWalk (graph F) n v) (hp : p.Nonbacktracking)
    {d : ℕ} (hd : 0 < d) (hfix : Nat.card (pathStabilizer F p) ≤ d)
    (hc : Nat.card (stabilizer F v) =
      Nat.card {q : BasedWalk (graph F) n v // q.Nonbacktracking} * d) :
    RootPathTransitive (graph F) G v n := by
  let P := {q : BasedWalk (graph F) n v // q.Nonbacktracking}
  let p' : P := ⟨p, hp⟩
  have hs : MulAction.stabilizer (stabilizer F v) p' =
      (pathStabilizer F p).subgroupOf (stabilizer F v) := by
    ext a
    change a • p' = p' ↔ a.val ∈ pathStabilizer F p
    exact Subtype.ext_iff.trans (mem_pathStabilizer_iff F p a).symm
  have hcard : Nat.card (MulAction.stabilizer (stabilizer F v) p') ≤ d := by
    rw [hs, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pathStabilizer_le F p)).toEquiv]
    exact hfix
  exact (rootPathTransitive_iff F n v).mpr
    (pretransitive_of_stabilizer_bound p' hd hcard hc)
end Subgroup.CosetGeometry.RankTwo
