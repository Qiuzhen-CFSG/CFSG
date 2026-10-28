module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Setup
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Symmetry

/-!
# The three natural-action indices on the original subgroups

Fixed lifting retains the central layer of U. The full upper-root parameter
computes the Baumann action index, and inverse-conjugation symmetry gives
the same index for Uˣ. The projection to the actual natural plane computes
the remaining square index. Source: C.5.6 (*), printed p.156.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] {R L : Subgroup G} {F : Type*} [Field F]

structure ActionIndices (R L : Subgroup G) (x : G) (q : ℕ) : Prop where
  actor : (centralizer (U L : Set G)).relIndex (S R) = q
  conjugate : (centralizer (U L : Set G)).relIndex
    ((U L).map (MulAut.conj x⁻¹).toMonoidHom) = q
  module : (centralizer (L : Set G)).relIndex (U L) = q * q

/-- The square index counts the genuine natural quotient, without removing
its fixed central kernel. -/
theorem projection_index (c : ActionCoordinates R L F) :
    (centralizer (L : Set G)).relIndex (U L) = Nat.card F * Nat.card F := by
  have hk : (centralizer (L : Set G)).subgroupOf (U L) = c.projection.ker := by
    ext u
    exact (c.projection_kernel u).symm
  change ((centralizer (L : Set G)).subgroupOf (U L)).index = _
  rw [hk, index_ker, c.projection.range_eq_top_of_surjective c.projection_surjective,
    Nat.card_congr (topEquiv.toEquiv.trans Multiplicative.toAdd), Nat.card_fun,
    Nat.card_fin, pow_two]

/-- C.5.6 (*) on the actual module and original right conjugate. -/
theorem Setup.indices (h : Setup R L F) {x : G} (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    ActionIndices R L x (Nat.card F) := by
  refine ⟨actor_index h.coordinates, ?_, projection_index h.coordinates⟩
  rw [conjugate_index_eq_inverse]
  exact module_index_of_fixedLift h.coordinates h.fixedLift _
    (h.conjugate_le ((normalizer (R : Set G)).inv_mem hx))
    (inverse_not_centralizing _ _ hnc)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
