module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.Displacement

/-!
# The original critical-index alternative

For every critical path in the original symplectic graph, the first critical
image is either at least the square of the field size or both reciprocal
critical indices are exactly the field size.  This is the literal numerical
split used at the opening of MS93 (3.7): the lower bound on both indices is
the original full-cover bound, while the small branch is the already proved
original critical-image calculation.  The final theorem applies the split to
the actual path through the marked beta vertex.

No characteristic-minimum replacement, saturation, or quotient re-marking is
introduced here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

theorem Input.original_critical_index_alternative
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R) :
    Nat.card F ^ 2 ≤ (Q R z).relIndex (Z R a) ∨
      ((Q R z).relIndex (Z R a) = Nat.card F ∧
        (Q R a).relIndex (Z R z) = Nat.card F) := by
  by_cases hlarge : Nat.card F ^ 2 ≤ (Q R z).relIndex (Z R a)
  · exact Or.inl hlarge
  · right
    exact h.original_small_critical_indices_eq_field path hb (by omega)

/-- The alternative on the source critical path through the marked beta vertex. -/
theorem Input.exists_original_critical_index_alternative
    (geometry : Geometry R) (hb : 0 < geometry.b R) :
    ∃ z : Vertex R, ∃ path : CriticalPath R geometry (alpha R) z,
      path.walk.getVert 1 = beta R ∧
        (Nat.card F ^ 2 ≤ (Q R z).relIndex (Z R (alpha R)) ∨
          ((Q R z).relIndex (Z R (alpha R)) = Nat.card F ∧
            (Q R (alpha R)).relIndex (Z R z) = Nat.card F)) := by
  obtain ⟨z, path, hfirst⟩ := exists_original_critical_path_through_beta geometry hb
  exact ⟨z, path, hfirst,
    h.original_critical_index_alternative path hb⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
