module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.PointResidual
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global

/-!
# The corank consequence of line intersections

An escaping centralizer forces its subgroup into a line intersection.
Monotonicity of relative index bounds its binary codimension from below by
the codimension of a field line. Taking the infimum gives the actual E.3
parameter r(G,V), including the empty-family value infinity.
Source: Aschbacher--Smith, 11.5.3(2), printed p.779.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
open Subgroup ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The source corank bound from the literal intersection assertion.
For the natural modules the line codimension is 2n or 3n. -/
theorem globalR_ge_of_line_intersections (L V V₁ : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g : G →* G) ≤
        V₁.map (MulAut.conj l : G →* G)) :
    (subgroupCorank V V₁ : ℕ∞) ≤ globalR V := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hAV, hescape⟩
  have hb : subgroupCorank V V₁ ≤ subgroupCorank V A := by
    by_contra hn
    apply hescape
    apply centralizer_le_normalizer_of_line_intersections L V V₁ A hAV hbound
    intro l hl hA
    have hV : V.map (MulAut.conj l : G →* G) = V :=
      mem_normalizer_iff_map_conj_eq.mp (hLV hl)
    have hi := relIndex_map_map_of_injective (f := (MulAut.conj l : G →* G)) V₁ V (MulAut.conj l).injective
    rw [hV] at hi
    have hc : subgroupCorank V (V₁.map (MulAut.conj l : G →* G)) =
        subgroupCorank V V₁ := congrArg (Nat.log 2) hi
    have hle : subgroupCorank V (V₁.map (MulAut.conj l : G →* G)) ≤
        subgroupCorank V A :=
      Nat.log_mono_right (relIndex_le_of_le_left (L := V) hA (by
        change (A.subgroupOf V).index ≠ 0
        exact index_ne_zero_of_finite))
    exact hn (hc ▸ hle)
  exact_mod_cast hb

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
