module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Saturated
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Splitting.Assembly
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Parabolics
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index
public import CFSG.Quasithin.ChapterI.Section04To05.A3Recognition
public import Theory.LinearAlgebra.BinaryFourAlternatingEight

/-!
# The nonnormal quaternion branch reduced to A₃ incidence geometry

The proved endpoint splitting and middle-normalizer theorems construct the
actual source configuration. Its point vertex has order 1344 and quotient
of order 168, so its two-core is nontrivial. The existing module reconstruction
then recognizes the generated subgroup once its actual coset incidence
geometry is supplied. The proved overgroup calculation gives A₈ or A₉.

Only the A₃ incidence geometry remains explicit in the final theorem; the
intersection, saturation, splitting, middle, parabolic and index premises
are all discharged. This is a conditional reduction, not completed I.4.6.
Source: Aschbacher, “A 2-local characterization of M12”, Lemmas 3.1–3.2
and Proposition 3.3; Aschbacher–Smith I.4.6 and I.5.1, pp.417,419.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition
open Quasithin.I5
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Both endpoint complements and the middle data are already constructed in
the existing source modules. This assembles them without an extra premise. -/
theorem source_configuration {z g : G} (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hs : ¬ FusionSaturated z g) : Nonempty (A3Configuration z g) := by
  apply Configuration.exists_configuration_of_middle h hn (intersectionData h hn) hgQ hg hs
  intro y hyQ hy hinter hsplit
  exact Configuration.middle_of_point_split h (intersectionData h hn g hgQ hg)
    (intersectionData h hn y hyQ hy) hinter hsplit

/-- The original point vertex has order 1344, so its two-core is nontrivial.
The order-168 quotient alone would not imply this. -/
theorem configuration_point_core_ne_bot {z g : G} (h : Hypotheses z)
    (d : IntersectionData z g) (c : A3Configuration z g)
    (dy : IntersectionData z c.y) (p : A3ParabolicData z g c.y c.A) :
    (configuration_system h d c dy p).Q 0 ≠ ⊥ := by
  let S := configuration_system h d c dy p
  have hc : Nat.card (S.family 0) = 1344 := by
    dsimp only [S]
    rw [configuration_system_family]
    exact (Nat.card_congr (subgroupOfEquivOfLe
      (show normalizer (coreIntersection z g : Set G) ≤ geometryGroup z g c.y
        from le_sup_left)).toEquiv).trans (intersection_normalizer_card d)
  obtain ⟨e⟩ := S.point_A3 rfl
  have hq : Nat.card (S.family 0 ⧸ pCore 2 (S.family 0)) = 168 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  intro hzero
  have hz : pCore 2 (S.family 0) = ⊥ :=
    (map_eq_bot_iff_of_injective _ (S.family 0).subtype_injective).mp hzero
  have hm := card_eq_card_quotient_mul_card_subgroup (pCore 2 (S.family 0))
  rw [hc, hq, hz, card_bot] at hm
  norm_num at hm

/-- Every nonnormal-quaternion source step except the A₃ incidence geometry
is discharged here. This is explicitly a conditional recognition theorem. -/
theorem nonnormal_recognition_of_geometry {z : G} (h : Hypotheses z)
    (hn : QuaternionSubgroupsNonnormal z)
    (geometry : ∀ (M : Subgroup G) (S : DSystem .A3 M), S.Q 0 ≠ ⊥ →
      Nonempty (A3Recognition.GeometryData S)) :
    ElementaryEightAlternative G ∨ Nonempty (G ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 9)) := by
  obtain ⟨g, hgQ, hg⟩ := h.fused
  have d := intersectionData h hn g hgQ hg
  by_cases hs : FusionSaturated z g
  · exact Or.inl (d.elementaryEight_of_normalizer_eq_top (hs.normalizer_eq_top h d))
  · obtain ⟨c⟩ := source_configuration h hn hgQ hg hs
    have dy := intersectionData h hn c.y c.conjugate_mem c.conjugate_ne
    let p := configuration_parabolics h d c dy
    let S := configuration_system h d c dy p
    have hQ : S.Q 0 ≠ ⊥ := configuration_point_core_ne_bot h d c dy p
    obtain ⟨a⟩ := geometry (geometryGroup z g c.y) S hQ
    let e := (A3Recognition.equivPSL4_of_geometry a hQ).trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
    exact Or.inr (alternating_eight_or_nine_of_source h hn (intersectionData h hn)
      (configuration_fusion_card h d c dy) (geometryGroup z g c.y) e
      (geometry_centralizer_le d c.y))

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
