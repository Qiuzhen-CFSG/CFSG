module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Inputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.NormalizerJoins.Maximality
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.NormalizerJoins.CommonSylow
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.NormalizerJoins.LocalCubics

/-!
# Characteristic-five centralizer and normalizer generation

The two actual centralizers generate the inner model and intersect in the
common Sylow two-subgroup. Each side has an element of order three normalizing
both of its marked small and large subgroups. Such an element lies outside
the opposite centralizer, whose maximality proves the two normalizer joins.

Thus every actual frame satisfies all five generation identities. Quadratic
field descent supplies a frame, giving the existential used by the independent
fusion and invariant-family assembly. All normalizers are taken in the actual
inner model, with the frame's prescribed projection and comparison.

Source: Aschbacher--Smith E.1.14(6), printed p.214 (Asc82a, Lemma 4.10).
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}
variable (c : Geometry.Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)
include hF hσ
variable [Finite (innerModel F σ)]

/-- An order-three local normalizer element suffices for the join with the
opposite centralizer, provided the centralizer intersection is the Sylow. -/
theorem opposite_sup_normalizer_eq_top_of_cubic
    (hinter : c.centralizerAt false ⊓ c.centralizerAt true = (c.T : Subgroup _))
    (i : Bool) (A : Subgroup (innerModel F σ))
    (x : innerModel F σ) (hxC : x ∈ c.centralizerAt i)
    (hxN : x ∈ normalizer (A : Set (innerModel F σ))) (hx : orderOf x = 3) :
    c.centralizerAt (!i) ⊔ normalizer (A : Set (innerModel F σ)) = ⊤ := by
  apply ((c.centralizer_isCoatom hF hσ (!i)).ne_iff_eq_top le_sup_left).mp
  intro heq
  have hxD : x ∈ c.centralizerAt (!i) :=
    (le_sup_right : normalizer (A : Set (innerModel F σ)) ≤
      c.centralizerAt (!i) ⊔ normalizer (A : Set (innerModel F σ))) hxN |>
      (fun h => heq ▸ h)
  have hxT : x ∈ (c.T : Subgroup (innerModel F σ)) := by
    rw [← hinter]
    cases i
    · exact ⟨hxC, hxD⟩
    · exact ⟨hxD, hxC⟩
  have hcop := c.T.isPGroup'.orderOf_coprime (by decide : Nat.Coprime 2 3)
    (⟨x, hxT⟩ : c.T)
  rw [Subgroup.orderOf_mk, hx] at hcop
  norm_num at hcop

/-- The actual intersection and local normalizer cubics discharge all five
fields of `Generation`. Neither premise asserts a generation identity. -/
theorem generation_of_intersection_and_local_cubics
    (hinter : c.centralizerAt false ⊓ c.centralizerAt true = (c.T : Subgroup _))
    (hcubic : ∀ i : Bool, ∃ x : innerModel F σ,
      x ∈ c.centralizerAt i ∧
      x ∈ normalizer (c.small hF hσ i : Set (innerModel F σ)) ∧
      x ∈ normalizer (c.large hF hσ i : Set (innerModel F σ)) ∧ orderOf x = 3) :
    c.Generation hF hσ where
  pair := c.centralizer_pair_eq_top hF hσ
  small i := by
    obtain ⟨x, hxC, hxS, _, hx⟩ := hcubic i
    exact c.opposite_sup_normalizer_eq_top_of_cubic hF hσ hinter i _ x hxC hxS hx
  large i := by
    obtain ⟨x, hxC, _, hxL, hx⟩ := hcubic i
    exact c.opposite_sup_normalizer_eq_top_of_cubic hF hσ hinter i _ x hxC hxL hx

/-- Every actual characteristic-five frame satisfies the five centralizer and
ambient-normalizer generation identities, with both model inputs discharged. -/
theorem generation : c.Generation hF hσ :=
  c.generation_of_intersection_and_local_cubics hF hσ
    (c.centralizer_intersection_eq_sylow hF hσ)
    (c.exists_local_normalizer_cubic hF hσ)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry

variable {F : Type*} [Field F] [Finite F]

/-- An actual common-Sylow frame with all five generating joins. This supplies
the generation input for the characteristic-five positioned geometry. -/
theorem exists_frame_generation (hF : Nat.card F = 5 ^ 2) (σ : F ≃+* F)
    (hσ : orderOf σ = 2) [Finite (innerModel F σ)] :
    ∃ c : Frame σ, c.Generation hF hσ := by
  obtain ⟨c⟩ := nonempty_frame hF σ hσ
  exact ⟨c, c.generation hF hσ⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry
