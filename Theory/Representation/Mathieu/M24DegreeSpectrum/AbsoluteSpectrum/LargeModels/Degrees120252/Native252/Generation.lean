module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native
public import Theory.Mathieu.LargeInvolutionGeneration.Certificates24

/-!
# Generation by the literal degree-252 native actors

The checked four-involution words recover the native point-stabilizer
generators. For their second row, the representative is generator A and
every conjugator is a word in A, B and B⁻¹. Thus both standard actors
generate the actual Witt-design automorphism group.

This supplies the all-elements invariance step for the sextet module.
Source: the native certificates in `LargeInvolutionGeneration`, accompanying
Guralnick–Malle I, Proposition 5.1; James, J. Algebra 27 (1973), 57–111.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252
open Sporadic.Mathieu Sporadic.Mathieu.LargeInvolutionGeneration

private theorem letter_mem (H : Subgroup M24) (hactor : ∀ j, actor j ∈ H)
    (j : Fin 3) : letter24 j ∈ H := by
  fin_cases j
  · exact hactor 0
  · exact hactor 1
  · exact H.inv_mem (hactor 1)

private theorem representative_eq_actor : representative24 1 = actor 0 := by
  simp only [representative24, actor, Matrix.cons_val_one, Matrix.cons_val_zero,
    Sporadic.Mathieu.M24InvolutionCentralizers.involution2B, m24Involution2B]

private theorem word_mem {G : Type*} [Group G] (H : Subgroup G)
    {n : ℕ} (f : Fin n → G) (hf : ∀ j, f j ∈ H)
    (w : List (Fin n)) : evalWord f w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons j w ih => exact H.mul_mem (hf j) ih

private theorem conjugate_mem (H : Subgroup M24) (hactor : ∀ j, actor j ∈ H)
    (i : Fin 4) : conjugate24 1 i ∈ H := by
  have hc : conjugator24 1 i ∈ H := word_mem H letter24 (letter_mem H hactor) _
  change conjugator24 1 i * representative24 1 * (conjugator24 1 i)⁻¹ ∈ H
  rw [representative_eq_actor]
  exact H.mul_mem (H.mul_mem hc (hactor 0)) (H.inv_mem hc)

/-- The two specified native generators generate all of the native carrier. -/
theorem actors_closure_eq_top : Subgroup.closure (Set.range actor) = ⊤ := by
  let H := Subgroup.closure (Set.range actor)
  have hactor (j : Fin 2) : actor j ∈ H := Subgroup.subset_closure ⟨j, rfl⟩
  have htarget (i : Fin 4) : target24 i ∈ H := by
    rw [← generation24 1 i]
    exact word_mem H _ (conjugate_mem H hactor) _
  exact m24_eq_top_of_generators H (htarget 0) (htarget 1) (htarget 2) (hactor 0)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252
