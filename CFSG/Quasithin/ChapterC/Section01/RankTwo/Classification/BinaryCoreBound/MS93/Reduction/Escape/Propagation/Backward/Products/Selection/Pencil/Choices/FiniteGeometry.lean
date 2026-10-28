module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Transvections

/-!
# Generating plane translates in the literal binary matrix model

For an order-four plane A and a two-element matrix subgroup H with fixed
plane of order four, mark A and the fixed plane by matrices a and k.
Conjugating H by k⁻¹ places it in the standard plane's shear fixer. The
coordinate construction supplies two moved planes with different intersection
lines. Transporting back gives the actual matrices `k * cᵢ * a⁻¹` and
`k * cⱼ * a⁻¹`; normalizers of their pointwise fixers generate with H.

`Planes` also proves fixer order four, equality of its normalizer with the
setwise plane stabilizer, and maximality of that stabilizer for every A.
These are the finite-model inputs to the relative-normalizer choices of
Meierfrankenfeld--Stellmacher (1993), (4.3.7)(i), printed p.887, with the
relative-normalizer convention on p.881. The two-vertex source assembly is
owned by the consuming Choices development.
-/

@[expose] public section

open Matrix Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry

theorem conjugate_cancel (g : SL) (H : Subgroup SL) :
    conjugate g (conjugate g⁻¹ H) = H := by
  simp only [conjugate, Subgroup.map_map]
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id SL := by
    ext t
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, Subgroup.map_id]

theorem generate_conjugate (g : SL) (B : Subgroup Space) (K : Subgroup SL)
    (h : planeStabilizer B ⊔ K = ⊤) :
    planeStabilizer (move g B) ⊔ conjugate g K = ⊤ := by
  rw [planeStabilizer_move]
  change (planeStabilizer B).map (MulAut.conj g).toMonoidHom ⊔
    K.map (MulAut.conj g).toMonoidHom = ⊤
  rw [← Subgroup.map_sup, h, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

/-- Two actual matrix translates generate with H and meet its fixed plane differently. -/
theorem exists_generating_plane_translates (A : Subgroup Space) (hA : Nat.card A = 4)
    (H : Subgroup SL) (hH : Nat.card H = 2) (hfixed : Nat.card (fixedSpace H) = 4) :
    ∃ g h : SL,
      normalizer (planeFixer (A.map (modelAction g).toMonoidHom) : Set SL) ⊔ H = ⊤ ∧
      normalizer (planeFixer (A.map (modelAction h).toMonoidHom) : Set SL) ⊔ H = ⊤ ∧
      A.map (modelAction g).toMonoidHom ⊓ fixedSpace H ≠
        A.map (modelAction h).toMonoidHom ⊓ fixedSpace H := by
  obtain ⟨a, ha⟩ := plane_transitive A hA
  obtain ⟨k, hk⟩ := plane_transitive (fixedSpace H) hfixed
  let K := conjugate k⁻¹ H
  have hK : Nat.card K = 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hH]
  have hKfix : fixedSpace K = standardPlane := by
    change fixedSpace (conjugate k⁻¹ H) = standardPlane
    rw [fixedSpace_conjugate, ← hk, move_cancel]
  obtain ⟨i, j, hi, hj, hij⟩ := standard_choices K hK hKfix
  have hmove (r : Fin 3) : move (k * crossActor r * a⁻¹) A =
      move k (move (crossActor r) standardPlane) := by
    rw [← ha, ← move_mul, move_cancel, ← move_mul]
  have hback : conjugate k K = H := conjugate_cancel k H
  have hgen (r : Fin 3) (hr : planeStabilizer (move (crossActor r) standardPlane) ⊔ K = ⊤) :
      normalizer (planeFixer (move (k * crossActor r * a⁻¹) A) : Set SL) ⊔ H = ⊤ := by
    rw [planeFixer_normalizer _ (by rw [move_card, hA]), hmove]
    have hh := generate_conjugate k _ K hr
    rwa [hback] at hh
  refine ⟨k * crossActor i * a⁻¹, k * crossActor j * a⁻¹, hgen i hi, hgen j hj, ?_⟩
  change move (k * crossActor i * a⁻¹) A ⊓ fixedSpace H ≠
    move (k * crossActor j * a⁻¹) A ⊓ fixedSpace H
  rw [hmove, hmove, ← hk]
  intro he
  apply hij
  apply Subgroup.map_injective (f := (modelAction k).toMonoidHom) (modelAction k).injective
  rw [Subgroup.map_inf _ _ (modelAction k).toMonoidHom (modelAction k).injective,
    Subgroup.map_inf _ _ (modelAction k).toMonoidHom (modelAction k).injective]
  exact he

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry
