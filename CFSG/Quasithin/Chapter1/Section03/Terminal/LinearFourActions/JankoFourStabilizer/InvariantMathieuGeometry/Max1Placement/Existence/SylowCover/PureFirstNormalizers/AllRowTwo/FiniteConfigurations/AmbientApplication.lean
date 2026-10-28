module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.HullTables
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.MarkedCoordinates
/-!
# Ambient all-row-two classification with one simultaneous conjugator

The strengthened marking theorem supplies both actual points and the marked
intersection using the original hypotheses. The complete census is applied
to that same conjugate of X. Conjugation preserves the entire eligible-sixteen
family and its join, so the resulting row, canonical hull and full normalizer
all use the same ambient conjugator. No enumeration or placement callback
appears in the conclusion. Whole-normalizer placement is a separate consumer.
Source: Kleidman--Wilson (1988), Corollary 1.2.2(a), Section 2.1, pp.488--489.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
open MarkedIntersection ElementaryNormalizerCover.PureTwoA.NativePair
attribute [local irreducible] modelGroup matrixA matrixB toMatrix
set_option Elab.async false

private theorem conjugation_cancel (A : Subgroup Model) (g : Model) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Model := by
    ext x
    simp [mul_assoc]
  rw [he,map_id]

private theorem family_conjugation (X Y : Subgroup Model) (g : Model)
    (hY : Y ∈ sixteenOvergroups X) :
    Y.map (MulAut.conj g).toMonoidHom ∈
      sixteenOvergroups (X.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hXY,hcard,hE,hp,hn⟩ := hY
  let := hE
  refine ⟨map_mono hXY,?_,IsElementaryAbelian.map _,?_,no_native_pair_map Y hn g⟩
  · rw [card_map_of_injective (MulAut.conj g).injective,hcard]
  · rintro y ⟨z,hz,rfl⟩ hy
    exact (hp z hz (fun he => hy (by simp [he]))).trans (isConj_iff.mpr ⟨g,rfl⟩)

theorem family_conjugation_iff (X Y : Subgroup Model) (g : Model) :
    Y ∈ sixteenOvergroups X ↔
      Y.map (MulAut.conj g).toMonoidHom ∈
        sixteenOvergroups (X.map (MulAut.conj g).toMonoidHom) := by
  constructor
  · exact family_conjugation X Y g
  · intro hY
    have hh := family_conjugation _ _ g⁻¹ hY
    simpa only [conjugation_cancel] using hh

private theorem hull_conjugation_le (X : Subgroup Model) (g : Model) :
    (sixteenHull X).map (MulAut.conj g).toMonoidHom ≤
      sixteenHull (X.map (MulAut.conj g).toMonoidHom) := by
  apply map_le_iff_le_comap.mpr
  refine sup_le (map_le_iff_le_comap.mp le_sup_left) (sSup_le ?_)
  intro Y hY
  apply map_le_iff_le_comap.mp
  exact le_sup_of_le_right (le_sSup (family_conjugation X Y g hY))

theorem hull_conjugation (X : Subgroup Model) (g : Model) :
    (sixteenHull X).map (MulAut.conj g).toMonoidHom =
      sixteenHull (X.map (MulAut.conj g).toMonoidHom) := by
  apply le_antisymm (hull_conjugation_le X g)
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom)
    (hull_conjugation_le (X.map (MulAut.conj g).toMonoidHom) g⁻¹)
  have hu (A : Subgroup Model) :
      (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
    simpa only [inv_inv] using conjugation_cancel A g⁻¹
  simpa only [conjugation_cancel,hu] using hh

/-- The complete ambient classification, retaining the same conjugator for
X, every eligible overgroup, the canonical hull, and the whole normalizer. -/
theorem conjugate_row_classification (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hc : 4 < Nat.card X) (hp : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hn : ¬ ∃ g : Model, nativePair.map (MulAut.conj g).toMonoidHom ≤ X) :
    ∃ (g : Model) (i : Fin 26),
      X.map (MulAut.conj g).toMonoidHom = row i ∧
      (∀ Y : Subgroup Model, Y ∈ sixteenOvergroups X ↔
        Y.map (MulAut.conj g).toMonoidHom ∈ sixteenOvergroups (row i)) ∧
      (sixteenHull X).map (MulAut.conj g).toMonoidHom = sixteenHull (row i) ∧
      (normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom =
        normalizer (row i : Set Model) := by
  obtain ⟨g,ht,hP,hM,_,_,_,hN⟩ :=
    simultaneous_marked_overgroup_coordinates_with_points X hc hp hn
  let : IsElementaryAbelian 2 (X.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  have hcg : 4 < Nat.card (X.map (MulAut.conj g).toMonoidHom) := by
    rwa [card_map_of_injective (MulAut.conj g).injective]
  have hpg : ∀ x ∈ X.map (MulAut.conj g).toMonoidHom, x ≠ 1 → IsConj a x := by
    rintro x ⟨z,hz,rfl⟩ hx
    exact (hp z hz (fun he => hx (by simp [he]))).trans (isConj_iff.mpr ⟨g,rfl⟩)
  obtain ⟨i,hi⟩ := marked_census _ hM ht hP hcg hpg (no_native_pair_map X hn g)
  refine ⟨g,i,hi,?_,?_,?_⟩
  · intro Y
    rw [← hi]
    exact family_conjugation_iff X Y g
  · rw [hull_conjugation,hi]
  · rwa [hi] at hN

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
