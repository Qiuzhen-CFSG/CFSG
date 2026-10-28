module
public import Theory.GroupTheory.PRadicalSylowNormalizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.LinearFiveRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.LinearFiveRows.Parabolics

/-!
# The arbitrary large-center radical rows in the native linear-five local

The literal native projection identifies the center with the exterior fixed
space and preserves the full normalizer quotient. A trivial image is F, with
quotient SL₅(2). A nontrivial radical image has a hyperplane-parabolic normalizer,
with quotient A₈. Conjugation retains the original subgroup, normalizer and
intrinsic core. The final exclusion is applied to both original chapter
configurations; it assumes neither a full ambient Sylow nor local maximality.

Source: An--O'Brien--Wilson (2003), Section 4 and Table 1, pp.122,124.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals.LinearFiveRows
open LinearFive
attribute [local irreducible] modelGroup matrixA matrixB

/-- Every placed large-center radical has one of the two actual simple quotients. -/
theorem radical_quotient (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer)
    (hlarge : 64 ≤ Nat.card (center P)) :
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      alternatingGroup (Fin 8)) := by
  rcases radical_quotient_or_nontrivial_image P hP hN hlarge with h | ⟨hi,hfixed,⟨e⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨e.trans (LinearFiveParabolics.radicalQuotientEquiv (image P) hi hfixed)⟩

/-- Every conjugate placement preserves the quotient of the entire normalizer. -/
theorem radical_quotient_of_conjugate (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hlarge : 64 ≤ Nat.card (center P)) (g : Model)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer.map (MulAut.conj g).toMonoidHom) :
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
      alternatingGroup (Fin 8)) := by
  let c := (MulAut.conj g).symm
  let Q := P.map c.toMonoidHom
  let a : normalizer (P : Set Model) ≃* normalizer (Q : Set Model) :=
    (c.subgroupMap _).trans (MulEquiv.subgroupCongr (map_equiv_normalizer_eq P c))
  have hQ := hP.map_equiv c
  have hlargeQ : 64 ≤ Nat.card (center Q) :=
    hlarge.trans_eq (Nat.card_congr (centerCongr (c.subgroupMap P)).toEquiv)
  have hQc : normalizer (Q : Set Model) ≤ fullNormalizer := by
    rw [← map_equiv_normalizer_eq P c]
    have hh := map_mono (f := c.toMonoidHom) hN
    have hi : c.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id Model := by
      ext x
      exact (MulAut.conj g).symm_apply_apply x
    simpa only [map_map,hi,map_id] using hh
  rcases radical_quotient Q hQ hQc hlargeQ with h | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨(MathieuRows.coreQuotientCongr a).trans e⟩
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨(MathieuRows.coreQuotientCongr a).trans e⟩

/-- The literal source quotient exclusions remove every conjugate linear-five
placement, without a maximal-two-local hypothesis. -/
theorem not_le_conjugate_of_quotients_excluded (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hlarge : 64 ≤ Nat.card (center P))
    (hq : let N := normalizer (P : Set Model)
      ¬ (Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
         Nonempty ((N ⧸ pCore 2 N) ≃* Sporadic.Mathieu.M24) ∨
         Nonempty ((N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 8)))) (g : Model) :
    ¬ normalizer (P : Set Model) ≤ fullNormalizer.map (MulAut.conj g).toMonoidHom := by
  intro hn
  rcases radical_quotient_of_conjugate P hP hlarge g hn with h | h
  · exact hq (Or.inl h)
  · exact hq (Or.inr (Or.inr h))

end Janko4.LocalStructure.LargeCenterRadicals.LinearFiveRows
