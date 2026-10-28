module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.NativeLinearFive
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MaximalOvergroup
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.MaximalLocal
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.UnitaryExclusion

/-!
# Conditional assembly of the native four-local exclusions

This leaf states the exact outstanding maximal-two-local cover and derives
its large-center and original-residual consequences. The two small-center
locals disappear by radical saturation. The remaining native Mathieu and
linear-five branches have already proved residual exclusions. All conjugators,
full intrinsic cores and whole-normal residuals are retained.

The cover is an explicit hypothesis here, not an asserted classification.
Its independent producer owns Kleidman--Wilson (1988), Section 2,
pp.488--493. The selective radical consumer follows An--O'Brien--Wilson
(2003), Section 4, p.122; the general surviving-row classification is separate.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals
open ElementaryNormalizerCover
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
attribute [local irreducible] modelGroup matrixA matrixB

/-- The outstanding source cover, stated on the four literal native locals.
This is a proposition specifying an input, not a proof of that input. -/
abbrev MaximalTwoLocalCover : Prop :=
  ∀ M : Subgroup Model, IsMaximalTwoLocal M → ∃ g : Model,
    M = max1.map (MulAut.conj g).toMonoidHom ∨
    M = sourceSubgroup.map (MulAut.conj g).toMonoidHom ∨
    M = LinearFive.fullNormalizer.map (MulAut.conj g).toMonoidHom ∨
    M = SymmetricLinear.max4Subgroup.map (MulAut.conj g).toMonoidHom

/-- The cover leaves just two actual overgroups for any large-center radical.
Neither a full ambient Sylow nor maximality of its own normalizer is required. -/
theorem large_center_normalizer_two_branches (hcover : MaximalTwoLocalCover)
    (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hlarge : 64 ≤ Nat.card (center P)) :
    ∃ g : Model,
      normalizer (P : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom ∨
      normalizer (P : Set Model) ≤
        LinearFive.fullNormalizer.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨M,hM,hNM,h2,h4⟩ := exists_maximal_overgroup_not_small P hP hlarge
  obtain ⟨g,hg | hg | hg | hg⟩ := hcover M hM
  · exact ⟨g, Or.inl (hg ▸ hNM)⟩
  · exact (h2 ⟨(MulEquiv.subgroupCongr hg).trans
      ((MulAut.conj g).subgroupMap sourceSubgroup).symm⟩).elim
  · exact ⟨g, Or.inr (hg ▸ hNM)⟩
  · exact (h4 ⟨(MulEquiv.subgroupCongr hg).trans
      ((MulAut.conj g).subgroupMap SymmetricLinear.max4Subgroup).symm⟩).elim

/-- A whole-normal unitary residual excludes both surviving branches of the
actual cover. The linear-five quotient is the proved native recognition. -/
theorem unitary_radical_false_of_cover (hcover : MaximalTwoLocalCover)
    (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hlarge : 64 ≤ Nat.card (center P))
    (B : Subgroup (normalizer (P : Set Model))) [B.Normal]
    (b : (B ⧸ pCore 2 B) ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  obtain ⟨g,hg | hg⟩ := large_center_normalizer_two_branches hcover P hP hlarge
  · exact MathieuRows.unitary_radical_normalizer_not_le_mathieu_conjugate P hP hlarge B b g hg
  · exact LinearFiveLocal.unitary_residual_not_embed_linearFive b
      (LinearFiveLocal.recognizedConjugateQuotientEquiv g)
      ((inclusion hg).comp B.subtype) ((inclusion_injective hg).comp B.subtype_injective)

/-- Source maximality excludes the two remaining locals for a normalizer
whose three candidate simple quotients have already been excluded. -/
theorem maximal_radical_false_of_cover (hcover : MaximalTwoLocalCover)
    (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hlarge : 64 ≤ Nat.card (center P))
    (hmax : IsMaximalTwoLocal (normalizer (P : Set Model)))
    (hq : let N := normalizer (P : Set Model)
      ¬ (Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
         Nonempty ((N ⧸ pCore 2 N) ≃* Sporadic.Mathieu.M24) ∨
         Nonempty ((N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 8)))) : False := by
  obtain ⟨g,hg | hg⟩ := large_center_normalizer_two_branches hcover P hP hlarge
  · exact MathieuRows.maximal_local_not_le_mathieu _ hmax hq g hg
  · exact LinearFiveLocal.maximal_local_not_le_recognized_conjugate _ hmax
      (fun h => hq (Or.inl h)) g hg

end Janko4.LocalStructure.LargeCenterRadicals
