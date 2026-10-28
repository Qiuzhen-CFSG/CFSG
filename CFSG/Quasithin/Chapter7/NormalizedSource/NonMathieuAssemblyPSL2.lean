module

public import CFSG.Quasithin.Chapter7.NormalizedSource.Alternatives
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.SourceAssembly
public import Theory.Representation.BinaryOffender.NormalizerNonFF
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# The selected PSL₂ branch on the original action

Chapter K constructs the actual natural or orthogonal model from the marked
central quotient. A natural offender embeds into the full component normalizer.
At the orthogonal field-four endpoint, the constructed five-point coordinates
embed the faithful symmetric-five action into that same normalizer. Its
transposition offender excludes this endpoint even for an alternating-five
ambient action. The surviving model has exponent greater than one.

Source: Aschbacher--Smith, K.3.1,3.2.9(1), and the proof of12.2.2,
printed pp.453--454,582--583,795 (combined manuscript,1 March2004).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuAssembly
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin CFSG.Quasithin.ChapterK.RankOne
open scoped MatrixGroups

variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) A E} {Q : Subgroup A}

/-- The full normalizer of the marked orthogonal field-four action is FF,
including when the original ambient action is only alternating-five. -/
theorem orthogonal_one_normalizer_ff (M : OrthogonalModel 1 ρ Q) :
    IsFFModule (normalizerRepresentation (ρ.comp Q.subtype)) := by
  classical
  by_contra hnon
  let C := OrthogonalFourMinus.FivePoint.Construction.comparison
  let e := M.groupEquiv.trans C.groupEquiv
  let F := M.fivePointNaturalCoordinates C
  let b : Representation.Equiv
      ((ρ.comp Q.subtype).comp e.symm.toMonoidHom)
      ((BinaryPermutation.naturalRepresentation (Fin 5)).comp
        (alternatingGroup (Fin 5)).subtype) := {
    __ := F
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      have ht := M.fivePoint_natural_intertwines C (e.symm g) v
      change F (ρ (e.symm g).val v) =
        BinaryPermutation.naturalRepresentation (Fin 5) (e (e.symm g)).val (F v) at ht
      simpa only [LinearMap.comp_apply, MonoidHom.comp_apply,
        LinearEquiv.coe_coe, MulEquiv.coe_toMonoidHom,
        Subgroup.coe_subtype, e.apply_symm_apply] using ht }
  let : ((alternatingGroup (Fin 5)).subtype).range.Normal := by
    rw [Subgroup.range_subtype]
    infer_instance
  have hn := not_isFFModule_of_marked_normal_range
    (BinaryPermutation.naturalRepresentation (Fin 5))
    (BinaryPermutation.naturalRepresentation_injective (Fin 5) (by decide))
    (alternatingGroup (Fin 5)).subtype (ρ.comp Q.subtype)
    e.symm.toMonoidHom e.symm.surjective b.symm hnon
  exact hn ⟨_, (ChapterB.Offenders.Odd.isOffender_disjointTranspositions
    (Or.inl rfl) (n := 5) (m := 1) (by decide) (by decide)).2.2.2⟩

variable [Finite A] [FiniteDimensional (ZMod 2) E]

omit [FiniteDimensional (ZMod 2) E] in
private theorem fullNormalizer_ff_of_ff (h : SourceHypotheses ρ Q) (hff : IsFFModule ρ) :
    IsFFModule (normalizerRepresentation (ρ.comp Q.subtype)) := by
  let : Q.Normal := h.layer_normal
  apply isFFModule_linearNormalizer ρ Q
  exact hff.map_equivariant ρ (imageRepresentation ρ) (actionHom ρ)
    (fun _ _ he => h.faithful (congrArg (fun a : actionImage ρ => a.val.val) he))
    (LinearEquiv.refl _ _) (fun _ _ => rfl)

/-- K.3.1 on the literal quotient: full-normalizer non-FF excludes the
natural action and the orthogonal endpoint, leaving exponent greater than one. -/
theorem orthogonal_of_psl2 (h : SourceHypotheses ρ Q)
    (hnon : ¬ IsFFModule (normalizerRepresentation (ρ.comp Q.subtype)))
    {r : ℕ} (hr : 2 ≤ r)
    (hq : ClassicalGroup.IsPSL (Q ⧸ center Q) 2 (2 ^ r)) :
    Chapter7.NormalizedSource.OrthogonalMinusAlternative ρ Q := by
  obtain ⟨K, hK, hfin, hchar, hc, e, hd, halt⟩ := h.psl2_case hr hq
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  rcases halt with ⟨_, _, M, _, hcubic, _⟩ | ⟨s, _, _, hs, _, _, M, _⟩
  · exact (hnon (fullNormalizer_ff_of_ff h
      ((isFFModule_iff_cubicRatio_le_one ρ).mpr hcubic.le))).elim
  · let : NeZero s := ⟨hs.ne'⟩
    have hs1 : 1 < s := by
      by_contra hn
      have he : s = 1 := by omega
      cases he
      exact hnon (orthogonal_one_normalizer_ff M)
    exact ⟨s, hs1, ⟨M⟩⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuAssembly
