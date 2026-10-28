module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.NormalizerBasis.CharacterMarking.LocalAction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.NormalizerBasis.CharacterMarking.OrbitConstruction

/-!
# Constructing the source seven-character marking

The dual of the actual Sylow eight has eight elements. Its marked seven-element
acts as a seven-cycle on the nontrivial characters, and the cubic element fixes
one of these characters. Label this fixed character by 4 and its orbit using the
column convention of the source matrices.

Evaluation at the marked involution is cubic-invariant and has kernel of order
four. Thus three nontrivial characters have value +1. The fixed index must have
value −1, and exactly one cubic triple has value +1. Inverting the seven-element
interchanges the triples, producing the exact diagonal of `normalX`.

This proves the finite character calculation in Gorenstein, *Finite Groups*,
§16.6, pp.482–483, preceding (6.1)–(6.2). The self-centralizing Sylow subgroup
and disjoint complement suffice; neither a representation nor ambient order
and fusion hypotheses are needed. The original character-frame interface and
its inverse-conjugation conventions are retained literally.
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation
open CharacterMarking

variable {G : Type*} [Group G] [Finite G] {h : Janko1CentralizerData G}

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private theorem character_value (χ : Character h) (s : h.sylow) :
    (χ s : ZMod 11) = 1 ∨ (χ s : ZMod 11) = -1 := by
  have hp : χ s ^ 2 = 1 := by rw [← map_pow, h.sylow_square, map_one]
  exact sq_eq_one_iff.mp (congrArg Units.val hp)

private theorem value_of_pattern (χ : Character h) (s : h.sylow) (i : Fin 7)
    (hi : decide (χ s = 1) = positivePattern i) :
    (χ s : ZMod 11) = normalX i i := by
  have hi' : decide ((χ s : ZMod 11) = 1) = positivePattern i := by
    simpa only [Units.val_eq_one] using hi
  rcases character_value χ s with hv | hv <;> rw [hv] at hi' ⊢ <;>
    fin_cases i <;> simp_all [positivePattern, normalX, Matrix.diagonal]

/-- Construct the complete character marking from the source normalizer frame.
The allowed orientation is chosen to give the literal diagonal of `normalX`. -/
public theorem exists_normalizerCharacterFrame (D : NormalizerFrame h) : Nonempty (NormalizerCharacterFrame D) := by
  classical
  let e : Character h →* (ZMod 11)ˣ := MonoidHom.eval ⟨D.x, D.x_mem⟩
  obtain ⟨C⟩ : Nonempty (OrbitMarking (characterY D false) (characterU D) e) := by
    apply exists_orbitMarking (character_card h)
    · exact characterY_pow D false
    · exact characterY_ne_one D false
    · exact characterU_pow D
    · exact character_action D false
    · exact evaluation_ker_card D
    · exact characterU_x D
  refine ⟨{ reverse := C.reverse
            character := C.character
            injective := C.injective
            nontrivial := C.nontrivial
            exhaustive := C.exhaustive
            y_action := ?_
            u_action := ?_
            x_value := ?_ }⟩
  · intro i s
    have hy : (if C.reverse then (characterY D false)⁻¹ else characterY D false) =
        characterY D C.reverse := by
      cases C.reverse
      · rfl
      · exact (characterY_reverse D).symm
    have he := congrArg (fun χ : Character h => χ s) (C.y_action i)
    rw [hy, characterY_apply] at he
    exact he
  · intro i s
    simpa only [characterU_apply] using congrArg (fun χ : Character h => χ s) (C.u_action i)
  · intro i
    apply value_of_pattern
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq, e, MonoidHom.eval, MonoidHom.flip_apply,
      MonoidHom.id_apply] using C.positive i

/-- The character marking for the actual source Bruhat frame, used by the
seven-dimensional normalizer-basis construction. -/
public theorem exists_normalizerCharacterFrame_of_bruhat (D : BruhatFrame h) :
    Nonempty (NormalizerCharacterFrame D.toNormalizerFrame) :=
  exists_normalizerCharacterFrame D.toNormalizerFrame

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation
