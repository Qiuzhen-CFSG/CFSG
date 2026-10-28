module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.NormalizerBasis.CharacterMarking.Orbit

/-!
# Constructing the oriented orbit before specializing the character group

This packages the finite eight-element argument at abstract automorphisms.
Keeping their power relations abstract prevents elaboration from expanding
concrete inverse-pullback functions. The source application supplies every
premise from its actual Sylow subgroup and the marked involution's evaluation.

The indexing and orientation follow Gorenstein, *Finite Groups*, §16.6,
pp.482–483, preceding (6.1)–(6.2).
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation.CharacterMarking

variable {W K : Type*} [Group W] [CommGroup K]

/-- An oriented seven-orbit with the source cubic permutation and positive triple. -/
public structure OrbitMarking (Y U : MulAut W) (e : W →* K) where
  reverse : Bool
  character : Fin 7 → W
  injective : Function.Injective character
  nontrivial : ∀ i, character i ≠ 1
  exhaustive : ∀ w : W, w ≠ 1 → ∃ i, character i = w
  y_action : ∀ i, character (i - 1) = (if reverse then Y⁻¹ else Y) (character i)
  u_action : ∀ i, character (2 * i + 3) = U (character i)
  positive : ∀ i, e (character i) = 1 ↔ positivePattern i = true

/-- The action relations and a cubic-invariant kernel of order four construct
all parts of the oriented orbit marking. -/
public theorem exists_orbitMarking [Finite W] (hW : Nat.card W = 8)
    (Y U : MulAut W) (hY7 : Y ^ 7 = 1) (hYn : Y ≠ 1) (hU3 : U ^ 3 = 1)
    (hUY : U * Y = Y ^ 2 * U) (e : W →* K) (he : Nat.card e.ker = 4)
    (hUe : ∀ w, e (U w) = e w) : Nonempty (OrbitMarking Y U e) := by
  classical
  obtain ⟨w, hw, hUw⟩ := cubic_fixed hW U hU3
  let f := orbitLabel Y w
  let p : Fin 7 → Bool := fun i => decide (e (f i) = 1)
  have hpU : ∀ i, p (2 * i + 3) = p i := by
    intro i
    dsimp [p, f]
    simp only [orbitLabel_u Y U hY7 hUY w hUw, hUe]
  have hpc : (Finset.univ.filter (fun i => p i = true)).card = 3 := by
    have hc := positive_card hW Y hY7 hYn hw e he
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
    simpa [p, f] using hc
  rcases finite_pattern p hpU hpc with hp | hp
  · refine ⟨{ reverse := false
              character := f
              injective := orbitLabel_injective hW Y hY7 hYn hw
              nontrivial := orbitLabel_nontrivial Y hw
              exhaustive := orbitLabel_exhaustive hW Y hY7 hYn hw
              y_action := orbitLabel_y Y hY7 w
              u_action := orbitLabel_u Y U hY7 hUY w hUw
              positive := ?_ }⟩
    intro i
    have hh := congrArg (fun b : Bool => b = true) (hp i)
    simpa only [p, decide_eq_true_eq] using Iff.of_eq hh
  · let f' : Fin 7 → W := fun i => f (1 - i)
    refine ⟨{ reverse := true
              character := f'
              injective := ?_
              nontrivial := fun i => orbitLabel_nontrivial Y hw (1 - i)
              exhaustive := ?_
              y_action := reflected_y Y f (orbitLabel_y Y hY7 w)
              u_action := reflected_u U f (orbitLabel_u Y U hY7 hUY w hUw)
              positive := ?_ }⟩
    · intro i j hij
      have hij' : (1 - i : Fin 7) = 1 - j := orbitLabel_injective hW Y hY7 hYn hw hij
      exact sub_right_injective hij'
    · intro χ hχ
      obtain ⟨i, hi⟩ := orbitLabel_exhaustive hW Y hY7 hYn hw χ hχ
      refine ⟨1 - i, ?_⟩
      change f (1 - (1 - i)) = χ
      rw [sub_sub_self]
      exact hi
    · intro i
      have hh := congrArg (fun b : Bool => b = true) (hp i)
      simpa only [p, f', decide_eq_true_eq] using Iff.of_eq hh

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation.CharacterMarking
