module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Center.Natural

/-!
# Regular conjugation on the moving natural line

An injective coordinate on the displacement subgroup intertwines conjugation
with multiplication by the diagonal unit. The unique unit taking one nonzero
coordinate to another is their ratio. Thus the actual conjugation action is
regular. If displacement is nontrivial, that same calculation makes its
coordinate map surjective and proves its order is the field order.

Source: the natural-line calculation underlying Aschbacher–Smith E.6.7 and
E.6.11, printed pp.246 and 249. Nonvanishing still requires the covering
argument of I.2.3; it is not inferred from a vacuous regular action.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.L2Torus
variable {L F : Type*} [Group L] [Finite L] [Field F] [Finite F] [CharP F 2]
    {B : Subgroup L} {a : MarkedBlockModel L B F}

/-- Literal conjugation, including uniqueness of the conjugating torus element. -/
theorem DiagonalSection.regular_displacement (d : DiagonalSection a)
    (hshort : ChapterC.IsShort L) (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    RegularConjugationOnNonidentity d.torus
      ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆ := by
  let D := ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆
  let f := d.displacementCoordinate hshort S
  have hf := d.displacementCoordinate_injective hshort S hS hn hF
  let act : d.torus →* MulAut D :=
    D.normalizerMonoidHom.comp (inclusion (normalizer_commutator_ge_right _ _))
  have he (x : d.torus) (v : D) :
      (f (act x v)).toAdd = (d.torusEquiv x : F) * (f v).toAdd :=
    d.displacementCoordinate_conjugate hshort S x v
  refine ⟨normalizer_commutator_ge_right _ _, ?_⟩
  intro v hv w hw
  have hv0 : (f v).toAdd ≠ 0 := by
    intro h
    exact hv (hf (h.trans (map_one f).symm))
  have hw0 : (f w).toAdd ≠ 0 := by
    intro h
    exact hw (hf (h.trans (map_one f).symm))
  let u : Fˣ := Units.mk0 ((f w).toAdd / (f v).toAdd) (div_ne_zero hw0 hv0)
  let x : d.torus := d.torusEquiv.symm u
  have hx : act x v = w := by
    apply hf
    apply Multiplicative.toAdd.injective
    rw [he]
    simp only [x, MulEquiv.apply_symm_apply, u, Units.val_mk0]
    exact div_mul_cancel₀ _ hv0
  refine ⟨x, congrArg Subtype.val hx, ?_⟩
  intro y hy
  have hy' : act y v = w := Subtype.ext hy
  apply d.torusEquiv.injective
  apply Units.ext
  apply mul_right_cancel₀ hv0
  rw [← he, ← he, hy', hx]

/-- A nonzero displacement vector generates every coordinate under the torus. -/
theorem DiagonalSection.displacementCoordinate_surjective (d : DiagonalSection a)
    (hshort : ChapterC.IsShort L) (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (hD : ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆ ≠ ⊥) :
    Function.Surjective (d.displacementCoordinate hshort S) := by
  let D := ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆
  let f := d.displacementCoordinate hshort S
  have hf := d.displacementCoordinate_injective hshort S hS hn hF
  obtain ⟨v, hv⟩ := ne_bot_iff_exists_ne_one.mp hD
  have hv0 : (f v).toAdd ≠ 0 := by
    intro h
    exact hv (hf (h.trans (map_one f).symm))
  intro t
  by_cases ht : t = 1
  · exact ⟨1, (map_one f).trans ht.symm⟩
  have ht0 : t.toAdd ≠ 0 := ht
  let u : Fˣ := Units.mk0 (t.toAdd / (f v).toAdd) (div_ne_zero ht0 hv0)
  let x : d.torus := d.torusEquiv.symm u
  refine ⟨D.normalizerMonoidHom (inclusion (normalizer_commutator_ge_right _ _) x) v, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [d.displacementCoordinate_conjugate]
  simp only [x, MulEquiv.apply_symm_apply, u, Units.val_mk0]
  exact div_mul_cancel₀ _ hv0

/-- The nontrivial displacement subgroup has order exactly 2ⁿ. -/
theorem DiagonalSection.displacement_card_of_ne_bot (d : DiagonalSection a)
    (hshort : ChapterC.IsShort L) (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (hD : ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆ ≠ ⊥) :
    Nat.card ↥⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), d.torus⁆ = 2 ^ n := by
  have he := Equiv.ofBijective (d.displacementCoordinate hshort S)
    ⟨d.displacementCoordinate_injective hshort S hS hn hF,
      d.displacementCoordinate_surjective hshort S hS hn hF hD⟩
  exact (Nat.card_congr he).trans hF

end CFSG.Quasithin.ChapterE.Section06.L2Torus
