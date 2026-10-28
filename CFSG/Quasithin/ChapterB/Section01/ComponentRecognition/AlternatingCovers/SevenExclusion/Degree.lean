module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.SevenExclusion.ModelInputs
public import Theory.Representation.CentralCubicDegree
public import Theory.GroupTheory.FiveCycleSquareLift
public import Theory.SpecificGroups.Alternating.SevenFiveCycle

/-!
# Faithful binary degrees of the triple cover of A₇

The central cubic subgroup embeds in the Schur endomorphism field, so that
field has binary degree at least two. Perfectness makes its representation
degree divisible by three. The five-cycle and squaring conjugator in A₇
lift through the actual central kernel, excluding representation degree at most
three over that field.
Thus every faithful irreducible binary module has dimension at least twelve,
which supplies the coarse bound ten used in the FF exclusion.

Source: Aschbacher–Smith, B.1.13, printed pp.73–74, and K.1, printed p.452,
citing Guralnick–Malle, Theorem 6.2 and Table 6.3. This is an elementary
degree-bound argument; it does not require a modular character catalogue.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.AlternatingCovers.SevenExclusion
open GLS3.Chapter5.OddCentralCovers
universe w

/-- The order-five squaring configuration in the genuine triple cover. -/
theorem tripleSeven_five_square_pair :
    ∃ x y : TripleSeven, orderOf x = 5 ∧ y * x * y⁻¹ = x ^ 2 := by
  obtain ⟨x, y, hx, hxy⟩ := alternatingGroup.exists_five_cycle_square_pair_seven
  exact tripleSevenCovering.toMonoidHom.exists_five_cycle_square_lift
    tripleSevenCovering.surjective tripleSevenCovering.ker_le_center
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using tripleSevenCovering_kernel_card)) x y hx hxy

/-- In fact the faithful irreducible binary degree is at least twelve. -/
theorem finrank_ge_twelve {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) TripleSeven W)
    (hf : Function.Injective τ) (hi : Representation.IsIrreducible τ) :
    12 ≤ Module.finrank (ZMod 2) W := by
  let := hi
  obtain ⟨x, y, hx, hxy⟩ := tripleSeven_five_square_pair
  exact Representation.CentralCubicDegree.finrank_ge_twelve τ hf
    tripleSeven_center_card x y hx hxy

/-- The exact model input consumed by the triple-seven FF exclusion. -/
theorem degreeBound : DegreeBound.{w} := by
  intro W _ _ _ τ hf hi
  exact (by decide : 10 ≤ 12).trans (finrank_ge_twelve τ hf hi)

end CFSG.Quasithin.ChapterB.ComponentRecognition.AlternatingCovers.SevenExclusion
