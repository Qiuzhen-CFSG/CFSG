module

public import Theory.Representation.BinaryAlternatingSixExtensions.SuzukiSection
public import Theory.SpecificGroups.SymmetricSix.NaturalExtensionLifts

public noncomputable section
namespace Representation.BinaryAlternatingSixExtensions

private abbrev A6 := alternatingGroup (Fin 6)
private abbrev Free := GLS3.Chapter5.SchurPresentation.AlternatingSuzukiFreeGroup 1

/-- Correct the fourth Suzuki lift to an involution while leaving the root and
root-adjacent relator evaluations unchanged.  The correction is made inside
the actual marked natural kernel and does not assume an A₆ complement. -/
theorem correct_last_suzuki_tail
    {E : Type*} [Group E] (q : E →* A6)
    (e : q.ker ≃* Multiplicative Theory.SpecificGroups.SymmetricSix.NaturalModule)
    (he : ∀ (g : E) (v : q.ker),
      e (MulAut.conjNormal g v) = Multiplicative.ofAdd
        (Theory.SpecificGroups.SymmetricSix.polarAction (q g).val (e v).toAdd))
    (lift : Fin 4 → E)
    (hvalues : ∀ i, q (lift i) =
      GLS3.Chapter5.SchurPresentation.alternatingSuzukiGenerator 1 i)
    (hroot : FreeGroup.lift lift
        (GLS3.Chapter5.SchurPresentation.SuzukiRelator.word
          (GLS3.Chapter5.SchurPresentation.SuzukiRelator.rootCube :
            GLS3.Chapter5.SchurPresentation.SuzukiRelator 1)) = 1)
    (hadj : FreeGroup.lift lift
        (GLS3.Chapter5.SchurPresentation.SuzukiRelator.word
          (GLS3.Chapter5.SchurPresentation.SuzukiRelator.rootAdjacentCube :
            GLS3.Chapter5.SchurPresentation.SuzukiRelator 1)) = 1) :
    ∃ lift' : Fin 4 → E,
      (∀ i, i ≠ 3 → lift' i = lift i) ∧
      q (lift' 3) = GLS3.Chapter5.SchurPresentation.alternatingSuzukiGenerator 1 3 ∧
      (lift' 3)^2 = 1 ∧
      FreeGroup.lift lift'
          (GLS3.Chapter5.SchurPresentation.SuzukiRelator.word
            (GLS3.Chapter5.SchurPresentation.SuzukiRelator.rootCube :
              GLS3.Chapter5.SchurPresentation.SuzukiRelator 1)) = 1 ∧
      FreeGroup.lift lift'
          (GLS3.Chapter5.SchurPresentation.SuzukiRelator.word
            (GLS3.Chapter5.SchurPresentation.SuzukiRelator.rootAdjacentCube :
              GLS3.Chapter5.SchurPresentation.SuzukiRelator 1)) = 1 := by
  have hq3 : orderOf (q (lift 3)) = 2 := by
    rw [hvalues]
    exact orderOf_eq_prime
      (by simpa using
        GLS3.Chapter5.SchurPresentation.alternatingSuzukiGenerator_tail_sq
          1 (3 : Fin 4) (by decide))
      (by intro h
          have := congrArg Subtype.val h
          norm_num at this)
  obtain ⟨p, hp2, hpy⟩ :=
    Theory.SpecificGroups.SymmetricSix.NaturalExtensionLifts.correct_involution_lift
      q e he (lift 3) hq3
  let lift' : Fin 4 → E := fun i => if i = 3 then p * lift 3 else lift i
  have h3 : lift' 3 = p * lift 3 := by simp [lift']
  have hne (i : Fin 4) (hi : i ≠ 3) : lift' i = lift i := by
    simp [lift', hi]
  refine ⟨lift', hne, ?_, ?_, ?_, ?_⟩
  · rw [h3, map_mul, hp2, one_mul, hpy]
  · rw [h3]
    exact hp2
  · simpa only [GLS3.Chapter5.SchurPresentation.SuzukiRelator.word,
      GLS3.Chapter5.SchurPresentation.suzukiFreeGenerator,
      FreeGroup.lift_apply_of, hne 0 (by decide),
      pow_three] using hroot
  · simpa only [GLS3.Chapter5.SchurPresentation.SuzukiRelator.word,
      GLS3.Chapter5.SchurPresentation.suzukiFreeGenerator,
      FreeGroup.lift_apply_of, hne 0 (by decide), hne 1 (by decide),
      pow_three] using hadj

end Representation.BinaryAlternatingSixExtensions
