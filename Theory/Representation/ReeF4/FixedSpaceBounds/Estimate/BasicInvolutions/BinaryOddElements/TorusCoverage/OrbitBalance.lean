module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusData

/-!
# The short and long F4 weight counts

The long-root orbit is obtained from the existing short-root table by reversing
the four coroot coordinates and doubling the last two. Kernel-checked reflection
words start at `(1,0,0,0)`; injectivity and closure under all simple reflections
certify the resulting twenty-four-weight Weyl orbit for the actual F4 Cartan
matrix. This is the orbit to compare with the end-node short-root orbit.

`ShortLongBalance` states equality of the numbers of fixed characters on these
two orbits. It is a condition, not a proved property of arbitrary torus elements.
The final lemma converts the fixed-short-weight bound four into exactly the
`EndWeightMovement` condition used by the displacement consumer.

Source: GLS3, Sections 1.8 and 1.14; the spectrum input to Guralnick--Malle II,
Lemma 8.8 (internal p.57). The exceptional fixed-point equation must separately
supply the balance for the literal binary Ree embedding.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage

@[expose] def longOrbitWeight (n : Fin 24) : CorootWeight :=
  ![EndNode.endOrbitWeight n 3, EndNode.endOrbitWeight n 2,
    2 * EndNode.endOrbitWeight n 1, 2 * EndNode.endOrbitWeight n 0]

@[expose] def longOrbitWord (n : Fin 24) : List (Fin 4) :=
  (EndNode.endOrbitWord n).map Fin.rev

theorem longOrbitWord_spec : ∀ n : Fin 24,
    (longOrbitWord n).foldl (fun μ i => EndNode.reflectWeight i μ)
      ![1, 0, 0, 0] = longOrbitWeight n := by decide

theorem longOrbitWeight_injective : Function.Injective longOrbitWeight := by decide

theorem longOrbitWeight_reflection_closed : ∀ (i : Fin 4) (n : Fin 24),
    ∃ m : Fin 24, EndNode.reflectWeight i (longOrbitWeight n) = longOrbitWeight m :=
  by decide

variable {F : Type*} [Field F]

@[expose] noncomputable def fixedWeightCount (w : Fin 24 → CorootWeight)
    (t : Fin 4 → Fˣ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun n => corootCharacter t (w n) = 1)).card

@[expose] def ShortLongBalance (t : Fin 4 → Fˣ) : Prop :=
  fixedWeightCount EndNode.endOrbitWeight t = fixedWeightCount longOrbitWeight t

theorem endWeightMovement_iff_fixedWeightCount_le (t : Fin 4 → Fˣ) :
    EndWeightMovement t ↔ fixedWeightCount EndNode.endOrbitWeight t ≤ 4 := by
  classical
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 24)))
    (fun n => corootCharacter t (EndNode.endOrbitWeight n) = 1)
  have hu : (Finset.univ : Finset (Fin 24)).card = 24 := by decide
  rw [hu] at hc
  change (Finset.univ.filter (fun n => corootCharacter t (EndNode.endOrbitWeight n) = 1)).card +
    (Finset.univ.filter (fun n => corootCharacter t (EndNode.endOrbitWeight n) ≠ 1)).card = 24 at hc
  constructor
  · rintro ⟨s, hs, hm⟩
    have hle : s.card ≤
        (Finset.univ.filter (fun n => corootCharacter t (EndNode.endOrbitWeight n) ≠ 1)).card :=
      Finset.card_le_card (fun n hn => Finset.mem_filter.mpr ⟨Finset.mem_univ n, hm n hn⟩)
    unfold fixedWeightCount
    omega
  · intro hb
    refine ⟨Finset.univ.filter (fun n => corootCharacter t (EndNode.endOrbitWeight n) ≠ 1),
      ?_, ?_⟩
    · unfold fixedWeightCount at hb
      omega
    · intro n hn
      exact (Finset.mem_filter.mp hn).2

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage
