module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.Actions
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.BinaryReduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.AmbientCoordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.NormalForms
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseThreeExclusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion

/-!
# Assembling the Held action alternatives from Janko's coordinate cases

Janko's Section 1 first obtains four matrix cases, then uses the simple
ambient group to exclude Cases III and IV. The explicit basis comparison
in `Coordinates` identifies Cases I and II with `PermutationModel` and
`TwistedModel`, respectively. Here that comparison is applied to the
literal action `D.binaryAction K hK` used by the centralizer reduction.

`action_alternatives` discharges four-case exhaustion and both ambient
exclusions under the original finite simple ambient hypotheses. The earlier
conditional assembly remains available. Ambient simplicity is essential to
the exclusions: faithfulness and the center orders alone do not exclude the
last two cases. Comparison with the concrete M22 and A10 centralizers belongs
to the enclosing local-model dichotomy.

Sources: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), pp.2–3, DOI 10.1016/0021-8693(68)90002-1;
D. Held, Illinois J. Math. 13 (1969), p.224, DOI 10.1215/ijm/1256053756.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal binary centralizer action has the desired alternatives once
the four-case classification and both ambient exclusions have been proved. -/
public theorem action_alternatives_of_coordinate_cases
    (D : LocalData G) (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K)
    (hcases : ∃ k, Nonempty (JankoCoordinates (D.binaryAction K hK) k))
    (hthree : ¬ Nonempty (JankoCoordinates (D.binaryAction K hK) .three))
    (hfour : ¬ Nonempty (JankoCoordinates (D.binaryAction K hK) .four)) :
    Nonempty ((BinaryFour ⋊[D.binaryAction K hK] SymmetricFour) ≃* TwistedModel) ∨
      Nonempty ((BinaryFour ⋊[D.binaryAction K hK] SymmetricFour) ≃* PermutationModel) := by
  obtain ⟨k, ⟨R⟩⟩ := hcases
  cases k with
  | one => exact Or.inr ⟨R.permutationEquiv⟩
  | two => exact Or.inl ⟨R.twistedEquiv⟩
  | three => exact (hthree ⟨R⟩).elim
  | four => exact (hfour ⟨R⟩).elim

/-- The actual binary complement action in a finite simple ambient group gives
one of the two surviving semidirect products from Held's local dichotomy.
Janko's four normal forms and both ambient exclusions are proved from the
supplied local data, with no additional coordinate or recognition premise. -/
public theorem action_alternatives [IsSimpleGroup G]
    (D : LocalData G) (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K) :
    Nonempty ((BinaryFour ⋊[D.binaryAction K hK] SymmetricFour) ≃* TwistedModel) ∨
      Nonempty ((BinaryFour ⋊[D.binaryAction K hK] SymmetricFour) ≃* PermutationModel) :=
  action_alternatives_of_coordinate_cases D K hK
    (binaryAction_jankoCoordinates D K hK)
    (not_nonempty_jankoCoordinates_three D K hK)
    (not_nonempty_jankoCoordinates_four D K hK)

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
