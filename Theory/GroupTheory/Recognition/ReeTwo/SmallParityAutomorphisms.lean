module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityProfiles
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityFourModels
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeModels

/-!
# Automorphism reduction for fourteen small Ree two parity candidates

The intrinsic profiles have stabilizers of exponent dividing four. The verified
Frattini models and the Burnside basis-kernel theorem therefore make the full
automorphism groups two-groups. Both ranks are
assembled into the original fourteen-candidate indexing without changing any
of the subgroups. The final theorem discharges the model premises using the
eight rank-four and six rank-three certificates.

Source: Shinoda (1975), (2.3), pp. 81–82, and the kernel-checked finite
profile stabilizers in `SmallParityProfiles`.
-/

namespace ReeTwo.SylowModel

/-- A rank-four model excludes odd-order automorphisms of its candidate. -/
public theorem smallParityFour_isPGroup_mulAut_of_model (i : Fin 8)
    (h : SmallParityFourFrattiniModel i) :
    IsPGroup 2 (MulAut (smallParityTwoCandidate (smallParityFourIndex i))) := by
  obtain ⟨π, hπ, hker, hcount⟩ := h
  apply MonoidHom.isPGroup_mulAut_of_frattini_predicateFiber
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) π hπ hker
    (fun j : Fin 3 => MulAut.orderCentralizerTest (smallParityFourTests i j))
    (fun f j x => MulAut.orderCentralizerTest_apply f _ x)
  intro a ha
  refine ⟨2, smallParityFourProfile_aut_fourth i a ?_⟩
  intro v
  rw [← hcount (a v), ← hcount v, ha 0 v, ha 1 v, ha 2 v]

/-- A rank-three model excludes odd-order automorphisms of its candidate. -/
public theorem smallParityThree_isPGroup_mulAut_of_model (i : Fin 6)
    (h : SmallParityThreeFrattiniModel i) :
    IsPGroup 2 (MulAut (smallParityTwoCandidate (smallParityThreeIndex i))) := by
  obtain ⟨π, hπ, hker, hcount⟩ := h
  apply MonoidHom.isPGroup_mulAut_of_frattini_predicateFiber
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) π hπ hker
    (fun j : Fin 3 => MulAut.orderCentralizerTest (smallParityThreeTests i j))
    (fun f j x => MulAut.orderCentralizerTest_apply f _ x)
  intro a ha
  refine ⟨2, smallParityThreeProfile_aut_fourth i a ?_⟩
  intro v
  rw [← hcount (a v), ← hcount v, ha 0 v, ha 1 v, ha 2 v]

/-- The two families of model certificates cover all fourteen original subgroups. -/
public theorem smallParityTwo_isPGroup_mulAut_of_models
    (h4 : ∀ i : Fin 8, SmallParityFourFrattiniModel i)
    (h3 : ∀ i : Fin 6, SmallParityThreeFrattiniModel i) :
    ∀ i : Fin 14, IsPGroup 2 (MulAut (smallParityTwoCandidate i)) := by
  intro i
  have hfour := fun j => smallParityFour_isPGroup_mulAut_of_model j (h4 j)
  have hthree := fun j => smallParityThree_isPGroup_mulAut_of_model j (h3 j)
  fin_cases i
  · exact hfour 0
  · exact hfour 1
  · exact hfour 2
  · exact hfour 3
  · exact hthree 0
  · exact hfour 4
  · exact hfour 5
  · exact hthree 1
  · exact hfour 6
  · exact hthree 2
  · exact hthree 3
  · exact hthree 4
  · exact hfour 7
  · exact hthree 5

/-- All fourteen exact small parity candidates have two-group automorphism groups. -/
public theorem smallParityTwo_isPGroup_mulAut :
    ∀ i : Fin 14, IsPGroup 2 (MulAut (smallParityTwoCandidate i)) :=
  smallParityTwo_isPGroup_mulAut_of_models
    smallParityFourFrattiniModels smallParityThreeFrattiniModels

end ReeTwo.SylowModel
