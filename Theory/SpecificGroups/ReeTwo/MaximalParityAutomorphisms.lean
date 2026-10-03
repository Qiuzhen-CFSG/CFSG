module

public import Theory.SpecificGroups.ReeTwo.MaximalParityProfiles
public import Theory.SpecificGroups.ReeTwo.ParityFrattiniModel
public import Theory.SpecificGroups.ReeTwo.TwistedParityFrattiniModel

/-!
# Automorphisms of the two Ree two parity kernels

A Frattini quotient model with the power counts in `MaximalParityProfiles`
forces the automorphism group of the corresponding kernel to be a two-group.
The finite profile stabilizer has exponent two, and the kernel of the Frattini
action is a two-group by the Burnside basis-kernel theorem.

The explicit rank-four and rank-three models in `ParityFrattiniModel` and
`TwistedParityFrattiniModel` discharge these hypotheses for both possible values
of the binary character parameter. The groups and character parameters are those
of Shinoda (1975), (2.3), pp. 81–82, verified in `Core` and `RootAction`.
-/

namespace ReeTwo.SylowModel

/-- The untwisted parity model suffices to exclude odd-order automorphisms. -/
public theorem parity_isPGroup_mulAut_of_frattiniModel (h : ParityFrattiniModel) :
    IsPGroup 2 (MulAut (maximalCharacter 1 0 0).ker) := by
  obtain ⟨π, hπ, hker, hcount⟩ := h
  apply MonoidHom.isPGroup_mulAut_of_frattini_powerFiber
    (IsPGroup.of_card (n := 11) (maximalCharacter_ker_card 1 0 0 (by decide))) π hπ hker
  intro a ha
  refine ⟨1, ?_⟩
  apply parityProfile_aut_square
  intro v
  rw [← hcount (a v), ← hcount v, ha v 2, ha v 4]

/-- The twisted parity model suffices to exclude odd-order automorphisms. -/
public theorem twistedParity_isPGroup_mulAut_of_frattiniModel
    (h : TwistedParityFrattiniModel) :
    IsPGroup 2 (MulAut (maximalCharacter 1 1 0).ker) := by
  obtain ⟨π, hπ, hker, hcount⟩ := h
  apply MonoidHom.isPGroup_mulAut_of_frattini_powerFiber
    (IsPGroup.of_card (n := 11) (maximalCharacter_ker_card 1 1 0 (by decide))) π hπ hker
  intro a ha
  refine ⟨1, ?_⟩
  apply twistedParityProfile_aut_square
  intro v
  rw [← hcount (a v), ← hcount v, ha v 2, ha v 4]

/-- Assembly of the two independent Frattini model certificates. -/
public theorem maximalParity_isPGroup_mulAut_of_frattiniModels
    (h₀ : ParityFrattiniModel) (h₁ : TwistedParityFrattiniModel) :
    ∀ b : ZMod 2, IsPGroup 2 (MulAut (maximalCharacter 1 b 0).ker) := by
  intro b
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl
  · exact parity_isPGroup_mulAut_of_frattiniModel h₀
  · exact twistedParity_isPGroup_mulAut_of_frattiniModel h₁

/-- Both the parity kernel and its root-three twist have two-group automorphism groups. -/
public theorem maximalParity_isPGroup_mulAut :
    ∀ b : ZMod 2, IsPGroup 2 (MulAut (maximalCharacter 1 b 0).ker) :=
  maximalParity_isPGroup_mulAut_of_frattiniModels
    parityFrattiniModel twistedParityFrattiniModel

end ReeTwo.SylowModel
