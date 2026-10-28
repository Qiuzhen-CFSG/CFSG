module

public import Stellmacher.Recognition.MinimalSimpleModels
public import Stellmacher.Recognition.ConversePSL2Binary
public import Stellmacher.Recognition.ConversePSL2ThreePower
public import Stellmacher.Recognition.ConversePSL2Prime
public import Stellmacher.Recognition.ConverseSuzuki
public import Stellmacher.Recognition.ConversePSL3Three

/-!
# The converse of Thompson's minimal-simple classification

Every finite group in the five-family catalogue is minimal simple. Each
constructor supplies an actual multiplicative equivalence to its model.
The corresponding model theorem proves minimal simplicity with exactly the
constructor's arithmetic hypotheses; transport along the inverse equivalence
then proves minimal simplicity of the original group.

Source: Thompson, *Nonsolvable finite groups all of whose local subgroups are
solvable*, I, Bull. Amer. Math. Soc. 74 (1968), Corollary 1, p. 388.
See `docs/thompson-minimal-simple-source-contract.md` and the five imported
converse modules for the model proofs.
-/

namespace Stellmacher.Recognition.ThompsonMinimalSimpleModel

/-- Every group in Thompson's five-family catalogue is minimal simple. -/
public theorem isMinimalSimple {G : Type*} [Group G] [Finite G]
    (hG : ThompsonMinimalSimpleModel G) : IsMinimalSimple G := by
  cases hG with
  | psl2Binary p hp e =>
      exact (isMinimalSimple_psl2_binary hp).of_mulEquiv e.symm
  | psl2ThreePower p hp hodd e =>
      exact (isMinimalSimple_psl2_three_power hp hodd).of_mulEquiv e.symm
  | psl2Prime p hp hgt hmod e =>
      let : Fact p.Prime := ⟨hp⟩
      exact (isMinimalSimple_psl2_prime (F := ZMod p) hp
        (by simp [Nat.card_eq_fintype_card]) hgt hmod).of_mulEquiv e.symm
  | suzuki n hp e =>
      exact (isMinimalSimple_suzuki hp).of_mulEquiv e.symm
  | psl3Three e =>
      exact isMinimalSimple_psl3_three.of_mulEquiv e.symm

end Stellmacher.Recognition.ThompsonMinimalSimpleModel
