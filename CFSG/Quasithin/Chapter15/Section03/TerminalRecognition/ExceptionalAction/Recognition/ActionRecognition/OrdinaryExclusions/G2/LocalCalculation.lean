module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.Actor
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.MarkedFactor
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement
public import Theory.Representation.G2BinaryParabolicFixed

/-!
# Applying the binary G₂ residual-core calculation to the source subgroup

Both natural actions have at most two fixed dimensions on the actual marked
core, under every isomorphism of the offender group with the full or derived
binary G₂ model. The source pair and its Thompson and commutator identities
identify the first local factor with a conjugate of the first-parabolic
two-residual. Automorphism invariance makes this marking valid for the
specified offender isomorphism, independently of the quotient isomorphism.
Transport of the intrinsic two-core then applies the natural-coordinate bound.

The bounds below require only `SourceInput` and the quotient isomorphism;
they assume no representation classification or action identification. Their
strict-four versions supply the upper bounds for the final marked-seed
contradiction, whose action-section construction remains with the consumer.

Source: Aschbacher–Smith, final proof of 15.3.1, printed p.1155.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Atlas.G2.BinaryParabolicPair
open Atlas.G2.Natural.BinaryParabolicFixed

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The literal source core on the full natural action, for the given
isomorphism and a proved marking of its first local factor. -/
theorem full_fixed_finrank_le_two_of_marking
    (f : d.offenderGroup ≃* Atlas.G2.Model (ZMod 2))
    (g : Atlas.G2.Model (ZMod 2))
    (hmark : (markedFactor d).map f.toMonoidHom =
      ResidualAction.K.map (MulAut.conj g).toMonoidHom) :
    Module.finrank (ZMod 2) (fixedSpace (g2Natural (ZMod 2))
      (d.firstCoreInOffender.map f.toMonoidHom)) ≤ 2 := by
  rw [firstCore_eq_factorCore, map_pCoreIn_of_injective 2 _ _ f.injective, hmark]
  exact conjugate_residual_core_fixed_finrank_le_two g

/-- The literal source core on the derived natural action. The marking
uses the actual derived inclusion, allowing conjugation by the full model. -/
theorem derived_fixed_finrank_le_two_of_marking
    (f : d.offenderGroup ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (g : Atlas.G2.Model (ZMod 2))
    (hmark : ((markedFactor d).map f.toMonoidHom).map
      (commutator (Atlas.G2.Model (ZMod 2))).subtype =
        ResidualAction.K.map (MulAut.conj g).toMonoidHom) :
    Module.finrank (ZMod 2) (fixedSpace (g2DerivedNatural (ZMod 2))
      (d.firstCoreInOffender.map f.toMonoidHom)) ≤ 2 := by
  rw [firstCore_eq_factorCore, map_pCoreIn_of_injective 2 _ _ f.injective]
  exact derived_residual_core_fixed_finrank_le_two _ g hmark

/-- Every full-model isomorphism sends the actual source core to a subgroup
fixing at most two natural dimensions. The source data discharge the marking. -/
theorem full_fixed_finrank_le_two
    (e0 : coreQuotient H ≃* Atlas.G2.Model (ZMod 2))
    (f : d.offenderGroup ≃* Atlas.G2.Model (ZMod 2)) :
    Module.finrank (ZMod 2) (fixedSpace (g2Natural (ZMod 2))
      (d.firstCoreInOffender.map f.toMonoidHom)) ≤ 2 := by
  obtain ⟨g, hmark⟩ := Placement.full_marking d e0 f
  exact full_fixed_finrank_le_two_of_marking d f g hmark

/-- The same source-core bound for every isomorphism onto the genuine
derived model, with its restricted natural action. -/
theorem derived_fixed_finrank_le_two
    (e0 : coreQuotient H ≃* Atlas.G2.Model (ZMod 2))
    (f : d.offenderGroup ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Module.finrank (ZMod 2) (fixedSpace (g2DerivedNatural (ZMod 2))
      (d.firstCoreInOffender.map f.toMonoidHom)) ≤ 2 := by
  obtain ⟨g, hmark⟩ := Placement.derived_marking d e0 f
  exact derived_fixed_finrank_le_two_of_marking d f g hmark

/-- The full natural action cannot accommodate the source's four-dimensional
fixed seed, even after choosing an arbitrary offender isomorphism. -/
theorem full_fixed_finrank_lt_four
    (e0 : coreQuotient H ≃* Atlas.G2.Model (ZMod 2))
    (f : d.offenderGroup ≃* Atlas.G2.Model (ZMod 2)) :
    Module.finrank (ZMod 2) (fixedSpace (g2Natural (ZMod 2))
      (d.firstCoreInOffender.map f.toMonoidHom)) < 4 :=
  lt_of_le_of_lt (full_fixed_finrank_le_two d e0 f) (by decide)

/-- The corresponding strict bound for the derived natural action. -/
theorem derived_fixed_finrank_lt_four
    (e0 : coreQuotient H ≃* Atlas.G2.Model (ZMod 2))
    (f : d.offenderGroup ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Module.finrank (ZMod 2) (fixedSpace (g2DerivedNatural (ZMod 2))
      (d.firstCoreInOffender.map f.toMonoidHom)) < 4 :=
  lt_of_le_of_lt (derived_fixed_finrank_le_two d e0 f) (by decide)

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation
