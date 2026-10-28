module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.Structure
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.UnitaryDescent

/-!
# Assembly of the intrinsic degree-three subgroup exhaustion

The point and dual-point cases and strict linear and unitary parameter descent
are proved. For the remaining groups, the assembly separates local solvability,
recognition of a self-centralizing simple normal subgroup, and solvability of
its outer quotient. These three inputs remain explicit below; this module does
not yet assert unconditional proper-subgroup exhaustion.

All model alternatives carry actual multiplicative equivalences. Normality is
relative to the proper subgroup, and its quotient is the actual group quotient.
No K-group or section-classification premise is used.

Source: GLS3, Theorem 6.5.3(a–i), `refs/KGroup/GLS3/chapter6.tex`, for
characteristic two and proper subgroups. The printed shortened proof's use of
the K-group hypothesis cannot discharge the recognition input here.
-/

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

open CFSG.KnownSimple Matrix
open scoped MatrixGroups

/-- Both parameter bounds follow from the actual subgroup injection, so a
recognized core model belongs to the envelope. -/
public theorem CoreModel.envelope {f : ℕ} (hf : 0 < f)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2 ^ f)
    (U : Subgroup PSL(3,F)) (hU : U ≠ ⊤) (N : Subgroup U)
    (hN : CoreModel N) : Envelope f N := by
  cases hN with
  | linearTwo q h => exact .linearTwo N q h
  | binaryThree h => exact .binaryThree N h
  | alternatingSix e =>
      obtain ⟨e⟩ := e
      exact .subgroup e.toMonoidHom e.injective .alternatingSix
  | linear m hm h =>
      exact .linearSubfield N m hm
        (linear_parameter_lt_of_injective hf F hF U hU h N.subtype N.subtype_injective) h
  | unitary m hm h =>
      exact .unitarySubfield N m hm
        (unitary_parameter_lt_of_injective hf hm F hF h
          (U.subtype.comp N.subtype) (U.subtype_injective.comp N.subtype_injective)) h

/-- Conditional assembly, with each unproved structural input stated separately.
The unconditional theorem must instantiate all three inputs. -/
public theorem proper_subgroup_envelope_of_core_inputs
    (hlocal : ∀ f, 2 ≤ f → ∀ (F : Type) [Field F] [Finite F],
      Nat.card F = 2 ^ f → ∀ U : Subgroup PSL(3,F), U ≠ ⊤ →
      ¬ FixesPointOrDual F U → HasAbelianNormal U → Group.IsSolvable U)
    (hcore : ∀ f, 2 ≤ f → ∀ (F : Type) [Field F] [Finite F],
      Nat.card F = 2 ^ f → ∀ U : Subgroup PSL(3,F), U ≠ ⊤ →
      ¬ FixesPointOrDual F U → ¬ HasAbelianNormal U → HasRecognizedCore U)
    (hquotient : ∀ f, 2 ≤ f → ∀ (F : Type) [Field F] [Finite F],
      Nat.card F = 2 ^ f → ∀ U : Subgroup PSL(3,F), U ≠ ⊤ →
      ∀ (N : Subgroup U) [N.Normal] [IsSimpleGroup N], ¬ Group.IsSolvable N →
      Subgroup.centralizer (N : Set U) = ⊥ → CoreModel N → Group.IsSolvable (U ⧸ N)) :
    ∀ f, 2 ≤ f → ∀ (F : Type) [Field F] [Finite F],
      Nat.card F = 2 ^ f → ∀ U : Subgroup PSL(3,F), U ≠ ⊤ → Envelope f U := by
  intro f hf F _ _ hF U hU
  by_cases hgeom : FixesPointOrDual F U
  · exact envelope_of_fixesPointOrDual F f U hgeom
  by_cases hab : HasAbelianNormal U
  · exact .solvable U (hlocal f hf F hF U hU hgeom hab)
  obtain ⟨N, hn, hs, hns, hc, hm⟩ := hcore f hf F hF U hU hgeom hab
  let := hn
  let := hs
  exact .extension N
    (hm.envelope (by omega) F hF U hU N)
    (.solvable _ (hquotient f hf F hF U hU N hns hc hm))

end CFSG.Quasithin.MainConverse.LinearThreeSections
