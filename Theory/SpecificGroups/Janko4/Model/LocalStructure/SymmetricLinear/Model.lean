module

public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# The specified symmetric-linear local subgroup of the binary J₄ model

`max4Program` executes the seventeen register instructions of the ATLAS
program `J4G1-max4W1` on the certified generators of the actual matrix carrier.
The source identifies the generated subgroup as
2^(3+12).(S₅ × L₃(2)). Its quotient identification, Sylow containment and
coverage of arbitrary local configurations remain separate proof obligations.
In particular, defining this subgroup asserts none of these properties.

`QuotientModel` uses SL₃(2) for the second factor. The imported, proved
`Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two` identifies it with PSL₃(2).

Source: https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/words/J4G1-max4W1,
retrieved 2026-10-05, SHA-256
`bcd21ddbe0f93dba41734f929dbdffbd8852a033d1a96f959439af48d5149529`.
The original bytes are retained in `Model/source/J4G1-max4W1`.
The application is Aschbacher–Smith, Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher's *Overgroups of
Sylow subgroups in sporadic groups* (1986).
-/

@[expose] public section

namespace Janko4.LocalStructure.SymmetricLinear

/-- Literal execution of the downloaded ATLAS subgroup program. -/
def max4Program {G : Type*} [Group G] (a b : G) : G × G :=
  let r3 := a * b
  let r4 := r3 ^ 3
  let r5 := r4 * b
  let r4 := b * a
  let r1 := r5 * b
  let r2 := r1 ^ 3
  let r1 := r4 ^ 22
  let r5 := r3 ^ 13
  let r3 := r1 * r5
  let r5 := r4 * r4
  let r1 := r3⁻¹
  let r4 := r1 * r2
  let r1 := r2 * r2
  let r2 := r4 * r3
  let r4 := r5⁻¹
  let r3 := r4 * r1
  let r1 := r3 * r5
  (r1, r2)

/-- The concrete subgroup, without a claim of maximality or local coverage. -/
def max4Subgroup : Subgroup Model :=
  Subgroup.closure {(max4Program a b).1, (max4Program a b).2}

/-- The actual symmetric and binary matrix factors of the proposed quotient. -/
abbrev QuotientModel :=
  Equiv.Perm (Fin 5) × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

end Janko4.LocalStructure.SymmetricLinear
