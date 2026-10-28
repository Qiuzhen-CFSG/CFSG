module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.Representatives
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.CyclicCoverage.ThreeSylow

/-!
# Cyclic conjugacy coverage for the two marked odd elements

A checked subgroup of order 27 contains a conjugate of every three-element.
Its noncentral elements fuse to the marked regular word, while its central
elements have centralizers divisible by 27 and therefore are not regular.
The marked seven-word has order seven; since seven divides 6048 only once,
Sylow conjugacy proves conjugacy of all seven-subgroups, without identifying
the two classes of seven-elements.

The concluding consumer discharges `ConjugacyCoverage` in the literal
odd-displacement assembly. The independent vertex and cycle matrix samples
remain explicit. Source: Guralnick–Malle, Classification of 2F-modules I,
Proposition 4.3, pp.10–11, with the additional degree-32 branch retained by
the parent interface.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements
open Subgroup Representation
open G2DerivedPermutationFiltration.VertexCoordinates
open CyclicCoverageCertificate
open scoped Pointwise

/-- Exact order in the actual derived group of the published seven-word. -/
theorem marked_seven_order : orderOf (groupHom sevenWord) = 7 := by
  simpa only [sevenWord, map_mul, map_inv, groupHom_of] using seven_order

private theorem seven_coverage (x : Derived) (hx : orderOf x = 7) :
    ∃ g : Derived, zpowers x = zpowers (g * groupHom sevenWord * g⁻¹) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : MulAction Derived (Sylow 7 Derived) := Sylow.mulAction
  let : MulAction.IsPretransitive Derived (Sylow 7 Derived) :=
    Sylow.isPretransitive_of_finite
  have sylow_card (y : Derived) (hy : orderOf y = 7) :
      Nat.card (zpowers y) = 7 ^ (Nat.card Derived).factorization 7 := by
    rw [Nat.card_zpowers, hy, card_actor]
    decide +kernel
  let P : Sylow 7 Derived := Sylow.ofCard (zpowers (groupHom sevenWord))
    (sylow_card _ marked_seven_order)
  let Q : Sylow 7 Derived := Sylow.ofCard (zpowers x) (sylow_card x hx)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Derived P Q
  refine ⟨g, ?_⟩
  have he := congrArg (fun S : Sylow 7 Derived => (S : Subgroup Derived)) hg
  change (zpowers (groupHom sevenWord)).map (MulAut.conj g).toMonoidHom = zpowers x at he
  rw [MonoidHom.map_zpowers] at he
  exact he.symm

/-- The required coverage on the literal root-word marking, with regularity retained. -/
theorem conjugacyCoverage : ConjugacyCoverage := by
  constructor
  · intro x hx
    obtain ⟨g, hg⟩ := isConj_iff.mp (regular_three_fusion x hx.1 hx.2)
    refine ⟨g, ?_⟩
    simpa only [regularWord, map_mul, groupHom_of] using congrArg zpowers hg.symm
  · exact seven_coverage

/-- The group certificate discharges coverage; both independent matrix calculations
remain explicit for the parent's final assembly. -/
theorem oddDisplacementBounds_of_samples
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hd : 8 < Module.finrank (ZMod 2) V) (hv : VertexSamples) (hc : CycleSamples) :
    OddDisplacementBounds σ :=
  oddDisplacementBounds_of_certificates σ hd conjugacyCoverage hv hc

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements
