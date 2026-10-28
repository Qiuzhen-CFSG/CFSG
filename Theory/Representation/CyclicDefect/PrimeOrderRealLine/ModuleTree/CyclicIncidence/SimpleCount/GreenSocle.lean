module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount.GreenSocle.Basic

/-!
# Assembling the Green-socle map on actual simple classes

Given the explicit Green restriction and local serial-module prerequisites,
choose the actual socle of each Green correspondent. Stable orthogonality makes
these simples pairwise inequivalent. Inverse Green correspondence supplies a
nonzero map from every local simple to one of the correspondents, identifying
it with that correspondent's socle. The supplied decomposition then identifies
the resulting bijection with the intrinsic ambient simple-class set.

This is the assembly step of Feit VII.3.11--12, not a proof of the two missing
prerequisites. The source theorem with only `PrimeOrderInput`, the supplied
`Decomposition`, and normalizer primitivity remains to be assembled after those
prerequisites are constructed. No numerical simple count is assumed here.

Source: Feit, *The Representation Theory of Finite Groups*, VII.3.11--12,
printed pp.285--286; VII.4, printed p.290.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount
open GreenSocle

variable {K G : Type*} [Field K] [Group G] [Finite G] {p m n : ℕ}
    {d : ModularBlock.PrimeBlockConstruction.PrimeCongruenceBlockData p G}
    {residue : Localization.AtPrime d.primeIdeal →+* K} {L : CyclicRootLift K m}

/-- Conditional assembly from actual Green modules, stable maps, and their socles. -/
def simpleClassEquiv_of_greenSocleInputs (a : Decomposition d residue L n) (P : Sylow p G)
    (F : GreenFamily a P) (S : LocalSocleTheory (normalizerSelector d residue P)) :
    SimpleClass (reducedPrincipal d residue) ≃
      SimpleClass (normalizerSelector d residue P) := by
  classical
  let s (i : Fin n) := Classical.choice (S.exists_socle (F.model i))
  refine (decompositionSimpleClassEquiv a).symm.trans
    (simpleClassEquivOfFamily _ (fun i => (s i).simple.degree)
      (fun i => (s i).simple.rep) (fun i => (s i).simple.irreducible)
      (fun i => (s i).simple.inBlock) ?_ ?_)
  · intro i j hij
    refine ⟨fun f => ?_⟩
    rcases S.overlap (F.model i) (F.model j) (s i) (s j) ⟨f⟩ with h | h
    · exact F.orthogonal hij h
    · exact F.orthogonal hij.symm h
  · intro k ρ hirr hin
    let T : SimpleModel (normalizerSelector d residue P) := ⟨k, ρ, hirr, hin⟩
    obtain ⟨i, hi⟩ := F.coverage T
    obtain ⟨f, hf⟩ := hi.exists_nonzero
    exact ⟨i, (s i).equiv_of_nonzero T f hf⟩


/-- The exact simple-class equivalence conclusion, with both module-theoretic
prerequisites still explicit. Their existence is required for source assembly. -/
theorem nonempty_simpleClassEquiv_of_greenSocleInputs
    (a : Decomposition d residue L n) (P : Sylow p G)
    (F : Nonempty (GreenFamily a P))
    (S : LocalSocleTheory (normalizerSelector d residue P)) :
    Nonempty (SimpleClass (reducedPrincipal d residue) ≃
      SimpleClass (normalizerSelector d residue P)) := by
  obtain ⟨F⟩ := F
  exact ⟨simpleClassEquiv_of_greenSocleInputs a P F S⟩

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount
