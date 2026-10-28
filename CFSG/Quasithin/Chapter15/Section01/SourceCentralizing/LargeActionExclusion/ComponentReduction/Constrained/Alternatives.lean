module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Input
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry

/-!
# Contracts for the constrained source catalogue

These are the clauses of 15.1.20--22 consumed by constrained quotient
recognition. All block assertions use their genuine natural modules;
subnormality in `G₁` is retained in `d.L_component`. The
rank-one row retains the Borel and Thompson commutator; the L₃(2) row retains
the two literal parabolics; the A₇ row retains its partition subgroup. The
linear row identifies the actual two-core quotient and both parabolics using
one isomorphism. The cubic centralizers use the original embedded residual.

No theorem asserting this catalogue is supplied here. In particular these
contracts are not a proof of C.2.7 or 15.1.20--22. They let the catalogue and
the three block-exclusion proofs be developed independently, with final
discharge retained by the constrained-recognition assembly.

Source: Aschbacher--Smith 15.1.20--26, printed pp.1094--1102.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The exact cubic-centralizer identity used in 15.1.26. -/
def ConstrainedCentralizerIdentity (d : CaseIComponentData T M Mc V) : Prop :=
  d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
    (M ⊓ d.L).subtype) : Set G) = d.S ⊓ centralizer (d.L : Set G)

/-- The constrained rank-one row before 15.1.21 eliminates it. -/
structure ConstrainedRankOneAlternative (d : CaseIComponentData T M Mc V) : Prop where
  block : (∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5
  borel : d.ML = (normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype
  thompson : ⁅d.L, elementaryAbelianMaxJ d.S⁆ = d.L

/-- The L₃(2)-block clauses needed by 15.1.24(2). The parabolics are
images under the literal quotient map, and are distinct over `S_L`. -/
structure ConstrainedL3Alternative (d : CaseIComponentData T M Mc V) : Prop where
  block : IsSL3EvenBlock d.L 1
  marked_parabolic : IsLinearMaximalParabolic
    ((d.ML.subgroupOf d.L).map (QuotientGroup.mk' (pCore 2 d.L))) 3 (ZMod 2)
  selected_parabolic : IsLinearMaximalParabolic
    (((M ⊓ d.L).subgroupOf d.L).map (QuotientGroup.mk' (pCore 2 d.L))) 3 (ZMod 2)
  distinct : d.ML ≠ M ⊓ d.L
  centralizing : d.ML = d.L ⊓ centralizer (centralInvolutions T : Set G)
  centralizers : d.ConstrainedCentralizerIdentity

/-- The ordinary natural A₇-block and the actual `2³,1` partition subgroup
needed by 15.1.25(5). The permutation action factors through `L/O₂(L)`. -/
structure ConstrainedA7Alternative (d : CaseIComponentData T M Mc V) : Prop where
  block : IsAlternatingBlock d.L 7
  partition : ∃ e : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
    ∃ p : Partition 7 4 ![2, 2, 2, 1],
      let f := (alternatingGroup (Fin 7)).subtype.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L)))
      (d.SL.subgroupOf d.L).map f ≤ p.stabilizer ∧
        alternatingGroup (Fin 7) ⊓ p.stabilizer ≤ ((M ⊓ d.L).subgroupOf d.L).map f
  generated : (M ⊓ d.L) ⊔ d.ML = d.L

/-- A proper flag parabolic under a specified isomorphism of the literal
two-core quotient. Both source parabolics use that same isomorphism. -/
def ConstrainedLinearParabolic (d : CaseIComponentData T M Mc V) {n : ℕ}
    (e : (d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (P : Subgroup G) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ f : LinearFlag (ZMod 2) n k,
    ((P.subgroupOf d.L).map (QuotientGroup.mk' (pCore 2 d.L))).map e.toMonoidHom =
      f.stabilizer

/-- The constrained source alternatives, retaining the rank-one row until
its independent 15.1.21 exclusion. The two surviving linear degrees are
actual matrix-group isomorphisms, not family tags. -/
inductive ConstrainedAlternatives (d : CaseIComponentData T M Mc V) : Prop
  | rankOne (source : d.ConstrainedRankOneAlternative)
  | linearThree (source : d.ConstrainedL3Alternative)
  | alternatingSeven (source : d.ConstrainedA7Alternative)
  | alternatingSix (block : IsAlternatingBlock d.L 6)
      (centralizers : d.ConstrainedCentralizerIdentity)
  | g2 (block : ChapterC.IsG2TwoBlock d.L)
      (centralizers : d.ConstrainedCentralizerIdentity)
  | linear (n : ℕ) (degree : n = 4 ∨ n = 5)
      (equiv : (d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
      (marked_parabolic : d.ConstrainedLinearParabolic equiv d.ML)
      (selected_parabolic : d.ConstrainedLinearParabolic equiv (M ⊓ d.L))
      (generated : (M ⊓ d.L) ⊔ d.ML = d.L)

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
