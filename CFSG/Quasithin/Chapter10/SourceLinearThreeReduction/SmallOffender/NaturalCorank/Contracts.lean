module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Inputs
public import CFSG.Quasithin.ChapterI.Section06To08.Basic

/-!
# The independent source steps in the natural corank-one exclusion

The diagonal-core theorem precedes the weak-closure calculation: its
hypotheses contain the literal natural geometry, point control and TI,
but no value of w. The local reduction is the corank-zero and nonzero-fixed
part analysis of 10.2.12. The final witness records the actual diagonal
involution and conjugate moved factor used in its terminal paragraph.

These definitions are outstanding obligations, not proofs of source
theorems. In particular, the later survivor record, which includes w=2,
cannot be used to discharge the diagonal-core obligation here.
Source: Aschbacher--Smith 10.2.10--12, printed pp.753--755.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02 ChapterE ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- The part of 10.2.11 consumed by the terminal contradiction, without
the later weak-closure and generation equalities. -/
def DiagonalCoreAt : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    SourceLinearThreeGeometry T D →
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) →
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ →
    IsTISubgroup ⁅D.fullModule,L⁆ →
    ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
    ∀ a b : G, a ∈ ⁅D.fullModule,L⁆ →
      b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom →
      a ≠ 1 → b ≠ 1 →
      a ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G) →
      b ∈ centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G) →
      a * b ∈ centerIn (T : Subgroup G) → orderOf (a * b) = 2 →
      D.fullModule ≤ (centralizer ({a * b} : Set G)).pCoreIn 2

/-- The earlier local reduction: zero corank is excluded, the full fixed
part vanishes, and the moved factor is a global TI subgroup. -/
def LocalReductionAt : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
    Configuration T D g → SourceLinearThreeGeometry T D →
    subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1 →
    subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) = 1 ∧
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ ∧
    IsTISubgroup ⁅D.fullModule,L⁆

/-- Original elements and subgroups in the last paragraph of 10.2.12.
The generated TI pair escapes its own two-core; the diagonal involution
centralizes the actual conjugate full module. The element `align` retains
the M-conjugation allowed by the source's choice of the central diagonal. -/
structure TerminalWitness {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G) where
  align : G
  align_mem : align ∈ D.maximalLocal
  exchange : G
  exchange_mem : exchange ∈ (T : Subgroup G)
  exchange_moves : exchange ∉ normalizer (L : Set G)
  first : G
  second : G
  first_mem : first ∈ ⁅D.fullModule,L⁆
  second_mem : second ∈ (⁅D.fullModule,L⁆).map (MulAut.conj exchange).toMonoidHom
  first_ne : first ≠ 1
  second_ne : second ≠ 1
  first_fixed : first ∈ centralizer
    (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G)
  second_fixed : second ∈ centralizer
    (((T : Subgroup G) ⊓ normalizer (L : Set G) : Subgroup G) : Set G)
  central : first * second ∈ centerIn (T : Subgroup G)
  order : orderOf (first * second) = 2
  conjugate_centralizes : D.fullModule.map (MulAut.conj (align * g)).toMonoidHom ≤
    centralizer ({first * second} : Set G)
  conjugator : G
  conjugator_eq : conjugator = align * g ∨ conjugator = (align * g) * exchange
  core_escape : ¬ ⁅D.fullModule,L⁆ ≤
    (⁅D.fullModule,L⁆ ⊔
      (⁅D.fullModule,L⁆).map (MulAut.conj conjugator).toMonoidHom).pCoreIn 2

/-- The terminal TI-pair construction takes the earlier local conclusions
explicitly, so it can be proved independently of their producer. -/
def TerminalConstructionAt : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
    Configuration T D g → SourceLinearThreeGeometry T D →
    subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) = 1 →
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ →
    IsTISubgroup ⁅D.fullModule,L⁆ → Nonempty (TerminalWitness T D g)

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
