module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.Context
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.CentralFactors
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.TwoCore
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.Rank
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.SecondComponent
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion

/-!
# The natural-component closure argument of B.5.9

The literal natural seed U=[C_V(O₂(LA)),L] equals W=[V,L]. If it were
proper, the second-component construction would produce a distinct natural
component with nontrivial cross action and the genuine residual placement.
The chief-factor estimates and the two-component rank bound then force
equality in the source inequalities. The local two-core calculation and
the central quotient C_V(B)/U give the contradictory factor counts.
Throughout, U=[C_V(B),L]; possible central summands are retained.

The only earlier-source input beyond `Setup` is universal full Theorem A
(`ChapterA.Section02.TheoremA`), applied to the actual SQTK cover in the
second-component construction. `Setup.preliminary` is the universally
quantified preliminary component-action conclusion. Its producer is
`qt-b05-component-preliminary-actions`; the B.5.9–10 assembly owner
`qt-b05-induction-component-reduction` must discharge both inputs and
transport the natural action along the proved equality. No counterexample
condition or further numerical or classification premise is needed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The final natural-component argument of B.5.9: the actual LA-invariant
natural seed is the whole moved space. Proper containment constructs the
second component, whose chief-factor contradiction has no remaining premises. -/
theorem seed_eq_moved {K : GroupClass.{u}} {A L : Subgroup G}
    (setup : Setup ρ K A)
    (theoremA : ∀ (D : Type u) [Group D] [Finite D], ChapterA.Section02.TheoremA K D)
    (hL : IsComponent G L) (hLA : ⁅L, A⁆ = L)
    (seed : NaturalSeed ρ A L) : seed.space.toSubmodule = moved ρ L := by
  by_contra hne
  have hproper := lt_of_le_of_ne (seed_le_moved ρ seed) hne
  obtain ⟨d⟩ := secondComponent_of_proper_seed ρ setup theoremA hL hLA seed hproper
  exact secondComponent_false ρ setup hL hLA seed d

/-- The closure equality on the literal source subspace, with O₂ taken
inside LA and then mapped to G. The seed supplies the genuine natural model. -/
theorem naturalSeedSpace_eq_moved {K : GroupClass.{u}} {A L : Subgroup G}
    (setup : Setup ρ K A)
    (theoremA : ∀ (D : Type u) [Group D] [Finite D], ChapterA.Section02.TheoremA K D)
    (hL : IsComponent G L) (hLA : ⁅L, A⁆ = L)
    (seed : NaturalSeed ρ A L) : naturalSeedSpace ρ L A = moved ρ L :=
  seed.space_eq.symm.trans (seed_eq_moved ρ setup theoremA hL hLA seed)

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
