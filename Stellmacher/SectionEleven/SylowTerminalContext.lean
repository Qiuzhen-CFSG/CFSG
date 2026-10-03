module

public import Stellmacher.SectionFiveToSeven.GeneratedPairHypotheses
public import Stellmacher.SectionFiveToSeven.CosetGraphConstruction
public import Stellmacher.SectionFiveToSeven.CriticalPathExistence
public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionTen.GeneratedContext

/-!
# Terminal contexts for a Sylow pair

Ambient Hypothesis Two with S equal to an ambient Sylow subgroup supplies
the Section Seven hypotheses on the actual join of the two local members.
This module constructs its finite coset graph and a normalized critical path,
retaining the ambient hypothesis on H rather than asserting its inheritance.
The common subgroup is a Sylow of the join by Sylow restriction, and its image
is the original Sylow of H.

The proof uses `HypothesisTwo.generatedSectionSevenHypotheses`, which transports
the intrinsic local-family properties and (5.3), then the existing coset-graph
and critical-path existence theorems. The commutator split gives adapters to
the generated Section Eight and Nine contexts; critical length three gives
Section Ten. These adapters preserve the exact graph and path. They assert
no numbered terminal conclusion or exceptional-type realization. In particular,
local normalizers remain in the join and ambient normalizers remain in H.

Source: Stellmacher, Sections Seven, Eight, Nine, and Ten openings and the
Sylow branch of Section Eleven, `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionEleven

open SectionsFiveToSeven Later

universe u

public structure SylowTerminalContext
    (H : Type u) [Group H] [Finite H]
    (S0 : Sylow 2 H) (P1 P2 : Subgroup H) where
  hypothesisTwo : HypothesisTwo H S0 (S0 : Subgroup H) P1 P2
  sectionSeven : SectionSevenHypotheses (P1 ⊔ P2 : Subgroup H)
    ((S0 : Subgroup H).subgroupOf (P1 ⊔ P2))
    (P1.subgroupOf (P1 ⊔ P2)) (P2.subgroupOf (P1 ⊔ P2))
  Γ : CosetGraphContext.{u,u} (P1 ⊔ P2 : Subgroup H)
    ((S0 : Subgroup H).subgroupOf (P1 ⊔ P2))
    (P1.subgroupOf (P1 ⊔ P2)) (P2.subgroupOf (P1 ⊔ P2))
  criticalPath : CriticalPath Γ

public theorem sylow_terminal_context
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (hyp : HypothesisTwo H S0 (S0 : Subgroup H) P1 P2) :
    Nonempty (SylowTerminalContext H S0 P1 P2) := by
  have h7 := hyp.generatedSectionSevenHypotheses
  obtain ⟨graph⟩ := exists_cosetGraphContext _ _ _ h7.generated
  obtain ⟨path⟩ := exists_criticalPath h7 graph
  exact ⟨⟨hyp, h7, graph, path⟩⟩

namespace SylowTerminalContext

variable {H : Type u} [Group H] [Finite H]
  {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
  (ctx : SylowTerminalContext H S0 P1 P2)

include ctx in
public theorem sylow_le_join : (S0 : Subgroup H) ≤ P1 ⊔ P2 :=
  ctx.hypothesisTwo.fiveOne.P1_mem.1.2.1.1.trans le_sup_left

@[expose] public def restrictedSylow : Sylow 2 (P1 ⊔ P2 : Subgroup H) :=
  S0.subtype ctx.sylow_le_join

public theorem restrictedSylow_coe :
    (ctx.restrictedSylow : Subgroup (P1 ⊔ P2 : Subgroup H)) =
      (S0 : Subgroup H).subgroupOf (P1 ⊔ P2) := rfl

public theorem restrictedSylow_map :
    (ctx.restrictedSylow : Subgroup (P1 ⊔ P2 : Subgroup H)).map
      (P1 ⊔ P2).subtype = (S0 : Subgroup H) :=
  Subgroup.map_subgroupOf_eq_of_le ctx.sylow_le_join

@[expose] public def toSectionEightContext
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ ≠ ⊥) :
    GeneratedSectionEightContext H S0 (S0 : Subgroup H) P1 P2 where
  hypothesisTwo := ctx.hypothesisTwo
  sectionSeven := ctx.sectionSeven
  Γ := ctx.Γ
  criticalPath := ctx.criticalPath
  commutator_ne := hcomm

@[expose] public def toSectionNineContext
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥) :
    GeneratedSectionNineContext H S0 (S0 : Subgroup H) P1 P2 :=
  GeneratedSectionNineContext.ofLocalContext ctx.hypothesisTwo
    { sectionSeven := ctx.sectionSeven
      Γ := ctx.Γ
      criticalPath := ctx.criticalPath
      commutator_eq := hcomm }

@[expose] public def toSectionTenContext
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥)
    (hlength : ctx.criticalPath.length = 3) :
    GeneratedSectionTenContext H S0 (S0 : Subgroup H) P1 P2 :=
  (ctx.toSectionNineContext hcomm).toTenContext hlength

end SylowTerminalContext

end Stellmacher.SectionEleven
