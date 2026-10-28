module
public import Stellmacher.SectionOne.LemmaOneTwo
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Trivial two-core from faithful Sylow-fixed generation

If the translates of the fixed subgroup of a Sylow two-subgroup generate
an actual faithful module, the acting group's two-core is trivial. The
normal two-core lies in that Sylow subgroup; its fixed subgroup is invariant
under the whole acting group and therefore contains every generating
translate. Faithfulness then kills the two-core pointwise.

This abstract form of the local fixed-generation argument supplies the
Section One hypotheses for the next quotient module in Stellmacher (8.6),
printed p.42, source-(5). No elementary-abelian or finite-module assumption
is needed for this part of the argument.
-/

namespace Stellmacher.SectionOne
universe u v

public theorem twoCore_eq_bot_of_fixed_sylow_generation
    {G : Type u} {V : Type v} [Group G] [Finite G] [Group V]
    [MulDistribMulAction G V] (S : Sylow 2 G)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hgen : (⊤ : Subgroup V) = actionClosure G V (FixedPoints.subgroup S V)) :
    pCore 2 G = ⊥ := by
  have hNS : pCore 2 G ≤ (S : Subgroup G) := pCore_isPGroup.le_sylow_of_normal S
  have htop : (⊤ : Subgroup V) ≤ FixedPoints.subgroup (pCore 2 G) V := by
    rw [hgen, actionClosure]
    apply (Subgroup.closure_le _).mpr
    rintro point ⟨actor, vector, hvector, rfl⟩
    apply smul_mem_fixedPoints_of_normal
    intro n
    exact hvector ⟨n, hNS n.property⟩
  apply bot_unique
  intro actor hactor
  rw [← hfaith]
  rw [mem_fixingSubgroup_iff]
  intro vector _
  exact htop (Subgroup.mem_top vector) ⟨actor, hactor⟩

end Stellmacher.SectionOne
