module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.FamilySieve.SourceLists
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.Quasithin.Rank
public import Theory.Quasithin.KSections

/-!
# Applying A.3.8 after factoring out the ambient two-core

The quotient of an SQTK-group by its two-core is again SQTK and has
trivial two-core. The solvable-quotient correspondence preserves a component
and reflects its normality. The intrinsic quotient B/O₂(B) is isomorphic
to the image of B in that ambient quotient. Thus A.3.8(3) applies without
assuming that the original centralizer has trivial two-core.

Source: Aschbacher–Smith, A.3.4 and A.3.8, pp.42–46, applied to the
involution centralizer in the proof of 16.2.5 on p.1174. The classification
clause of A.3.8 remains an explicit earlier-source input.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.FamilySieve
universe u
variable {H : Type u} [Group H]

private theorem component_isCComponent {B : Subgroup H} (hB : IsComponent H B) :
    B.IsCComponent := by
  let := hB.2
  let := hB.2.simple
  have hnt : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  refine ⟨(nontrivial_iff_ne_bot B).mp hnt, inferInstance, hB.1, ?_⟩
  intro J hJ hne hp hs
  rcases hB.subnormal_dichotomy J hs with h | hc
  · exact h
  · exact (hne (bot_unique ((isPerfect_iff.mp hp).symm.le.trans
      ((commutator_mono hJ le_rfl).trans hc.le)))).elim

/-- The raw source list for the intrinsic quotient of a nonnormal component. -/
theorem sourceOrbitModel_quotient [Finite H] {K : GroupClass.{u}}
    (a38 : SourceA38Three K) (hH : IsSQTK K H)
    {B : Subgroup H} (hB : IsComponent H B) (hn : ¬ B.Normal) :
    SourceOrbitModel (B ⧸ pCore 2 B) := by
  have hc := component_isCComponent hB
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hQ : IsSQTK K (H ⧸ pCore 2 H) := by
    refine ⟨?_, ?_⟩
    · intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
        (hH.stronglyQuasithin p hp ho)
    · exact KGroup.isKGroup_of_quotient K hH.isKGroup
        (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  have hm := a38 _ hQ (pCore_quotient_pCore_eq_bot 2)
    (B.map (QuotientGroup.mk' (pCore 2 H))) (hc.map_quotient (pCore 2 H))
    (fun h => hn (cComponent_normal_of_quotient_normal hc (pCore 2 H) h))
  exact hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hc)

variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {z : G} {L : Subgroup G}

/-- The nonnormal centralizer component satisfies the raw quotient list. -/
theorem quotient_model (c : CounterexampleSetup K T z L) (a38 : SourceA38Three K) :
    SourceOrbitModel (L ⧸ pCore 2 L) := by
  have hB := sourceOrbitModel_quotient a38
    (c.global.involution_centralizer_sqtk c.localSetup.involution)
    c.localSetup.component.2 c.not_normal
  let e := (subgroupOfEquivOfLe c.localSetup.component.1).symm
  exact hB.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.FamilySieve
end
