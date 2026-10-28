module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.ComponentBorels.LinearThree.Construction
public import Theory.SpecificGroups.PSL3.CartanActions.RootTorusControl.Transport


/-!
# Ordinary PSL₃ Borel commutator control in E.6.25

Choose the compatible torus `diag(a,1,a⁻¹)` in an actual marked PSL₃ model.
It has the same induced action on V as X and retains every clause of the
regular cyclic section. An odd actor with commuting action image normalizes
U, hence L and L ∩ M by the earlier relative C-component theorem. Its
commutator with the chosen torus centralizes V, and therefore the highest-root
group. The transported matrix calculation puts that commutator in O₂(L ∩ M).

All model placement and automorphism-coverage premises are discharged.
The full centralizer C_L(V) is never assumed to be a two-group.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11(3b)
and the factor-count paragraph of E.6.25, printed pp.249–250,255.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
open Components
variable {G : Type*} [Group G] [Finite G]

/-- The ordinary PSL₃ branch of the component Borel calculation in E.6.25.
The compatible root torus is constructed and all its section clauses proved. -/
theorem componentBorel_lift_linear_three
    {K : GroupClass} {T : Sylow 2 G} {M V U Q L X : Subgroup G}
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hLC : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hX : RegularCyclicSection M V U X)
    (b : BorelAlternative M V U L (subgroupCorank V U))
    (t : TorusAction M V L X (subgroupCorank V U))
    (hn : 1 < subgroupCorank V U)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (iso : ClassicalGroup.IsPSL L 3 (2 ^ subgroupCorank V U)) :
    ComponentBorelLiftConclusion M V U L X := by
  let _ := h.elementary
  obtain ⟨Y,hYL,hY,hi,F,_,_,_,hF,e,hB,hZ,heY⟩ :=
    exists_linear_three_torus_placement h hU hL hX b t hn hVL hQ S hS iso
  refine ⟨Y,hYL,hY,hi,?_⟩
  intro A hA ho hc
  have hAU : A ≤ normalizer (U : Set G) := by
    have hh := normalizes_fixed_of_image_commutes hY
      (A.subgroupOf (normalizer (V : Set G))) hc
    rwa [map_subgroupOf_eq_of_le hA] at hh
  have hAL := odd_normalizes_local_component h earlier hU hLC hAU ho
  have hAB := odd_normalizes_local_intersection h earlier hU hY hLC hA ho hc
  have hkernel := cross_commutator_le_kernel hA
    (hY.contained.trans (inf_le_left.trans inf_le_right)) hc
  exact Matrix.PSL3.CartanActions.RootTorusControl.commutator_le_core_of_model
    F (by omega) hF L (L ⊓ M) A Y e hB heY.le hAL hAB
    (hkernel.trans (centralizer_le hZ))

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
