module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceIrreducible
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Consequences
public import CFSG.Quasithin.ChapterE.Section06.Defs

/-!
# The ambient weak-closure setup for the invariant non-FF orbit

The multiple-overgroup hypothesis kills the fixed seed space. The source TI
theorem consequently applies to the original orbit when the seed is invariant.
Uniqueness of LT and the literal equality C_T(W)=O₂(LT) supply E.6.1's relative
maximality clause. Normality is only inside T, and TI is only under N_G(L).

This constructs the ambient input for the remaining 7.3--7.4 parameter
bounds; it assumes no rank, fixed-codimension or centralizer-containment bound.
Source: Aschbacher--Smith, E.6.1, 3.2.2 and 7.0.2, printed pp.244--245,579,695,
as applied to the chosen orbit in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- E.6.1 on the original chosen orbit, using the invariant seed and the
actual multiple-overgroup hypothesis. The TI clause is relative to N_G(L). -/
theorem sourceOrbit_hypothesisE61_of_invariant_nonFF
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) D.sourceOrbit := by
  have h127 := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hu := (D.fundamentalSetup h.toHypothesis1221).lemma_3_2_3_uniqueness h127
  have hM : IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
        N = normalizer (L : Set G) := by
    simpa only [Chapter3.Section02.FundamentalSetup.maximalLocal,
      Chapter3.Section02.localJoin, D.localOrbit_eq] using And.intro hu.1 hu.2.2
  have hcore : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [D.sourceOrbit_eq]
    exact D.orbit_centralizer h.toHypothesis1221
  have hjoin : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer D.sylow_normalizes_component
  have hnorm : L ⊔ (T : Subgroup G) ≤ normalizer (D.sourceOrbit : Set G) :=
    sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes
  refine ⟨h.simpleQTKE, hM.1, D.sylow_normalizes_component,
    D.sourceOrbit_weakClosure_setup.nontrivial, inferInstance,
    D.sourceOrbit_weakClosure_setup.le_sylow,
    normal_subgroupOf_of_le_normalizer D.sourceOrbit_weakClosure_setup.normalizes, ?_, ?_⟩
  · intro g hg
    have ht := D.ti_of_centralizer_eq_bot h.toHypothesis1221
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1 g hg
    rwa [hV] at ht
  · intro N hN hle
    apply hM.2 N hN
    apply le_trans _ hle
    change L ⊔ (T : Subgroup G) ≤
      ((normalizer (L : Set G)) ⊓ normalizer (D.sourceOrbit : Set G)) ⊓
        normalizer (((T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) : Subgroup G) : Set G)
    rw [hcore]
    exact le_inf (le_inf hjoin hnorm) ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
