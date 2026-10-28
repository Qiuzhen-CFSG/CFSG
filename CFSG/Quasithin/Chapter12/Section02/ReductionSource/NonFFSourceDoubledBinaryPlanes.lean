module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlanes
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinarySpans

/-!
# The binary paired-plane reduction on the original chosen orbit

The unchanged automizer coordinates retain the original conjugator and both
seed axes. They transport the two-dimensional paired planes and their
component conjugacy into the ambient group. Control of the centralizer of
one such plane gives r ≥ 2. The exact maximal-obstruction action premise
from E.6.11 then gives r ≥ 3, discharging the geometry in the reduction
paragraph of source 7.7.1.

The one-plane centralizer containment from 7.7.3 and the E.6.11 structural
premise remain explicit and belong to the final assembly owner
qt-d-1222-nonff-doubled. The theorem is a conditional reduction, not a proof
of the full binary exclusion. No identification of the seed with the orbit
is used.
Source: Aschbacher–Smith, 7.7.1–3, printed pp.703–704.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE
open BinaryLinearThree
open DoubledBinaryPlanes
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original chosen orbit reduces its r > 2 argument to one literal paired
plane and the exact maximal-obstruction action premise from E.6.11. The same
original conjugator, both seed axes and the original component marking are retained. -/
theorem sourceOrbit_binary_pairedPlane_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ q : L →* Group, Function.Surjective q ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ l w, E (doubledSeedAction L D.sourceOrbit
          D.sourceOrbit_component_normalizes l w) = NaturalDual.action (q l) (E w)) ∧
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∀ v : Vector, ∀ f : Module.Dual (ZMod 2) Vector, f v = 1 →
          rank (ambientPlane D.sourceOrbit E v f) = 2 ∧
          (∀ v' f', f' v' = 1 →
            ∃ l : L, (ambientPlane D.sourceOrbit E v f).map (MulAut.conj (l : G)).toMonoidHom =
              ambientPlane D.sourceOrbit E v' f') ∧
          (centralizer (ambientPlane D.sourceOrbit E v f : Set G) ≤ normalizer (L : Set G) →
            2 ≤ globalR D.sourceOrbit ∧
            ((∀ U ∈ ChapterE.Section06.obstructionFamily (normalizer (L : Set G)) D.sourceOrbit,
              (∀ X : Subgroup G, U < X → X ≤ D.sourceOrbit →
                centralizer (X : Set G) ≤ normalizer (L : Set G)) →
              1 < subgroupCorank D.sourceOrbit U →
              ∃ x ∈ normalizer (L : Set G) ⊓ centralizer (U : Set G),
                x ∉ centralizer (D.sourceOrbit : Set G)) →
              3 ≤ globalR D.sourceOrbit)) := by
  obtain ⟨t,ht,hnt,q,hq,E,a,hE,_,_,hcov,hV,hVt⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  have hmark : ∀ l w, E (automizerRepresentation D.sourceOrbit
      (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
        (inclusion D.sourceOrbit_component_normalizes l)) w) = NaturalDual.action (q l) (E w) := hE
  have hN := D.sourceOrbit_normalizer_eq_of_markedDoubled h hd
  refine ⟨t,ht,hnt,q,hq,E,hE,hV,hVt,?_⟩
  intro v f hfv
  refine ⟨ambientPlane_rank D.sourceOrbit E v f hfv,?_,?_⟩
  · intro v' f' hfv'
    exact ambientPlane_transitive D.sourceOrbit L D.sourceOrbit_component_normalizes E q
      hmark hq v v' f f' hfv hfv'
  · intro hC
    have hp := all_plane_centralizers D.sourceOrbit L D.sourceOrbit_component_normalizes E q
      hmark hq v f hfv (hN.symm ▸ hC)
    refine ⟨two_le_globalR_of_planes D.sourceOrbit E hp,?_⟩
    intro hact
    have h61 := D.sourceOrbit_hypothesisE61_of_markedDoubled h hd
    rw [← hN] at h61 hact
    exact three_le_globalR_of_planes D.sourceOrbit E a hcov h61 hact hp

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
