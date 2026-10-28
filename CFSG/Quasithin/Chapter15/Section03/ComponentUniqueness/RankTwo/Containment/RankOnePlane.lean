module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.Definitions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.SmallModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryField
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.BorelGeometry
public import Stellmacher.ResidualCommutatorIdempotence

/-!
# The component actor in the rank-one alternatives

In the oriented configuration of 15.3.40, W = [V,O²(Y₊ ∩ L)] is a definite
plane contained in L. Relative normality of L in I and the actual normalizer
of Y₊ make M ∩ I preserve W. Residual commutator idempotence gives
[W,O²(Y₊ ∩ L)] = W, and the compatible natural action makes W a four-group
inside the specified Sylow subgroup.

Source 15.3.33(1) identifies M ∩ L with the actual Borel in both rank-one
families. Its action on W forces the fixed field to have order four. The
unitary Sylow-center identification then feeds the full local exclusion,
retaining Mc = C_G(Z), the residual construction, and the natural orthogonal
action. For PSL₂(4) and PSL₃(2), the self-centralizer calculation and
2-perfectness identify the actual component actor with A₄.

`component_model_and_actor_of_source` assembles all three alternatives.
Its remaining inputs are genuine earlier local conclusions and the oriented
plane, including the odd-core and component two-core facts used in the
15.3.37 Borel argument. It assumes no Borel identification, field bound,
small-model restriction, Sylow-center identity, or A₄ identification.
The final residual-product contradiction and Y₊ containment remain with the
15.3.40 assembly owner.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
15.3.40, printed p.1138, with 15.3.2--12 on pp.1121--1125 and 15.3.33--38
on pp.1134--1137. The unitary parameter is the fixed-field order throughout.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane
variable {G : Type*} [Group G] [Finite G]

private theorem oriented_plane_facts
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (h : Candidates.RankOneAction.Setup d.Yplus d.S d.M I L)
    [(L.subgroupOf I).Normal] (i : OrthogonalPlaneIndex)
    (hgen : ⁅d.V, componentFactor d.Yplus L⁆ = d.action.plane i) :
    IsKleinFour (d.action.plane i) ∧ d.action.plane i ≤ d.S ∧
      d.M ⊓ I ≤ normalizer (d.action.plane i : Set G) ∧
      ⁅d.action.plane i, componentFactor d.Yplus L⁆ = d.action.plane i := by
  let : IsElementaryAbelian 2 (d.action.plane i) :=
    d.action.elementary_of_le (d.action.plane_le i)
  let : Nontrivial (d.action.plane i) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [d.action.card_plane]; decide)
  refine ⟨⟨d.action.card_plane i, IsElementaryAbelian.exponent_eq_prime⟩,
    (d.action.plane_le i).trans (d.action.le_planeStabilizer d.T d.sylow_le
      (localModule_le d.T d.sylow_le) 1), ?_, ?_⟩
  · have hY : d.M ⊓ I ≤ normalizer (d.Yplus : Set G) :=
      h.normalizer_eq.symm.le.trans inf_le_right
    have hL : d.M ⊓ I ≤ normalizer (L : Set G) :=
      inf_le_right.trans (le_normalizer_of_normal_subgroupOf h.component_le)
    have hA := normalizes_componentFactor hY hL
    intro m hm
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [← hgen, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (d.action.normalizes hm.1),
      mem_normalizer_iff_map_conj_eq.mp (hA hm)]
  · let := d.action.elementary
    have hn : d.Yplus ⊓ L ≤ normalizer (d.V : Set G) :=
      (inf_le_left.trans (h.yplus_le.trans inf_le_left)).trans d.action.normalizes
    calc
      ⁅d.action.plane i, componentFactor d.Yplus L⁆ =
          ⁅⁅d.V, componentFactor d.Yplus L⁆, componentFactor d.Yplus L⁆ := by rw [hgen]
      _ = ⁅d.V, componentFactor d.Yplus L⁆ :=
        Stellmacher.commutator_twoResidualAmbient_idempotent d.V (d.Yplus ⊓ L)
          (IsElementaryAbelian.isPGroup 2 d.V) hn
      _ = d.action.plane i := hgen

/-- The conditional model-analysis step of 15.3.40 for the already oriented
component plane. The odd-core input is 15.3.11(8); `hcore` is the trivial
two-core conclusion supplied with the actual rank-one models in 15.3.37
(`SignedReduction.RankOneModels.rankOneInitialModel_and_core_of_triality_witnesses`).
The natural action and residual definitions are those of 15.3.2--10, and
`h` retains the genuine local conclusions through 15.3.33(1).

The orientation supplies only the component containment of the plane and
its generation from V. Its order, invariance, and self-generation are proved
here. The actual model alternatives are exhausted: both rank-one Borels
are identified using 15.3.33(1), the fields are restricted, and the unitary
case is excluded in the full local configuration. The conclusion constructs
an equivalence for the literal residual `O²(Y₊ ∩ L)`.

This is the model-analysis step, not the final containment `Y₊ ≤ L`:
that source-theorem assembly remains in `Containment.lean`. -/
theorem component_model_and_actor_of_source
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (h : Candidates.RankOneAction.Setup d.Yplus d.S d.M I L)
    [(L.subgroupOf I).Normal]
    (hMc : d.Mc = centralizer (d.Z : Set G))
    (hodd : pPrimeCore 2 I = ⊥) (hcore : pCore 2 L = ⊥)
    (i : OrthogonalPlaneIndex)
    (hgen : ⁅d.V, componentFactor d.Yplus L⁆ = d.action.plane i)
    (hWL : d.action.plane i ≤ L) (hm : RankOneAlternative L) :
    (ClassicalGroup.IsPSL L 2 4 ∨ ClassicalGroup.IsPSL L 3 2) ∧
      Nonempty (componentFactor d.Yplus L ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨hW, hWS, hWN, hself⟩ := oriented_plane_facts d h i hgen
  let := hW
  obtain ⟨P, hP⟩ := h.component_sylow
  have hYS : d.Yplus ⊔ d.S ≤ d.M ⊓ I :=
    le_inf (sup_le (h.yplus_le.trans inf_le_left) h.sylow_le) h.outside.1.2
  have hSY : d.S ≤ normalizer (d.Yplus : Set G) :=
    (le_sup_right.trans hYS).trans (h.normalizer_eq.symm.le.trans inf_le_right)
  have h33 : ∀ K : Subgroup G, K ≤ L →
      d.Yplus ⊔ d.S ≤ normalizer (K : Set G) →
      Theory.GroupTheory.generalizedFitting K = pCore 2 K → K ≤ d.M ⊓ I := by
    intro K hKL
    exact h.characteristic_two_containment K (hKL.trans h.orbit_eq.le)
  rcases hm with ⟨n, hn, _, hm⟩ | ⟨n, hn, heven, hm⟩ | hm
  · obtain ⟨hn2, he⟩ := linear_component_actor_alternating hn hm h.component_le
      h.sylow_le hYS h.component_outside P hP h33 hWS hWL hWN hSY hself
    exact ⟨Or.inl (by simpa only [hn2, show (2 : ℕ) ^ 2 = 4 from rfl] using hm), he⟩
  · obtain ⟨hB, _, _⟩ := h.unitary_borel_identification hodd hcore hn heven hm
    have hBW : borel L d.S ≤ normalizer (d.action.plane i : Set G) := by
      rw [hB]
      exact (le_inf inf_le_left (inf_le_right.trans h.component_le)).trans hWN
    obtain ⟨hn2, hcenter⟩ := unitary_plane_degree_eq_two hn hm P hP hWS hWL hW hBW
    have hm4 : ClassicalGroup.IsPSU L 3 4 := by
      simpa only [hn2, show (2 : ℕ) ^ 2 = 4 from rfl] using hm
    exact (UnitaryExclusion.exclusion_of_unitary_four_of_ambient_center d h hMc i
      hgen hm4 P hP hB.symm hWL hcenter).elim
  · exact ⟨Or.inr hm, binary_component_actor_alternating hm hWS hWL hSY
      (((componentFactor_le_left d.Yplus L).trans h.yplus_le).trans hWN) hself⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane
