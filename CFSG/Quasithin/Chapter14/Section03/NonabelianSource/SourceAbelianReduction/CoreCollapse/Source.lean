module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionCore
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionCoreCollapse
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionRQ
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionComponents
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionModelSieve
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionOddCore
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionAlternating
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionFixedResidual
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionComponentAction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.ResidualFusion

/-!
# Final assembly of the opposite-centralizer contradiction

The complete local construction supplies the literal three-factor involution,
all LocalGeometry clauses, and its global Sylow centralizer on the original T.
The RQ marking is proved from subgroup generation and orders. The actual
G₂(2) quotient then supplies residual fusion, which contradicts transfer.
`source_core_eq_U_of_quotient_recognition` retains only that quotient premise
for the constructed triple.

The original-point component catalogue, its reduced small-model alternatives,
both exact quotient-local markings, and the faithful quotient action on the
original layer are re-exported for the remaining model inspection. The odd
core and radical reductions exclude the alternating triple covers. The marked
local residual centralizer then excludes both alternating actions, leaving
inner actions in the remaining component catalogue. The fixed-residual and
quintic-centralizer bounds further exclude M₁₂ and A₈ central covers and
PSU₃(4), retaining six Lie alternatives, L₃(4) covers, the odd rows and M₁₁.

The earlier conditional interfaces are preserved. Global quotient recognition
remains with qt-e-14322-core-collapse; this module does not assert its existence
or split the whole centralizer.

Source: Aschbacher--Smith 14.3.22, printed pp.998--999, with the residual-cover
correction in docs/quasithin-proof-basis.md.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open OppositeCentralizer Recognition
variable {G : Type*} [Group G] [Finite G]

/-- Apply residual fusion and transfer to the actual marked centralizer.
The Sylow witness is constructed from the local geometry, not assumed anew. -/
theorem false_of_recognized_local_geometry {κ : GroupClass}
    (hG : IsSimpleQTKE κ G) {T : Sylow 2 G} {V : Subgroup G}
    (F : InvariantFlag T V 2) (L : Subgroup G)
    (hout : OutsidePointNonfusion F L) (z w : G)
    (h : LocalGeometry F L z w)
    (e : (ResidualFusion.C w ⧸ ResidualFusion.W w) ≃* Atlas.G2.Model (ZMod 2))
    (hRQ : ((T : Subgroup G) ⊓ ResidualFusion.C w) ⊓
      ((F.I₂ L).pCoreIn 2 ⊔ F.H.pCoreIn 2) ≤ ResidualFusion.J w) : False := by
  obtain ⟨_, S, hS⟩ := global_sylow_of_local_geometry F z w h.point h.mem_sylow
    h.involution h.nonfusion h.product_fusion h.omega_center h.local_sylow
  have hzV : z ∈ F.Vi 1 := h.point.symm ▸ mem_zpowers z
  have hz2 : orderOf z = 2 := by
    rw [← Nat.card_zpowers, ← h.point]
    simpa using F.card 1 (by decide)
  apply false_of_local_geometry_and_fusion hG F L z w h
  intro a ha hza
  exact ResidualFusion.controls_fusion_of_outsidePointNonfusion F L hout w z
    h.involution hz2 hzV e h.point_mem_global_commutator h.nonfusion h.product_fusion
    S (by rw [hS]; exact inf_le_left) (by rw [hS]; exact hRQ) a ha hza

/-- The literal triple construction now discharges every transfer premise;
only the global Sylow, quotient recognition and RQ marking remain explicit. -/
theorem false_of_recognized_triple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hout : OutsidePointNonfusion F (sourceResidual M Mc))
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)
    (ew : (ResidualFusion.C (tripleProduct d a) ⧸ ResidualFusion.W (tripleProduct d a)) ≃*
      Atlas.G2.Model (ZMod 2))
    (S : Sylow 2 (ResidualFusion.C (tripleProduct d a)))
    (hS : (S : Subgroup _).map (ResidualFusion.C (tripleProduct d a)).subtype =
      (T : Subgroup G) ⊓ ResidualFusion.C (tripleProduct d a))
    (hRQ : ((T : Subgroup G) ⊓ ResidualFusion.C (tripleProduct d a)) ⊓
      ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2) ≤ ResidualFusion.J (tripleProduct d a)) :
    False := by
  have h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hzV : z ∈ F.Vi 1 := s.point.symm ▸ mem_zpowers z
  have hz2 : orderOf z = 2 := by
    rw [← Nat.card_zpowers, ← s.point]
    simpa using F.card 1 (by decide)
  have hw1 : tripleProduct d a ≠ 1 := by
    intro hh
    exact source_triple_outside_transfer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
      (hh ▸ (localResidual F ⊔ (F.I₂ (sourceResidual M Mc)).pCoreIn 2).one_mem)
  apply source_false_of_triple_fusion hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
  exact ResidualFusion.controls_fusion_of_outsidePointNonfusion F (sourceResidual M Mc) hout
    (tripleProduct d a) z (s.involution_of_ne_one hc hw1).2 hz2 hzV ew
    (s.point_mem_global_commutator hc h.L_normalizes_seed)
    (source_triple_nonfusion hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s)
    (source_triple_product_fusion hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s)
    S (by rw [hS]; exact inf_le_left) (by rw [hS]; exact hRQ)

private theorem proper_supplement_of_core_ne
    {T : Sylow 2 G} {V : Subgroup G} (F : InvariantFlag T V 2)
    [IsElementaryAbelian 2 V] (dg : ClosureGeometry F)
    (hZ : F.ZU = F.Vi 1) (dU : QuaternionCentralProductData F.U)
    (hneq : F.H.pCoreIn 2 ≠ F.U) :
    F.Vi 1 < F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G) := by
  have hUQ : F.U ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hZU0 : F.ZU ≤ F.U := by
    rw [ZU, centerIn_eq_inf_centralizer]
    exact inf_le_left
  have hZC0 : F.ZU ≤ centralizer (F.U : Set G) := by
    rw [ZU, centerIn_eq_inf_centralizer]
    exact inf_le_right
  have hZU : F.Vi 1 ≤ F.U := (F.point_le_ZU (by decide)).trans hZU0
  have hZC : F.Vi 1 ≤ centralizer (F.U : Set G) :=
    (F.point_le_ZU (by decide)).trans hZC0
  let D := F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)
  have hZD : F.Vi 1 ≤ D := le_inf (hZU.trans hUQ) hZC
  have hDne : D ≠ F.Vi 1 := by
    intro hD
    apply hneq
    rw [Recognition.core_eq_U_sup_centralizer F dg hZ dU]
    change F.U ⊔ D = F.U
    rw [hD]
    exact sup_eq_left.mpr hZU
  exact lt_of_le_of_ne hZD hDne.symm

/-- The original core-collapse conclusion, with only the still-unproved
opposite geometry and its marked recognition explicit. This conditional
assembly is not a proof that those premises exist. -/
theorem source_core_eq_U_of_opposite_centralizers
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hout : OutsidePointNonfusion F (sourceResidual M Mc))
    (hopposite : CyclicTIInput F (sourceResidual M Mc) →
      ∃ z w : G, LocalGeometry F (sourceResidual M Mc) z w ∧
        Nonempty ((ResidualFusion.C w ⧸ ResidualFusion.W w) ≃* Atlas.G2.Model (ZMod 2)) ∧
        ((T : Subgroup G) ⊓ ResidualFusion.C w) ⊓
          ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2) ≤ ResidualFusion.J w) :
    F.H.pCoreIn 2 = F.U := by
  by_contra hneq
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg, he, _, _, _, _, _⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  have hproper := proper_supplement_of_core_ne F dg hZ dU hneq
  obtain ⟨z, w, hw, ⟨ew⟩, hRQ⟩ := hopposite
    (source_cyclicTIInput hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hproper)
  exact false_of_recognized_local_geometry hG F (sourceResidual M Mc) hout z w hw ew hRQ

/-- The complete local construction discharges the opposite-geometry premise
of core collapse. Only the actual global quotient and RQ recognition remain;
these are still obligations of qt-e-14322-core-collapse. -/
theorem source_core_eq_U_of_recognition
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hout : OutsidePointNonfusion F (sourceResidual M Mc))
    (hrecognition : ∀ z w : G, LocalGeometry F (sourceResidual M Mc) z w →
      Nonempty ((ResidualFusion.C w ⧸ ResidualFusion.W w) ≃* Atlas.G2.Model (ZMod 2)) ∧
      ((T : Subgroup G) ⊓ ResidualFusion.C w) ⊓
        ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2) ≤ ResidualFusion.J w) :
    F.H.pCoreIn 2 = F.U := by
  apply source_core_eq_U_of_opposite_centralizers
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hout
  intro hc
  obtain ⟨z,w,hlocal⟩ := source_opposite_local_geometry_of_cyclicTI
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc hself
  obtain ⟨ew,hRQ⟩ := hrecognition z w hlocal
  exact ⟨z,w,hlocal,ew,hRQ⟩

/-- All local geometry, the original Sylow and the RQ marking are discharged.
The sole remaining obligation is G₂(2) recognition for the constructed triple;
its proof and final source assembly remain with qt-e-14322-core-collapse. -/
theorem source_core_eq_U_of_quotient_recognition
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hout : OutsidePointNonfusion F (sourceResidual M Mc))
    (hrecognition : ∀ (_hc : CyclicTIInput F (sourceResidual M Mc)) (z d a : G),
      CubicTriple F (sourceResidual M Mc) z d a →
      Nonempty ((ResidualFusion.C (tripleProduct d a) ⧸ ResidualFusion.W (tripleProduct d a)) ≃*
        Atlas.G2.Model (ZMod 2))) :
    F.H.pCoreIn 2 = F.U := by
  apply source_core_eq_U_of_opposite_centralizers
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hout
  intro hc
  obtain ⟨z,d,a,s,_,_⟩ := source_triple_involution
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc
  obtain ⟨ew⟩ := hrecognition hc z d a s
  exact ⟨z,tripleProduct d a,
    source_triple_local_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself,
    ⟨ew⟩, source_triple_RQ_le_residual_product
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself ew⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse
