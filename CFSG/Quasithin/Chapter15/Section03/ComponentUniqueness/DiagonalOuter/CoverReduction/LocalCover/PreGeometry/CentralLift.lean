module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.PreGeometry.CentralLift.CentreAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.PreGeometry.CentralLift.Projective
public import Theory.GroupTheory.CoprimeCentralizerDecomposition.CubicQuotient

/-!
# Central lifting before centre identification

The two-core of the opposite residual D fixes Z(L), so the centre action
factors through D/O₂(D), of order three. Coprime action and C_Z(L)(D)=1
therefore give [Z(L),D]=Z(L). The projective commutator calculation now lifts
to [S∩L,D]=S∩L. Comparing the genuinely conjugate residual cores then yields
O₂(D)=S∩L. Finally the marked fixed-subgroup calculations give both required
centralizer bounds, using the actual plane and Sylow centre throughout.

The theorem consumes ProjectiveRootData explicitly. Its independent producer
and the subsequent centre and I-product assemblies remain outside this module.
No full product with y, centre identity, or automorphism-coverage premise enters.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136, combined manuscript
of 1 March 2004 (PDF p.1153).
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
open Candidates.LinearCore
variable {G : Type*} [Group G] [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
variable {n : ℕ} {c : ProjectiveMarking L (2^n)} {y : d.Yplus}

/-- The actual opposite residual two-core acts trivially on Z(L). -/
theorem PreparedResiduals.opposite_core_centralizes_center
    (g : PreparedResiduals d I L c y) [Group.IsPerfect L]
    (hc : pCore 2 L ≤ center L) :
    (planeResidual d.M d.Y g.borel.W₂).pCoreIn 2 ≤ centralizer (centerImage L : Set G) := by
  let D := planeResidual d.M d.Y g.borel.W₂
  have hDY : D ≤ d.Yplus := ((planeResidual_le _ _ _).trans inf_le_left).trans g.plus.ge
  have hi := centralLift_twoSubgroup_inner g (D.pCoreIn 2)
    ((pCoreIn_le 2 D).trans hDY) (isPGroup_pCoreIn 2 D)
  intro a ha
  have haY := hDY (pCoreIn_le 2 D ha)
  let aY : d.Yplus := ⟨a, haY⟩
  have haH : aY ∈ (D.pCoreIn 2).subgroupOf d.Yplus := ha
  have hi' := hi (mem_map_of_mem (quotientAction g.normalizes c.equivalence) haH)
  have he : markedAction c ⟨a, g.normalizes haY⟩ =
      quotientAction g.normalizes c.equivalence aY := by
    apply MulEquiv.ext
    intro x
    obtain ⟨u, rfl⟩ := c.equivalence.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) u
    exact (markedAction_apply c ⟨a, g.normalizes haY⟩ l).trans
      (quotientAction_apply g.normalizes c.equivalence aY l).symm
  apply centralLift_inner_centralizes_center c hc ⟨a, g.normalizes haY⟩
  rw [he]
  exact hi'

/-- Lift the intrinsic projective calculations through the component centre.
The root data remain explicit; all central-cover lifting premises are discharged
from the prepared residuals and the exact earlier local hypotheses. -/
theorem precentreCalculations_of_projectiveRootData
    (g : PreparedResiduals d I L c y) (h : MatrixImage.SourceSetup d I L)
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥)
    (r : ProjectiveRootData d.S L (planeResidual d.M d.Y g.borel.W₂) g.borel.W₂ c) :
    PrecentreCalculations d.S L (planeResidual d.M d.Y g.borel.W₂) g.borel.W₂ := by
  let A := componentPart d.Yplus L
  let D := planeResidual d.M d.Y g.borel.W₂
  let b := g.borel
  have hIL := (normal_subgroupOf_iff_le_normalizer h.component_le).mp g.normal
  have hSI : d.S ≤ I := le_sup_right.trans h.outside.1.2
  have hDY : D ≤ d.Yplus := ((planeResidual_le _ _ _).trans inf_le_left).trans g.plus.ge
  have hDL : D ≤ normalizer (L : Set G) := hDY.trans g.normalizes
  have hDA : D ≤ normalizer (A : Set G) := hDY.trans
    (ComponentIntersection.normalizes_intersectionResidual g.normalizes)
  have hDQ : D ≤ normalizer (d.S ⊓ L : Subgroup G) := by
    rw [← b.component_core]
    exact hDA.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hc := center_eq_twoCore_in h.component_le h.component h.odd_core
  let : IsQuasisimple (L.subgroupOf I) := h.component.2
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  have hcore := g.opposite_core_centralizes_center hc.ge
  have hZnorm : D ≤ normalizer (centerImage L : Set G) :=
    hDL.trans (normalizer_le_normalizer_characteristic_image L (center L))
  have hZeq : centerImage L = L.pCoreIn 2 := congrArg (Subgroup.map L.subtype) hc
  have hZp : IsPGroup 2 (centerImage L) := hZeq ▸ isPGroup_pCoreIn 2 L
  have hZfixed := (g.center_fixed_eq_bot h hΩ hVY).2
  have hZcomm : ⁅centerImage L, D⁆ = centerImage L :=
    commutator_eq_of_twoCore_centralizes_of_quotient_card_three hZnorm hZp hcore g.opposite_quotient hZfixed
      (by obtain ⟨z, hz, hdiag⟩ := g.opposite_diagonal; exact ⟨z, hz, hdiag.1⟩)
  obtain ⟨P, hP⟩ := h.sylow
  have hS : IsPGroup 2 d.S := hP ▸ P.isPGroup'.map I.subtype
  have hZS : centerImage L ≤ d.S := by
    rw [hZeq]
    exact (pCoreIn_mono_of_normalizes h.component_le hIL).trans
      (hP ▸ pCoreIn_le_sylow I P)
  have hZQ : centerImage L ≤ d.S ⊓ L := le_inf hZS (centerImage_le L)
  have hcomm : ⁅d.S ⊓ L, D⁆ = d.S ⊓ L :=
    centralLift_commutator c r hDL hc.ge hDQ
      (by rw [← hZcomm]; exact commutator_mono hZQ le_rfl) g.opposite_diagonal
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le _ _
  have hMY : d.M ≤ normalizer (d.Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal _ _)
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  have hSD : d.S ≤ normalizer (D : Set G) :=
    normalizes_planeResidual (hSM.trans d.M.le_normalizer) (hSM.trans hMY) b.second_invariant
  have hMt : d.M.map (MulAut.conj b.t).toMonoidHom = d.M :=
    mem_normalizer_iff_map_conj_eq.mp (d.M.le_normalizer b.t_mem)
  have hYt : d.Y.map (MulAut.conj b.t).toMonoidHom = d.Y :=
    mem_normalizer_iff_map_conj_eq.mp (hMY b.t_mem)
  have hAD : A.map (MulAut.conj b.t).toMonoidHom = D := by
    change (componentPart d.Yplus L).map _ = _
    rw [g.residual.component_eq, planeResidual_map, hMt, hYt, b.first_interchange]
  have hQDcore : d.S ⊓ L ≤ D.pCoreIn 2 := by
    rw [← hcomm]
    exact commutator_le_twoCore (hS.to_le inf_le_left) (inf_le_left.trans hSD) hDQ
  have hDcore := (core_eq_and_invariant (MulAut.conj b.t) hAD b.component_core hQDcore).1
  refine ⟨hDQ, hcomm, centralLift_root_fixed c r hDL hc.ge g.opposite_diagonal, ?_⟩
  exact centralLift_sylow_fixed c r hc.ge (by rw [g.parameter]; decide)
    (hSI.trans hIL) (b.second_le_component_sylow.trans inf_le_left)
    (hDcore ▸ pCoreIn_le 2 D)
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
