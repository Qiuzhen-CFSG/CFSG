module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.PreGeometry.Contracts

/-!
# Centre reduction using the product-free residual preparation

The constructed residuals and their conjugate cores feed the existing centre
argument. Only the precise central-cover lifting output remains explicit;
it is the obligation of the separate CentralLift producer. Full automorphism
coverage is absent from the earlier centre theorem and enters only the final
literal product theorem. Neither theorem is asserted to be a completed source
result until the lifting output has been constructed.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
open Candidates.LinearCore
variable {G : Type*} [Group G] [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
variable {n : ℕ} {c : ProjectiveMarking L (2 ^ n)} {y : d.Yplus}

/-- Earlier centre control needs no full product with the original cubic actor
and no arbitrary-automorphism coverage. The lifting premise has a separate
intrinsic producer; it is not discharged by this reduction. -/
theorem precentre_of_prepared_residuals
    (g : PreparedResiduals d I L c y) (h : MatrixImage.SourceSetup d I L)
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥)
    (m : PrecentreCalculations d.S L (planeResidual d.M d.Y g.borel.W₂) g.borel.W₂) :
    center L = pCore 2 L ∧ centerImage L = g.borel.W₁ ∧
      d.S ⊓ centralizer (L : Set G) = g.borel.W₁ ∧
      I ⊓ centralizer (L : Set G) = g.borel.W₁ ∧
      (planeResidual d.M d.Y g.borel.W₂).pCoreIn 2 = d.S ⊓ L ∧
      d.Y.pCoreIn 2 = d.S ⊓ L ∧
      (d.Y : Set G) = (componentPart d.Yplus L : Set G) *
        (planeResidual d.M d.Y g.borel.W₂ : Set G) := by
  let b := g.borel
  let A := componentPart d.Yplus L
  let D := planeResidual d.M d.Y b.W₂
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le _ _
  have hMY : d.M ≤ normalizer (d.Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal _ _)
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  have hSY : d.S ≤ normalizer (d.Y : Set G) := hSM.trans hMY
  have hSD : d.S ≤ normalizer (D : Set G) :=
    normalizes_planeResidual (hSM.trans d.M.le_normalizer) hSY b.second_invariant
  have hMt : d.M.map (MulAut.conj b.t).toMonoidHom = d.M :=
    mem_normalizer_iff_map_conj_eq.mp (d.M.le_normalizer b.t_mem)
  have hYt : d.Y.map (MulAut.conj b.t).toMonoidHom = d.Y :=
    mem_normalizer_iff_map_conj_eq.mp (hMY b.t_mem)
  have hAD : A.map (MulAut.conj b.t).toMonoidHom = D := by
    change (componentPart d.Yplus L).map _ = _
    rw [g.residual.component_eq, planeResidual_map, hMt, hYt, b.first_interchange]
  have hDA : D.map (MulAut.conj b.t).toMonoidHom = A := by
    change (planeResidual d.M d.Y b.W₂).map _ = _
    rw [planeResidual_map, hMt, hYt, b.second_interchange, ← g.residual.component_eq]
  have hIL := (normal_subgroupOf_iff_le_normalizer h.component_le).mp g.normal
  obtain ⟨P, hP⟩ := h.sylow
  obtain ⟨hZ, hZW, hCS, hCI, hDcore, _⟩ := center_and_centralizers
    I L d.Y d.S d.V A D b.W₁ b.W₂ h.component_le h.component hIL P hP h.odd_core
    hSY hΩ hVY g.residual.generated b.t b.sylow_invariant hAD hDA b.second_interchange
    b.component_core (inf_le_left.trans hSD) m.normalizes_sylow m.commutator
    b.sylow_centralizer b.second_le_component_sylow
    ((planeResidual_le d.M d.Y b.W₂).trans (inf_le_right.trans inf_le_right))
    m.root_fixed m.sylow_fixed
  have hDY : D ≤ d.Y := (planeResidual_le _ _ _).trans inf_le_left
  have hYA : d.Y ≤ normalizer (A : Set G) := g.plus.ge.trans
    (ComponentIntersection.normalizes_intersectionResidual g.normalizes)
  have hDN : D ≤ normalizer (A : Set G) := hDY.trans hYA
  have hDcard : Nat.card D = Nat.card A := by
    rw [← hAD, card_map_of_injective (MulAut.conj b.t).injective]
  have hcore := core_of_residual_product g.residual.generated hDN b.component_core hDcore
    hDcard b.component_quotient g.quotient_card
  refine ⟨hZ, hZW, hCS, hCI, hDcore, hcore, ?_⟩
  change (d.Y : Set G) = (A : Set G) * (D : Set G)
  rw [g.residual.generated, coe_mul_of_right_le_normalizer_left A D hDN]

/-- The later I-product uses full marked coverage only after centre control.
This preserves the original conditional coverage contract separately from
the earlier theorem required by the kernel-modulo-centre argument. -/
theorem local_product_of_prepared_residuals
    (g : PreparedResiduals d I L c y) (h : MatrixImage.SourceSetup d I L)
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥)
    (m : PrecentreCalculations d.S L (planeResidual d.M d.Y g.borel.W₂) g.borel.W₂)
    (hcover : ∀ α : MulAut PSL(3,c.F), ∃ l ∈ L,
      ∃ z ∈ planeResidual d.M d.Y g.borel.W₂, ∃ s ∈ d.S, c.Realizes (l * z * s) α) :
    (I : Set G) = (L : Set G) * (planeResidual d.M d.Y g.borel.W₂ : Set G) *
      (d.S : Set G) := by
  obtain ⟨hZ, hZW, _, hCI, _⟩ := precentre_of_prepared_residuals g h hΩ hVY m
  let : IsQuasisimple (L.subgroupOf I) := h.component.2
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  have hYI : d.Y ≤ I := g.plus.ge.trans (le_sup_left.trans h.outside.1.2)
  exact product_of_marked_automorphism_coverage c hZ.ge h.component_le
    (((planeResidual_le _ _ _).trans inf_le_left).trans hYI)
    (le_sup_right.trans h.outside.1.2)
    ((normal_subgroupOf_iff_le_normalizer h.component_le).mp g.normal)
    (hCI ▸ hZW ▸ centerImage_le L) hcover

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
