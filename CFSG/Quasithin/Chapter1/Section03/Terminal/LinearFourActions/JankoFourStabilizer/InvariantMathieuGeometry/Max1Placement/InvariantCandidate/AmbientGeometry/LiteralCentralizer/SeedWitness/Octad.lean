module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralCentralizer.SeedWitness.Duads
import all Theory.Mathieu.M24.LocalGeometry.LinearFourCore

/-!
# A duad in the core center of an octad residual

The octad stabilizer is perfect and the kernel of max1 → M₂₄ is abelian.
Thus the quotient of the octad preimage by its solvable residual is
abelian: the preimage's commutators belong to the residual. Two-transitivity
on the octad expresses a duad vector as one such commutator. The octad
two-core fixes its endpoints, so the vector centralizes the two-core of
the residual, and its kernel membership puts it inside that two-core.

The private-scope import is used only to evaluate the unexposed restriction
map `LinearFourCore.alternatingAction` on octad points. No shared API is
changed. All permutation and group-structure facts are its proved public
theorems.

Source: the local E₂₁₁.M₂₄ geometry in GLS3 Table 5.3i and the octad
E₁₆.A₈ action in Table 5.3e, used for Aschbacher–Smith A.3.12(17).
-/

public section

open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry.SeedDuads
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry

attribute [local irreducible] Janko4.modelGroup certifiedMathieuSubgroup

private theorem residual_sup_core (O : Octad) :
    literalOctadResidual O ⊔ pCore 2 certifiedMathieuSubgroup = literalOctadPreimage O := by
  rw [← literalMathieuMap_ker, ← comap_map_eq, literalOctadResidual_image]
  rfl

private theorem core_le_preimage (O : Octad) :
    pCore 2 certifiedMathieuSubgroup ≤ literalOctadPreimage O :=
  (residual_sup_core O) ▸ le_sup_right

private theorem commutator_mem_residual (O : Octad) (x y : certifiedMathieuSubgroup)
    (hx : x ∈ literalOctadPreimage O) (hy : y ∈ literalOctadPreimage O) :
    ⁅x, y⁆ ∈ literalOctadResidual O := by
  let H := literalOctadPreimage O
  let N := solvableResidual H
  let V := (pCore 2 certifiedMathieuSubgroup).subgroupOf H
  let : IsElementaryAbelian 2 (pCore 2 certifiedMathieuSubgroup) := literalCore_elementary
  let : IsMulCommutative V := inferInstance
  have htop : N ⊔ V = ⊤ := by
    apply (map_injective H.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (core_le_preimage O),
      ← MonoidHom.range_eq_map, range_subtype]
    exact residual_sup_core O
  have hcomm : commutator H ≤ N :=
    Normal.commutator_le_of_self_sup_commutative_eq_top htop inferInstance
  exact mem_map_of_mem H.subtype (hcomm
    (commutator_mem_commutator (mem_top (⟨x, hx⟩ : H)) (mem_top (⟨y, hy⟩ : H))))

private theorem core_intersection_le (B : Subgroup certifiedMathieuSubgroup) :
    (pCore 2 certifiedMathieuSubgroup) ⊓ B ≤ B.pCoreIn 2 := by
  have h : (pCore 2 certifiedMathieuSubgroup).subgroupOf B ≤ pCore 2 B :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  simpa only [subgroupOf_map_subtype, pCoreIn] using map_mono (f := B.subtype) h

/-- Duads on the seed octad are fixed by the embedded core of its preimage residual. -/
theorem duad_centralizes_seed_core (i j : LinearFourCore.seedOctad.val) :
    duad i.val j.val ∈ centralizer
      ((literalOctadResidual LinearFourCore.seedOctad).pCoreIn 2 :
        Set certifiedMathieuSubgroup) := by
  intro x hx
  have hxi : literalMathieuMap x ∈ (octadStabilizer LinearFourCore.seedOctad).pCoreIn 2 := by
    rw [← literalOctadResidual_coreImage]
    exact mem_map_of_mem literalMathieuMap hx
  obtain ⟨y, hy, he⟩ := hxi
  have hfix := (LinearFourCore.mem_action_ker _ y).mp (LinearFourCore.core_le_kernel hy)
  have hc := conjugate_duad x i.val j.val
  rw [← he] at hc
  change x * duad i.val j.val * x⁻¹ = duad ((y : M24) • i.val) ((y : M24) • j.val) at hc
  rw [hfix _ i.property, hfix _ j.property] at hc
  have hm := congrArg (· * x) hc
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

/-- Two-transitivity on the octad expresses each duad as a commutator in its preimage. -/
theorem duad_mem_seed_residual (i j k : LinearFourCore.seedOctad.val)
    (hik : i ≠ k) (hjk : j ≠ k) :
    duad i.val j.val ∈ literalOctadResidual LinearFourCore.seedOctad := by
  classical
  let : MulAction.IsMultiplyPretransitive
      (alternatingGroup LinearFourCore.seedOctad.val) LinearFourCore.seedOctad.val
      (Nat.card LinearFourCore.seedOctad.val - 2) :=
    alternatingGroup.isMultiplyPretransitive _
  have ht : MulAction.IsMultiplyPretransitive
      (alternatingGroup LinearFourCore.seedOctad.val) LinearFourCore.seedOctad.val 2 :=
    MulAction.isMultiplyPretransitive_of_le
      (n := Nat.card LinearFourCore.seedOctad.val - 2)
      (by rw [LinearFourCore.seed_card]; decide) (Nat.sub_le _ _)
  obtain ⟨a, ha, hk⟩ := MulAction.is_two_pretransitive_iff.mp ht hik hjk
  obtain ⟨h, hh⟩ := LinearFourCore.alternatingAction_surjective a
  have hi : (h : M24) • i.val = j.val := by
    have he := congrArg (fun b : alternatingGroup LinearFourCore.seedOctad.val =>
      (b.val i).val) hh
    exact he.trans (congrArg Subtype.val ha)
  have hkeep : (h : M24) • k.val = k.val := by
    have he := congrArg (fun b : alternatingGroup LinearFourCore.seedOctad.val =>
      (b.val k).val) hh
    exact he.trans (congrArg Subtype.val hk)
  obtain ⟨x, hx⟩ := literalMathieuMap_surjective h.val
  have hxp : x ∈ literalOctadPreimage LinearFourCore.seedOctad := by
    change literalMathieuMap x ∈ octadStabilizer LinearFourCore.seedOctad
    rw [hx]
    exact h.property
  have he : ⁅x, duad i.val k.val⁆ = duad j.val i.val := by
    change x * duad i.val k.val * x⁻¹ * (duad i.val k.val)⁻¹ = _
    rw [conjugate_duad, hx, hi, hkeep, duad_inv, duad_mul]
  have hm := commutator_mem_residual LinearFourCore.seedOctad x (duad i.val k.val)
    hxp (core_le_preimage _ (duad_mem_core _ _))
  rw [he] at hm
  rwa [duad_symm j.val i.val] at hm


/-- A conjugate of the literal seed lies in the core center of the seed-octad residual. -/
theorem seed_octad_witness : ∃ g : certifiedMathieuSubgroup,
    g * literalCentralizerSeed * g⁻¹ ∈
      coreCenter (literalOctadResidual LinearFourCore.seedOctad) := by
  classical
  let e : Fin 8 ≃ LinearFourCore.seedOctad.val :=
    (Fintype.equivFinOfCardEq (show Fintype.card LinearFourCore.seedOctad.val = 8 by
      rw [← Nat.card_eq_fintype_card, LinearFourCore.seed_card])).symm
  obtain ⟨g, hg⟩ := duad_is_seed_conjugate (e 0).val (e 1).val (by
    intro he
    have hh := e.injective (Subtype.ext he)
    exact (by decide : (0 : Fin 8) ≠ 1) hh)
  refine ⟨g, hg ▸ ?_⟩
  exact ⟨core_intersection_le _ ⟨duad_mem_core _ _,
    duad_mem_seed_residual (e 0) (e 1) (e 2)
      (e.injective.ne (by decide)) (e.injective.ne (by decide))⟩,
    duad_centralizes_seed_core (e 0) (e 1)⟩

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry.SeedDuads
