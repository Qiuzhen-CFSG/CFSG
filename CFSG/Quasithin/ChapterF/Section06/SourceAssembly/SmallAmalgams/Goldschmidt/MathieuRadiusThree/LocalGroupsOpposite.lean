module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsOppositeAction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.GeneratedLocals

/-!
# Recovery of the original endpoint stabilizers

The two source generated groups cover the original vertex groups modulo the
edge stabilizer. Their local transitivity and orders give the same order-64
edge overlap. Two-perfect generation and Goldschmidt (2.6) then identify them
with the original stabilizers.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), last paragraph
of (6.12), printed p.406.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup SimpleGraph Theory.GroupAction.CubicTree Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- The generated opposite group has an orbit of length three at each neighbour. -/
theorem LocalRelations.oppositeGroup_intersection_card_mul_three
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    {a v : RankTwo.Vertex F} (hv : v.type ≠ d.side)
    (hva : (RankTwo.graph F).Adj v a) :
    Nat.card (oppositeGroup d v ⊓ RankTwo.stabilizer F a : Subgroup G) * 3 =
      Nat.card (oppositeGroup d v) := by
  let H := oppositeGroup d v
  have horbit : MulAction.orbit H a = (RankTwo.graph F).neighborSet v := by
    ext w
    constructor
    · intro hw
      obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hw
      have hh := (translationGraphIso F k.val).toHom.map_adj hva
      change (RankTwo.graph F).Adj (k.val • v) (k.val • a) at hh
      change (RankTwo.graph F).Adj v (k.val • a)
      simpa only [show k.val • v = v from oppositeGroup_le_stabilizer d v k.property] using hh
    · intro hw
      obtain ⟨k, hk, he⟩ := r.oppositeGroup_neighbor_transitive hr hv hva hw
      exact MulAction.mem_orbit_iff.mpr ⟨⟨k, hk⟩, he⟩
  have ho : Nat.card (MulAction.orbit H a) = 3 :=
    (Nat.card_congr (Equiv.setCongr horbit)).trans (h.action.card_neighbor v)
  let e : MulAction.stabilizer H a ≃* (H ⊓ RankTwo.stabilizer F a : Subgroup G) := {
    toFun := fun k => ⟨k.val.val, k.val.property, k.property⟩
    invFun := fun k => ⟨⟨k.val, k.property.1⟩, k.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H a)
  rw [Nat.card_prod, ho, Nat.card_congr e.toEquiv, Nat.mul_comm] at hc
  exact hc

/-- Once the independently computed source orders are known, the generated
local groups are the literal vertex stabilizers. -/
theorem LocalRelations.generated_locals_eq_stabilizers_of_card
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    {a v : RankTwo.Vertex F} (ha : a.type = d.side)
    (hva : (RankTwo.graph F).Adj v a)
    (hPcard : Nat.card (d.labelBall a 4) = 192)
    (hHcard : Nat.card (oppositeGroup d v) = 192) :
    d.labelBall a 4 = RankTwo.stabilizer F a ∧
      oppositeGroup d v = RankTwo.stabilizer F v := by
  let P := d.labelBall a 4
  let H := oppositeGroup d v
  let Ga := RankTwo.stabilizer F a
  let Gv := RankTwo.stabilizer F v
  have hv : v.type ≠ d.side := by simpa only [ha] using hva.1
  have hP : P ≤ Ga :=
    d.labelBall_le_stabilizer a 4 (by omega) (by have := h.five_le; omega)
  have hH : H ≤ Gv := oppositeGroup_le_stabilizer d v
  let : Finite Gv := h.action.finite_stabilizer v
  let : Finite H := Finite.of_injective (inclusion hH) (inclusion_injective hH)
  let : Finite (H ⊓ Ga : Subgroup G) := Finite.of_injective
    (inclusion (show H ⊓ Ga ≤ H from inf_le_left)) (inclusion_injective _)
  have hPH : P ⊓ H = oppositeGenerator d v a := by
    apply le_antisymm
    · exact inf_le_inf_left P hH
    · exact le_inf inf_le_left (oppositeGenerator_le d hva)
  have hPQ : P ⊓ Gv = P ⊓ H := hPH.symm
  have hQPc : Nat.card (H ⊓ Ga : Subgroup G) = 64 := by
    have hh := r.oppositeGroup_intersection_card_mul_three hr hv hva
    change Nat.card (H ⊓ Ga : Subgroup G) * 3 = Nat.card H at hh
    change Nat.card H = 192 at hHcard
    omega
  have hPQc : Nat.card (P ⊓ H : Subgroup G) = 64 := by
    rw [hPH]
    exact r.oppositeGenerator_card_of_radiusFour_card hr ha hva hPcard
  have hQP : H ⊓ Ga = P ⊓ H := by
    apply (eq_of_le_of_card_ge (show P ⊓ H ≤ H ⊓ Ga from
      le_inf inf_le_right (inf_le_left.trans hP)) ?_).symm
    rw [hQPc, hPQc]
  have hcoverP : Ga ≤ P ⊔ (Ga ⊓ Gv) := by
    calc
      Ga = P ⊔ RankTwo.ballKernel F a 2 :=
        (r.radiusFour_sup_radiusTwoKernel hr a ha).symm
      _ ≤ P ⊔ (Ga ⊓ Gv) := sup_le_sup_left
        (le_inf (RankTwo.ballKernel_le_stabilizer F a 2)
          ((RankTwo.ballKernel_succ_le F hva.symm 1).trans
            (RankTwo.ballKernel_le_stabilizer F v 1))) P
  have hcoverH : Gv ≤ H ⊔ (Ga ⊓ Gv) := by
    intro g hg
    have hga : (RankTwo.graph F).Adj v (g • a) := by
      have hh := (translationGraphIso F g).toHom.map_adj hva
      change (RankTwo.graph F).Adj (g • v) (g • a) at hh
      simpa only [show g • v = v from hg] using hh
    obtain ⟨k, hk, he⟩ := r.oppositeGroup_neighbor_transitive hr hv hva hga
    have hkg : k⁻¹ * g ∈ Ga ⊓ Gv := by
      refine ⟨?_, Gv.mul_mem (Gv.inv_mem (hH hk)) hg⟩
      change (k⁻¹ * g) • a = a
      rw [mul_smul, ← he, inv_smul_smul]
    have hh := (H ⊔ (Ga ⊓ Gv)).mul_mem (mem_sup_left hk) (mem_sup_right hkg)
    simpa only [mul_inv_cancel_left] using hh
  have hgen : P ⊔ H = ⊤ := h.action.sup_eq_top_of_local_coverage hva.symm P H
    (inf_le_left.trans (d.labelBall_normalized a 4))
    (inf_le_right.trans (oppositeGroup_normalized d h.action.toCubicTreeAction v))
    hcoverP hcoverH
  exact h.action.toCubicTreeAction.generated_locals_eq_stabilizers
    hva.symm P H hP hH hPQ hQP hgen

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
