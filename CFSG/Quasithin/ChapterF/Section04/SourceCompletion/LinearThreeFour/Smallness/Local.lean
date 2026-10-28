module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.Basic
public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.FullCore
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound

/-!
# Endpoint orders, whole overlap and valence for PSL₃(4) completions

The projective parabolics are the affine groups of order 960; the marked
Borel has order 192. Its prime index forces any excess overlap to identify
both endpoints. Generation and the trivial Borel core would then embed a
group of order 960 into the symmetric group on five letters, a contradiction.
The actual typed coset action is consequently faithful and every vertex has
five neighbors. The argument works without ambient finiteness.

Source: Aschbacher–Smith F.3.3 and F.4.4–6, printed pp.270, 274–277.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
open Matrix.PSL3.LinearThree
open CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour
local notation "F" => Matrix.PSL3Four.F

theorem native_endpoint_card (i : Bool) : Nat.card (modelCompletion.family i) = 960 := by
  have hc : Nat.card (Matrix.SL2.Affine F) = 960 := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
      show Nat.card (Multiplicative (Fin 2 → F)) = Nat.card (Fin 2 → F) from rfl,
      Nat.card_fun, Nat.card_fin, Atlas.card_sl_two, Matrix.PSL3Four.card_F]
    norm_num
  have he := Matrix.PSL3Four.ElementaryParabolic.native_parabolic_eq_local (!i)
  cases i
  · change pointParabolic F = pointLocal F at he
    simpa only [Completion.family_false, model_left_range, he,
      Nat.card_congr (pointLocalEquivAffine F).toEquiv] using hc
  · change lineParabolic F = lineLocal F at he
    simpa only [Completion.family_true, model_right_range, he,
      Nat.card_congr (lineLocalEquivAffine F).toEquiv] using hc

namespace Completion
variable {G : Type*} [Group G] (c : Completion G)
theorem endpoint_card (i : Bool) : Nat.card (c.family i) = 960 := by
  have h := native_endpoint_card i
  cases i
  · rw [family_false, model_left_range] at h
    exact c.left_card.trans h
  · rw [family_true, model_right_range] at h
    exact c.right_card.trans h

theorem middle_relIndex (i : Bool) : c.middle.range.relIndex (c.family i) = 5 := by
  have hle : c.middle.range ≤ c.family i := by
    cases i
    · exact c.middle_le_left
    · exact c.middle_le_right
  have h := (c.middle.range.subgroupOf (c.family i)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, c.middle_card,
    c.endpoint_card] at h
  change 192 * c.middle.range.relIndex (c.family i) = 960 at h
  omega

theorem overlap : c.left.range ⊓ c.right.range = c.middle.range := by
  let K := c.left.range ⊓ c.right.range
  have hBK : c.middle.range ≤ K := le_inf c.middle_le_left c.middle_le_right
  have hKL : K ≤ c.left.range := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex c.middle.range K c.left.range hBK hKL
  have hidx : c.middle.range.relIndex c.left.range = 5 := c.middle_relIndex false
  rw [hidx] at hmul
  have hd : K.relIndex c.left.range ∣ 5 := ⟨c.middle.range.relIndex K, by simpa only [Nat.mul_comm] using hmul.symm⟩
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with hK | hK
  · have hLK : c.left.range ≤ K := Subgroup.relIndex_eq_one.mp hK
    have hLR : c.left.range ≤ c.right.range := hLK.trans inf_le_right
    have hcard : Nat.card c.right.range ≤ Nat.card c.left.range := by
      have h0 := c.endpoint_card false
      have h1 := c.endpoint_card true
      change Nat.card c.left.range = 960 at h0
      change Nat.card c.right.range = 960 at h1
      omega
    let : Finite c.right.range := Nat.finite_of_card_ne_zero (by
      change Nat.card (c.family true) ≠ 0
      rw [c.endpoint_card]; decide)
    have he : c.left.range = c.right.range := eq_of_le_of_card_ge hLR hcard
    have htop : c.left.range = ⊤ := by simpa only [←he, sup_idem] using c.generated
    have hcG : Nat.card G = 960 := by
      have h := c.endpoint_card false
      change Nat.card c.left.range = 960 at h
      simpa only [htop, card_top] using h
    let : Finite G := Nat.finite_of_card_ne_zero (by rw [hcG]; decide)
    have hB : c.middle.range.index = 5 := by
      simpa only [htop, relIndex_top_right] using hidx
    have hi : Function.Injective (MulAction.toPermHom G (G ⧸ c.middle.range)) := by
      rw [←MonoidHom.ker_eq_bot_iff, ←Subgroup.normalCore_eq_ker]
      exact c.middle_normalCore
    have hb := Nat.card_le_card_of_injective _ hi
    rw [hcG, Nat.card_perm, ←Subgroup.index_eq_card, hB] at hb
    norm_num at hb
  · have hB : c.middle.range.relIndex K = 1 := by rw [hK] at hmul; omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hB) hBK
/-- The whole intersection identifies the action kernel with the marked Borel core. -/
theorem vertex_action_injective : Function.Injective (MulAction.toPermHom G c.Vertex) :=
  c.vertex_action_injective_of_overlap c.overlap

/-- In particular the source involutions require no additional faithfulness premise. -/
theorem vertex_action_injective_of_involutions (s t : G)
    (_hs : s ∈ c.left.range) (_ht : t ∈ c.right.range)
    (_hsout : s ∉ c.middle.range) (_htout : t ∉ c.middle.range)
    (_hs2 : orderOf s = 2) (_ht2 : orderOf t = 2) (_hst : orderOf (s*t) = 3) :
    Function.Injective (MulAction.toPermHom G c.Vertex) := c.vertex_action_injective

/-- The local coset index, using the whole intersection. -/
theorem neighbor_index (i : Bool) :
    ((c.family (!i)).subgroupOf (c.family i)).index = 5 := by
  have hi : c.family (!i) ⊓ c.family i = c.middle.range := by
    cases i
    · exact (inf_comm _ _).trans c.overlap
    · exact c.overlap
  have hh : (c.family (!i)).subgroupOf (c.family i) =
      c.middle.range.subgroupOf (c.family i) := by
    rw [←hi]
    ext g
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, and_iff_left g.property]
  rw [hh]
  exact c.middle_relIndex i

/-- Each actual typed coset has five neighbors. -/
theorem card_neighbors (v : c.Vertex) : Nat.card (c.graph.neighborSet v) = 5 :=
  Subgroup.CosetGeometry.RankTwo.card_neighbors_of_indices c.family (fun _ => 5)
    c.neighbor_index v

end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour
