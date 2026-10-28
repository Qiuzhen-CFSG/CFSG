module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusSeedIntersection

/-!
# The remaining fixed index for a nontrivial actor in the original mover

The full smaller mover has fixed index at most q². Every actor outside the
literal vertex kernel has fixed index at least q. The whole-Z decomposition
preserves both indices, including its complete central attachment. Multiplying
indices through the two nested fixed subgroups bounds their relative index by
q. On an actual critical path the full mover-fixed subgroup is precisely the
intersection with its second seed, so every actor-fixed subgroup of the first
seed has index at most q modulo that second seed.

This is the small remaining fixed quotient used in the large-distance
displacement comparison of MS93 (5.11), printed p.924. The actor is measured
against the original full kernel, and no quotient complement is chosen.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

private theorem fixed_index_of_central_join {G : Type*} [Group G]
    (X U C A : Subgroup G) [IsMulCommutative X]
    (hUX : U ≤ X) (hsplit : X=U ⊔ C)
    (hCA : C ≤ centralizer (A : Set G)) :
    (centralizer (A : Set G)).relIndex X =
      (centralizer (A : Set G)).relIndex U := by
  let Y := X ⊓ centralizer (A : Set G)
  have hCX : C ≤ X := le_sup_right.trans_eq hsplit.symm
  have hjoin : U ⊔ Y=X := by
    apply le_antisymm (sup_le hUX inf_le_left)
    exact hsplit.le.trans (sup_le le_sup_left
      ((show C ≤ Y from le_inf hCX hCA).trans le_sup_right))
  let : CommGroup X := IsMulCommutative.instCommGroup
  have hh := relIndex_sup_right (U.subgroupOf X) (Y.subgroupOf X)
  rw [←subgroupOf_sup hUX (show Y ≤ X from inf_le_left),hjoin,
    relIndex_subgroupOf le_rfl,relIndex_subgroupOf hUX] at hh
  have he (V : Subgroup G) (hv : V ≤ X) :
      Y.subgroupOf V=(centralizer (A : Set G)).subgroupOf V := by
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨hv x.property,hx⟩⟩
  change (Y.subgroupOf X).index=(Y.subgroupOf U).index at hh
  rwa [he X le_rfl,he U hUX] at hh

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A nontrivial actor inside the literal first mover leaves at most one
field dimension outside the actual second seed, on every fixed subgroup
of the complete first seed. -/
theorem Input.replacement_path_nontrivial_actor_fixed_seed_index_le_field
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (A : Subgroup (FreeAmalgam d.radical))
    (hAJ : A ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (path.walk.getVert 1)) (Nat.card F^2))
    (hne : ¬ A ≤ Q d.radical a)
    (D : Subgroup (FreeAmalgam d.radical)) (hDZ : D ≤ Z d.radical a)
    (hDA : ⁅D,A⁆=⊥) :
    (Z d.radical (path.walk.getVert 2)).relIndex D ≤ Nat.card F := by
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical (path.walk.getVert 1)) (Nat.card F^2)
  let C := Z d.radical a ⊓ centralizer
    (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  let CA := Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical))
  let CJ := Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hJS : J ≤ stabilizer d.radical a := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm _ hat))
  have hAS := hAJ.trans hJS
  have hsplit : Z d.radical a=U d.radical a ⊔ C :=
    h.replacement_Z_eq_U_sup_fixed d geometry hb.le path.start_color
  let := geometry.Z_elementary (by omega) a path.start_color
  let := finite_Z d.radical a
  let : Finite CA := Finite.of_injective (inclusion (show CA ≤ Z d.radical a from inf_le_left))
    (inclusion_injective _)
  have hidx (T : Subgroup (FreeAmalgam d.radical)) (hTS : T ≤ stabilizer d.radical a) :
      (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a)=
        (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) :=
    fixed_index_of_central_join _ _ C T (U_le_Z a) hsplit
      (inf_le_right.trans (centralizer_le hTS))
  have hlow : Nat.card F ≤ CA.relIndex (Z d.radical a) := by
    rw [show CA=Z d.radical a ⊓ centralizer (A : Set _) from rfl,
      inf_relIndex_left,hidx A hAS]
    exact h.replacement_natural_fixed_index_lower d geometry hb.le path.start_color A hAS hne
  have hupp : CJ.relIndex (Z d.radical a) ≤ Nat.card F^2 := by
    rw [show CJ=Z d.radical a ⊓ centralizer (J : Set _) from rfl,
      inf_relIndex_left,hidx J hJS]
    exact h.replacement_small_mover_index_le_square_of_four_lt d geometry hb path.start_color hat
  have hC : CJ ≤ CA := inf_le_inf_left _ (centralizer_le hAJ)
  have hmul := relIndex_mul_relIndex CJ CA (Z d.radical a) hC inf_le_left
  have hbound : CJ.relIndex CA ≤ Nat.card F := by
    have hq : 0 < Nat.card F := Nat.card_pos
    have hh := Nat.mul_le_mul_left (CJ.relIndex CA) hlow
    rw [←hmul] at hupp
    nlinarith
  have hDC : D ≤ CA := le_inf hDZ (commutator_eq_bot_iff_le_centralizer.mp hDA)
  have hm := (relIndex_le_of_le_right hDC (by
    exact index_ne_zero_of_finite (H := CJ.subgroupOf CA))).trans hbound
  have he : CJ.subgroupOf D=(Z d.radical (path.walk.getVert 2)).subgroupOf D := by
    ext x
    change x.val ∈ Z d.radical a ⊓ centralizer (J : Set _) ↔
      x.val ∈ Z d.radical (path.walk.getVert 2)
    rw [←h.replacement_path_seed_intersection_of_four_lt d path hb]
    exact ⟨fun hx => hx.2,fun hx => ⟨hDZ x.property,hx⟩⟩
  change (CJ.subgroupOf D).index ≤ Nat.card F at hm
  rwa [he] at hm

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
