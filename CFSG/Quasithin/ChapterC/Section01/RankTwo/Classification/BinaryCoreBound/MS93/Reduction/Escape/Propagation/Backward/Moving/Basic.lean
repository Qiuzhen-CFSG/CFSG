module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Control
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Stages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Algebra

/-!
# Local products in the moving-neighbor argument

The product hypothesis is transported to the actual starting vertex before
it is used. A nonmoving neighbor gives a normal product of Z-layers: the
residual acts trivially modulo the first Z-layer, and the kernel normalizes
both factors. Normal radius products can be conjugated towards a prescribed
vertex, giving a kernel bound from strict critical minimality.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.7)(ii)--(iii), p.888.
The conjugation argument follows the earlier local-product calculation on
pp.885--886, already formalized in PairingControl.Geometry.Terminal.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Moving
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- Part (i) at an arbitrary M-vertex, justified by an actual transported
contrary configuration. -/
theorem products_at (p : Counterexample geometry) (hb : 0 < geometry.b R)
    (products : ProductFacts geometry) (a d : Vertex R) (ha : color R a = false)
    (hd : (cosetGraph R).dist a d = 2) (hm : a ∈ movingNeighbors geometry d) :
    V R d ⊔ V R a ≤ stabilizer R a ∧
      ((V R d ⊔ V R a).subgroupOf (stabilizer R a)).Normal ∧
      ⁅V R d, Ltilde R a⁆ ≤ Vcirc R a := by
  obtain ⟨q, hq⟩ := counterexample_at_vertex p hb a ha
  subst a
  exact products.products q d hd hm

variable [Finite M]

/-- The literal quotient-fixed definition of B bounds its residual
commutator by Z, without replacing B by an ambient centralizer. -/
theorem B_commutator_le_Z (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) :
    ⁅B R a (geometry.Z_normal a), Ltilde R a⁆ ≤ Z R a := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl x hx
  exact ((mem_B_iff R a (geometry.Z_normal a)
    ((geometry.V_le_Q hb a ha).trans (fun _ hv => hv.1)) x).mp hx).2 l hl

/-- In the nonmoving direction the product of Z-layers is normalized by
the full local group, using its residual/kernel generation. -/
theorem nonmoving_Z_join_normalized (source : LocalSource L R)
    (hb : 2 < geometry.b R) {a d : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a d = 2)
    (hn : d ∉ movingNeighbors geometry a) :
    stabilizer R a ≤ normalizer (Z R a ⊔ Z R d : Subgroup (FreeAmalgam R)) := by
  have hdc : color R d = false :=
    (color_eq_of_dist_even R a d (hd.symm ▸ (by decide : Even 2))).symm.trans ha
  have hB : Z R d ≤ B R a (geometry.Z_normal a) := by
    by_contra h
    exact hn ⟨hd, h⟩
  rw [← source.local_generation a ha]
  apply sup_le
  · exact PairingControl.Geometry.LocalProducts.normalizes_sup_of_commutator_le
      _ _ _ ((Ltilde_le_stabilizer a).trans (Z_normalized R a))
      ((commutator_mono hB le_rfl).trans (B_commutator_le_Z hb a ha))
  · exact (le_inf ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans
        (Z_normalized R a))
      ((Q_le_stabilizer_of_dist_le_two a d ha hdc hd.le).trans (Z_normalized R d))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- Normality is relative to the actual vertex stabilizer. -/
theorem nonmoving_Z_join_normal (source : LocalSource L R)
    (hb : 2 < geometry.b R) {a d : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a d = 2)
    (hn : d ∉ movingNeighbors geometry a) :
    ((Z R a ⊔ Z R d).subgroupOf (stabilizer R a)).Normal :=
  normal_subgroupOf_of_le_normalizer (nonmoving_Z_join_normalized source hb ha hd hn)

/-- A normal radius product can be moved towards the target. The strict
distance bound is measured from its normalizing vertex, not from both
original radius centers. -/
theorem normal_radius_product_le_kernel {a s d : Vertex R}
    (ha : color R a = false) (hs : color R s = false)
    (has : (cosetGraph R).dist a s = 2) (hb : 4 < geometry.b R)
    (hn : ((V R a ⊔ V R s).subgroupOf (stabilizer R s)).Normal)
    (hd : (cosetGraph R).dist s d + 2 < geometry.b R) :
    V R a ⊔ V R s ≤ Q R d := by
  by_cases hds : d = s
  · subst d
    exact sup_le (V_le_Q_of_dist_add_two_lt ha (by omega))
      (V_le_Q_of_dist_add_two_lt hs hd)
  have hlocal : V R a ⊔ V R s ≤ stabilizer R s :=
    (sup_le (V_le_Q_of_dist_add_two_lt ha (by omega))
      (geometry.V_le_Q (by omega) s hs)).trans (fun _ hx => hx.1)
  have hnorm := (normal_subgroupOf_iff_le_normalizer hlocal).mp hn
  obtain ⟨t, hat, hst⟩ := exists_common_neighbor_of_dist_two R a s has
  have hpos : 0 < (cosetGraph R).dist s d :=
    (cosetGraph_connected R).pos_dist_of_ne (Ne.symm hds)
  obtain ⟨u, hsu, hud⟩ := exists_adjacent_dist_sub_one R s d hpos
  obtain ⟨g, hgs, hgt⟩ := stabilizer_transitive_neighbors R s hst hsu
  have hgu : Adjacent R (act R g a) u := by
    rw [← hgt]
    exact (adjacent_act_iff R g a t).mpr hat
  have hag : color R (act R g a) = false := by rw [action_preserves_color]; exact ha
  have hgd : (cosetGraph R).dist (act R g a) d + 2 < geometry.b R := by
    have htri := (cosetGraph_connected R).dist_triangle (u := act R g a) (v := u) (w := d)
    have hone := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hgu)
    omega
  have hmap := mem_normalizer_iff_map_conj_eq.mp
    (hnorm ((stabilizer R s).inv_mem hgs))
  change (V R a ⊔ V R s).map (MulAut.conj g⁻¹).toMonoidHom = V R a ⊔ V R s at hmap
  have hfix : act R g s = s := hgs
  rw [Subgroup.map_sup, ← V_act, ← V_act, hfix] at hmap
  rw [← hmap]
  exact sup_le (V_le_Q_of_dist_add_two_lt hag hgd) (V_le_Q_of_dist_add_two_lt hs hd)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Moving
