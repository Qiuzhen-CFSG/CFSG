module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving.Basic

/-!
# The local normal subgroups in the asymmetric case

Suppose a moves at d, but d does not move at a. The Z-product is normal
at a. Its centralizer in Q_a is exactly Q_a ∩ Q_d, so that intersection is
also normal there. Part (i)'s residual bound similarly normalizes the
product of the two moving radius groups. Finally H_d lies in U_a whereas
H_a lies in D_a, proving the disjointness used in the symmetry argument.

These are preparatory deductions for (4.3.7)(ii); the normal-commutator
and three-subgroup contradiction are not asserted here.
Source: Meierfrankenfeld--Stellmacher (1993), printed p.888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Moving
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

private theorem normalizes_inf {G : Type*} [Group G] (K A B : Subgroup G)
    (hA : K ≤ normalizer (A : Set G)) (hB : K ≤ normalizer (B : Set G)) :
    K ≤ normalizer (A ⊓ B : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro k hk x hx
  exact ⟨le_normalizer_iff.mp hA k hk x hx.1,
    le_normalizer_iff.mp hB k hk x hx.2⟩

include geometry in
/-- The kernel intersection is the centralizer of the Z-product inside
the first kernel. All centralizers are taken in the actual amalgam. -/
theorem kernel_intersection_eq_centralizer (source : LocalSource L R)
    {a d : Vertex R} (ha : color R a = false) (hd : color R d = false)
    (had : (cosetGraph R).dist a d = 2) :
    Q R a ⊓ Q R d = Q R a ⊓ centralizer (Z R a ⊔ Z R d : Subgroup (FreeAmalgam R)) := by
  apply le_antisymm
  · apply le_inf inf_le_left
    apply le_centralizer_iff.mpr
    apply sup_le
    · exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha)).trans
        (centralizer_le inf_le_left)
    · exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hd)).trans
        (centralizer_le inf_le_right)
  · apply le_inf inf_le_left
    rw [← source.C_eq_Q geometry.radical_ne_bot d hd]
    exact le_inf (inf_le_left.trans (Q_le_stabilizer_of_dist_le_two a d ha hd had.le))
      (inf_le_right.trans (centralizer_le
        (show Z R d ≤ Z R a ⊔ Z R d from le_sup_right)))

/-- The second normal subgroup displayed in the proof of (ii). -/
theorem nonmoving_kernel_intersection_normalized (source : LocalSource L R)
    (hb : 2 < geometry.b R) {a d : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a d = 2) (hn : d ∉ movingNeighbors geometry a) :
    stabilizer R a ≤ normalizer (Q R a ⊓ Q R d : Subgroup (FreeAmalgam R)) := by
  have hdc : color R d = false :=
    (color_eq_of_dist_even R a d (hd.symm ▸ (by decide : Even 2))).symm.trans ha
  rw [kernel_intersection_eq_centralizer (geometry := geometry) source ha hdc hd]
  exact normalizes_inf _ _ _ (Q_normalized R a)
    ((nonmoving_Z_join_normalized source hb ha hd hn).trans
      (normalizer_le_normalizer_centralizer _))

/-- Relative normality of the kernel intersection, without any claim of
normality at the opposite vertex. -/
theorem nonmoving_kernel_intersection_normal (source : LocalSource L R)
    (hb : 2 < geometry.b R) {a d : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a d = 2) (hn : d ∉ movingNeighbors geometry a) :
    ((Q R a ⊓ Q R d).subgroupOf (stabilizer R a)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (nonmoving_kernel_intersection_normalized source hb ha hd hn)

/-- The third normal subgroup displayed in (ii). The residual commutator
bound in (i) controls one factor; Q_a normalizes it because Q_a ≤ G_d. -/
theorem moving_join_normalized (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 0 < geometry.b R)
    (products : ProductFacts geometry) {a d : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a d = 2) (hm : a ∈ movingNeighbors geometry d) :
    stabilizer R a ≤ normalizer (Vcirc R a ⊔ Vcirc R d : Subgroup (FreeAmalgam R)) := by
  have hdc : color R d = false :=
    (color_eq_of_dist_even R a d (hd.symm ▸ (by decide : Even 2))).symm.trans ha
  have hp := products_at p hb products a d ha hd hm
  have hV : Vcirc R d ≤ V R d := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer d).trans (V_normalized d))
  rw [← source.local_generation a ha]
  apply sup_le
  · exact PairingControl.Geometry.LocalProducts.normalizes_sup_of_commutator_le _ _ _
      ((Ltilde_le_stabilizer a).trans (Vcirc_normalized a))
      ((commutator_mono hV le_rfl).trans hp.2.2)
  · exact (le_inf ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans
        (Vcirc_normalized a))
      ((Q_le_stabilizer_of_dist_le_two a d ha hdc hd.le).trans (Vcirc_normalized d))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- Relative normality of the moving join. -/
theorem moving_join_normal (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 0 < geometry.b R)
    (products : ProductFacts geometry) {a d : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a d = 2) (hm : a ∈ movingNeighbors geometry d) :
    ((Vcirc R a ⊔ Vcirc R d).subgroupOf (stabilizer R a)).Normal :=
  normal_subgroupOf_of_le_normalizer (moving_join_normalized source p hb products ha hd hm)

/-- Both displayed factors being normalized implies their commutator is
normalized. This is the normal subgroup used before the three-subgroup step. -/
theorem asymmetric_commutator_normalized (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (products : ProductFacts geometry) {a d : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a d = 2) (hm : a ∈ movingNeighbors geometry d)
    (hn : d ∉ movingNeighbors geometry a) :
    stabilizer R a ≤ normalizer
      (⁅Vcirc R a ⊔ Vcirc R d, Q R a ⊓ Q R d⁆ : Subgroup (FreeAmalgam R)) := by
  have hV := moving_join_normalized source p (by omega) products ha hd hm
  have hQ := nonmoving_kernel_intersection_normalized source hb ha hd hn
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hV hg), mem_normalizer_iff_map_conj_eq.mp (hQ hg)]

omit [Finite M] in
/-- The global fixed-core control bounds the actual H subgroup at any
vertex, after transporting the contrary configuration. -/
theorem H_le_fixedCore (p : Counterexample geometry) (hb : 0 < geometry.b R)
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (a : Vertex R) (ha : color R a = false) : H R a ≤ fixedCore R a := by
  have hV : Vcirc R a ≤ V R a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  exact (commutator_mono hV le_rfl).trans (commutator_le_fixed_at p hb control a ha)

/-- In the reverse-moving direction H_d is the edge displacement coming
from Z_a, hence lies in the genuine natural subgroup U_a. -/
theorem reverse_H_le_U {source : LocalSource L R}
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (control : ∀ q : Counterexample geometry, LocalControl q)
    {a d : Vertex R} (ha : color R a = false) (hm : a ∈ movingNeighbors geometry d) :
    H R d ≤ U R a := by
  have hdc : color R d = false :=
    (color_eq_of_dist_even R d a (hm.1.symm ▸ (by decide : Even 2))).trans ha
  obtain ⟨t, hdt, hat⟩ := exists_common_neighbor_of_dist_two R d a hm.1
  rw [(moving_edge_eq_at p (by omega) control d t a hdc hdt hat hm).2]
  exact EdgeTransfer.edge_commutator_le_natural hb modules a t ha hat

/-- The H factors in the asymmetric argument are disjoint. This uses
the natural/fixed disjointness of (4.1), not a bare dimension label. -/
theorem reverse_H_disjoint {source : LocalSource L R}
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (control : ∀ q : Counterexample geometry, LocalControl q)
    {a d : Vertex R} (ha : color R a = false) (hm : a ∈ movingNeighbors geometry d) :
    Disjoint (H R a) (H R d) := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  rw [← EdgeTransfer.U_fixed_eq_bot modules a ha]
  exact le_inf (inf_le_right.trans (reverse_H_le_U p hb modules control ha hm))
    (inf_le_left.trans ((H_le_fixedCore p (by omega) control a ha).trans inf_le_right))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Moving
