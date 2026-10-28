module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple.Action
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer

/-!
# Nontrivial residual action on the radius head

The radius-one span at an adjacent holomorph vertex normally generates V_a
inside its local stabilizer. If the residual fixed V_a/(Z_a[V_a,Q_a]), this
span together with [V_a,Q_a] would be normal in that stabilizer, hence equal
to V_a. A finite two-group commutator argument removes [V_a,Q_a] from this
supplement. The span would then be normal in both adjacent stabilizers,
contradicting the source characteristic condition and |U_a| = 8.

This proves nontrivial action on the actual head before any triple bound
or natural splitting. It supplies the geometric input to the dual-module
argument of Meierfrankenfeld--Stellmacher (1993), (4.3.1)(iii), pp.882--883,
using the common-normal obstruction of (2.1)(iii), p.855.
-/

public section

open Subgroup Representation Representation.BinaryOffender

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
private theorem le_of_le_sup_commutator_pGroup (hp : IsPGroup 2 G)
    (H N : Subgroup G) [H.Normal] [N.Normal]
    (h : H ≤ N ⊔ ⁅H, ⊤⁆) : H ≤ N := by
  let q := QuotientGroup.mk' N
  have hb : H.map q ≤ ⁅H.map q, ⊤⁆ := by
    have hh := map_mono (f := q) h
    rw [Subgroup.map_sup, map_commutator, QuotientGroup.map_mk'_self,
      map_top_of_surjective q (QuotientGroup.mk'_surjective N), bot_sup_eq] at hh
    exact hh
  have he : ⁅H.map q, ⊤⁆ = H.map q := le_antisymm (commutator_le_left _ _) hb
  have hz : H.map q ≤ ⊥ := le_normal_of_quotient_isPGroup_of_eq_commutator
    (H.map q) ⊤ ⊥ ((hp.to_quotient N).to_quotient ⊥) he
  have hh := (map_eq_bot_iff H).mp (le_bot_iff.mp hz)
  simpa only [q, QuotientGroup.ker_mk'] using hh
end Subgroup

open Subgroup Representation Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

omit [Finite M] in
private theorem ball_normalized (t : Vertex R) (n : ℕ) :
    stabilizer R t ≤ normalizer (VBall R t n : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (VBall R t n).map (MulAut.conj g).toMonoidHom = VBall R t n
  have h := VBall_act R g⁻¹ t n
  have hgt : act R g⁻¹ t = t := (stabilizer R t).inv_mem hg
  simpa only [hgt, inv_inv] using h.symm

omit [Finite M] in
private theorem star_le_radius (a t : Vertex R) (hat : Adjacent R a t) :
    VBall R t 1 ≤ V R a := by
  have hta : (cosetGraph R).dist t a = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
      (adjacent_symm R hat))
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  apply le_iSup_of_le d
  apply le_iSup_of_le (show (cosetGraph R).dist d a ≤ 2 from ?_)
  · exact le_rfl
  · have hh := (cosetGraph_connected R).dist_triangle (u := d) (v := t) (w := a)
    omega

omit [Finite M] in
private theorem Z_le_star (a t : Vertex R) (hat : Adjacent R a t) :
    Z R a ≤ VBall R t 1 := le_iSup_of_le a (le_iSup_of_le
      (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)).le le_rfl)

/-- One adjacent radius-one span normally generates the radius-two group. -/
theorem radius_le_of_star_normalized (a t : Vertex R) (hat : Adjacent R a t)
    (K : Subgroup (FreeAmalgam R)) (hN : VBall R t 1 ≤ K)
    (hn : stabilizer R a ≤ normalizer (K : Set (FreeAmalgam R))) : V R a ≤ K := by
  apply iSup_le
  intro c
  apply iSup_le
  intro hc
  obtain ⟨w, hw⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a c
  have hwle : w.length ≤ 2 := by rw [hw, SimpleGraph.dist_comm]; exact hc
  cases w with
  | nil => exact (Z_le_star a t hat).trans hN
  | cons had w =>
    rename_i d
    have had' := (cosetGraph_adj R a d).mp had
    obtain ⟨g, hg, hgt⟩ := stabilizer_transitive_neighbors R a hat had'
    have hstar : VBall R d 1 ≤ K := by
      have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hN
      have he := VBall_act R g t 1
      rw [hgt] at he
      have hk : K.map (MulAut.conj g⁻¹).toMonoidHom = K :=
        mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer R a).inv_mem hg))
      rw [← he, hk] at hm
      exact hm
    apply le_trans ?_ hstar
    apply le_iSup_of_le c
    apply le_iSup_of_le (show (cosetGraph R).dist c d ≤ 1 from ?_)
    · exact le_rfl
    · rw [SimpleGraph.dist_comm]
      exact (cosetGraph R).dist_le w |>.trans (by simpa using hwle)

/-- The radius quotient by its Q-commutators still has nontrivial residual action.
This uses the finite two-group supplement argument and the common-normal obstruction. -/
theorem radius_head_moving (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) :
    ¬ ⁅V R a, Ltilde R a⁆ ≤ Z R a ⊔ ⁅V R a, Q R a⁆ := by
  intro hfixed
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  let a := mVertex R g
  let t := hVertex R g
  have hat : Adjacent R a t :=
    (adjacent_iff_exists_common R _ _).mpr ⟨g, Or.inl ⟨rfl, rfl⟩⟩
  let N := VBall R t 1
  let D := ⁅V R a, Q R a⁆
  let K := N ⊔ D
  have hVQ := geometry.V_le_Q hb a (show color R a = false from rfl)
  have hNV : N ≤ V R a := star_le_radius a t hat
  have hD : D ≤ V R a := le_normalizer_iff_commutator_le_left.mp
    ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (V_normalized a))
  have hKV : K ≤ V R a := sup_le hNV hD
  have hNQ : N ≤ Q R a := hNV.trans hVQ
  have hQN : Q R a ≤ normalizer (N : Set (FreeAmalgam R)) :=
    (show Q R a ≤ stabilizer R t from fun _ hx => hx.2 t hat).trans (ball_normalized t 1)
  have hQD : Q R a ≤ normalizer (D : Set (FreeAmalgam R)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq]
    change D.map (MulAut.conj x).toMonoidHom = D
    dsimp [D]
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp ((V_normalized a) hx.1),
      mem_normalizer_iff_map_conj_eq.mp ((Q R a).le_normalizer hx)]
  have hQK : Q R a ≤ normalizer (K : Set (FreeAmalgam R)) :=
    (le_inf hQN hQD).trans (normalizer_inf_normalizer_le_normalizer_sup N D)
  have hPK : Ltilde R a ≤ normalizer (K : Set (FreeAmalgam R)) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono hKV le_rfl).trans (hfixed.trans
      (sup_le ((Z_le_star a t hat).trans le_sup_left) le_sup_right))
  have hSK : stabilizer R a ≤ normalizer (K : Set (FreeAmalgam R)) := by
    rw [← source.local_generation a rfl]
    exact sup_le hPK hQK
  have hVK : V R a ≤ K := radius_le_of_star_normalized a t hat K le_sup_left hSK
  let P := Q R a
  let H := (V R a).subgroupOf P
  let N₀ := N.subgroupOf P
  let := finite_stabilizer R a
  let : Finite P := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)) (inclusion_injective _)
  let : H.Normal := normal_subgroupOf_of_le_normalizer
    ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (V_normalized a))
  let : N₀.Normal := normal_subgroupOf_of_le_normalizer hQN
  have hHN : H ≤ N₀ ⊔ ⁅H, ⊤⁆ := by
    apply (map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_sup, map_commutator, map_subgroupOf_eq_of_le hVQ,
      map_subgroupOf_eq_of_le hNQ, ← MonoidHom.range_eq_map, range_subtype]
    exact hVK
  have hle := le_of_le_sup_commutator_pGroup
    (Q_isPGroup R source.two_group source.core_le a rfl) H N₀ hHN
  have hVN : V R a ≤ N := by
    have hm := map_mono (f := P.subtype) hle
    rwa [map_subgroupOf_eq_of_le hVQ, map_subgroupOf_eq_of_le hNQ] at hm
  have hNS : N ≤ stabilizer R a ⊓ stabilizer R t :=
    le_inf (hNQ.trans (fun _ hx => hx.1)) (hNQ.trans (fun _ hx => hx.2 t hat))
  have hNa : stabilizer R a ≤ normalizer (N : Set (FreeAmalgam R)) := by
    rw [← le_antisymm hVN hNV]
    exact V_normalized a
  have hbot := no_common_normal_at_edge R source.characteristic a t rfl hat N hNS
    (normal_subgroupOf_of_le_normalizer hNa)
    (normal_subgroupOf_of_le_normalizer (ball_normalized t 1))
  have hz : U R a = ⊥ := le_bot_iff.mp
    ((U_le_Z a).trans ((Z_le_star a t hat).trans hbot.le))
  have hc := modules.natural.card_at a rfl
  rw [hz, card_bot] at hc
  omega
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple

