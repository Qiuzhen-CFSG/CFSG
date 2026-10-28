module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.Contracts
public import Theory.GroupAction.CubicTree.TrackArcs

/-!
# Separation of the actual radius-three labels

Short-arc transitivity carries an ordered pair of vertices to the chosen
translation track. The exact fixed intervals there distinguish its labels.
Consequently the center and six forward vertices have seven different
nonidentity labels: the radius-two label group has order at least eight.
Together with the four-generator bound this is the order range used in
Goldschmidt's commutator argument for (6.12.1)--(6.12.4), pp.403--404.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

namespace LargeTreeSource

/-- Transport the chosen track segment to the literal ordered vertex pair. -/
theorem exists_track_pair (h : LargeTreeSource F s) (d : CanonicalLabelSetup F s)
    {a b : RankTwo.Vertex F} (ha : a.type = d.side)
    (hd : (RankTwo.graph F).dist a b ≤ s) :
    ∃ g : G, g • d.track.vertex d.center = a ∧
      g • d.track.vertex (d.center + (RankTwo.graph F).dist a b) = b := by
  obtain ⟨g₀, hg₀⟩ := (RankTwo.same_orbit_iff F (d.track.vertex d.center) a).mpr
    (d.center_type.trans ha.symm)
  let w := g₀⁻¹ • b
  have hw : (RankTwo.graph F).dist (d.track.vertex d.center) w =
      (RankTwo.graph F).dist a b := by
    have he := RankTwo.dist_smul F g₀ (d.track.vertex d.center) w
    simpa only [hg₀, w, smul_inv_smul] using he.symm
  obtain ⟨q, hq, hend⟩ := BasedWalk.exists_geodesic
    (h.action.tree.connected.preconnected (d.track.vertex d.center) w)
  obtain ⟨k, hk, hmap⟩ := rootPathTransitive_of_short_rightRegular trackGraphAction
    s h.regular (d.track.vertex d.center) _ (hw ▸ hd)
    (d.track.arc d.center _) q (d.track.arc_nonbacktracking _ _) hq
  have he : k • d.track.vertex
      (d.center + (RankTwo.graph F).dist (d.track.vertex d.center) w) = w := by
    simpa only [Track.arc_endpoint, hend] using
      endpoint_smul_of_vertices trackGraphAction k (d.track.arc d.center _) q hmap
  refine ⟨g₀ * k, ?_, ?_⟩
  · rw [mul_smul, hk, hg₀]
  · rw [mul_smul, ← hw, he]
    exact smul_inv_smul g₀ b

end LargeTreeSource

namespace CanonicalLabelSetup

/-- Distinct vertices at the available short distances have distinct labels.
This uses the exact track intervals and does not enlarge the short-arc bound. -/
theorem label_ne_of_short_dist (d : CanonicalLabelSetup F s)
    (h : LargeTreeSource F s) {a b : RankTwo.Vertex F}
    (ha : a.type = d.side) (hb : b.type = d.side) (hne : a ≠ b)
    (hd : (RankTwo.graph F).dist a b ≤ s) : d.label a ≠ d.label b := by
  obtain ⟨k, hk⟩ := (RankTwo.even_dist_iff F h.action.generated a b).mpr
    (ha.trans hb.symm)
  have hn : 0 < k := by
    have hn : (RankTwo.graph F).dist a b ≠ 0 :=
      fun hz => hne (h.action.tree.connected.dist_eq_zero_iff.mp hz)
    omega
  obtain ⟨g, hga, hgb⟩ := h.exists_track_pair d ha hd
  have ht : d.center + ((RankTwo.graph F).dist a b : ℤ) = d.center + 2 * (k : ℤ) := by
    omega
  rw [ht] at hgb
  intro he
  have he' : d.label (d.track.vertex d.center) =
      d.label (d.track.vertex (d.center + 2 * (k : ℤ))) := by
    have haa := d.conjugate g (d.track.vertex d.center) d.center_type
    have hbb := d.conjugate g (d.track.vertex (d.center + 2 * (k : ℤ)))
      (d.shifted_type k)
    rw [hga] at haa
    rw [hgb] at hbb
    exact (MulAut.conj g).injective (haa.symm.trans (he.trans hbb))
  let i := d.center - (d.radius + 1 : ℕ)
  have hfix : d.label (d.track.vertex d.center) • d.track.vertex i = d.track.vertex i := by
    have hh := (d.shifted_fixed_iff 0 i).mpr (by dsimp [i]; omega)
    simpa only [mul_zero, add_zero] using hh
  rw [he'] at hfix
  have hh := (d.shifted_fixed_iff k i).mp hfix
  dsimp [i] at hh
  omega

/-- The seven vertices of the labelled radius-two ball give seven distinct
nonidentity elements of its actual generated subgroup. -/
theorem radiusTwo_card_ge (d : CanonicalLabelSetup F s) (h : LargeTreeSource F s)
    (a : RankTwo.Vertex F) (ha : a.type = d.side) :
    8 ≤ Nat.card (d.labelBall a 2) := by
  classical
  obtain ⟨f⟩ := h.action.toCubicTreeAction.exists_branchFrame a
  let v : Option (Fin 3 × ZMod 2) → RankTwo.Vertex F := fun x => x.elim a f.point
  have hvtype (x : Option (Fin 3 × ZMod 2)) : (v x).type = d.side := by
    cases x with
    | none => exact ha
    | some x =>
      have he := (RankTwo.even_dist_iff F h.action.generated a (f.point x)).mp
        (by rw [f.point_dist h.action.toCubicTreeAction]; decide)
      exact he.symm.trans ha
  have hvdist (x : Option (Fin 3 × ZMod 2)) : (RankTwo.graph F).dist a (v x) ≤ 2 := by
    cases x with
    | none => exact (by simp [v])
    | some x => exact le_of_eq (f.point_dist h.action.toCubicTreeAction x)
  have hvinj : Function.Injective v := by
    intro x y he
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact ((f.point_ne_center y) he.symm).elim
    | some x =>
      cases y with
      | none => exact ((f.point_ne_center x) he).elim
      | some y => exact congrArg some (f.point_injective h.action.toCubicTreeAction he)
  let l : Option (Fin 3 × ZMod 2) → d.labelBall a 2 := fun x =>
    ⟨d.label (v x), d.label_mem_labelBall (hvtype x) (hvdist x)⟩
  have hlinj : Function.Injective l := by
    intro x y he
    apply hvinj
    by_contra hvne
    have hdist : (RankTwo.graph F).dist (v x) (v y) ≤ s := by
      have ht := h.action.tree.connected.dist_triangle (u := v x) (v := a) (w := v y)
      rw [SimpleGraph.dist_comm (u := v x) (v := a)] at ht
      have hx := hvdist x
      have hy := hvdist y
      have hs := h.five_le
      omega
    exact d.label_ne_of_short_dist h (hvtype x) (hvtype y) hvne hdist
      (congrArg Subtype.val he)
  have hlne (x : Option (Fin 3 × ZMod 2)) : l x ≠ 1 := by
    intro he
    have hh := d.order_two (v x) (hvtype x)
    have he' : d.label (v x) = 1 := congrArg Subtype.val he
    rw [he', orderOf_one] at hh
    omega
  let u : Option (Option (Fin 3 × ZMod 2)) → d.labelBall a 2 := fun x => x.elim 1 l
  have hu : Function.Injective u := by
    intro x y he
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact (hlne y he.symm).elim
    | some x =>
      cases y with
      | none => exact (hlne x he).elim
      | some y => exact congrArg some (hlinj he)
  let : Finite (RankTwo.stabilizer F a) := h.action.finite_stabilizer a
  have hr : 2 ≤ d.radius + 1 := by
    rcases d.radius_cases with hr | hr <;> omega
  let : Finite (d.labelBall a 2) := Finite.of_injective
    (Subgroup.inclusion (d.labelBall_le_stabilizer a 2 hr (by have := h.five_le; omega)))
    (Subgroup.inclusion_injective _)
  have hc := Nat.card_le_card_of_injective u hu
  have he : Nat.card (Option (Option (Fin 3 × ZMod 2))) = 8 := by
    rw [Nat.card_eq_fintype_card]
    simp
  exact he ▸ hc

/-- The unconditional elementary-group size range preceding (6.12.3). -/
theorem radiusThree_radiusTwo_card_bounds (d : CanonicalLabelSetup F s)
    (h : LargeTreeSource F s) (hr : d.radius = 3)
    (a : RankTwo.Vertex F) (ha : a.type = d.side) :
    IsElementaryAbelian 2 (d.labelBall a 2) ∧
      8 ≤ Nat.card (d.labelBall a 2) ∧ Nat.card (d.labelBall a 2) ≤ 16 := by
  obtain ⟨he, hcard⟩ := d.radiusTwo_card_le h.action.toCubicTreeAction (by omega)
    (by have := h.five_le; omega) a ha
  exact ⟨he, d.radiusTwo_card_ge h a ha, hcard⟩

end CanonicalLabelSetup
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
