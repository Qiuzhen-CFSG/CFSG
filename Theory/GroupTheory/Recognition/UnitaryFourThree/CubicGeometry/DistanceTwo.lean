module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.TwoSteps

/-!
# The complete original distance-two sphere

The selected opposite cubic has a free D-orbit of order 243, and each
orbit point has four common neighbors with W. These 972 incidences
inject into the 972 two-step paths from W, hence exhaust them. Every
point at distance two therefore belongs to this orbit. In particular D
acts regularly on the sphere, and every opposite pair generates the
actual SL₂(3) subgroup already constructed from the quaternion factor.

Source: Aschbacher, *Sporadic Groups* (1994), 45.10(6)–(7), p.248.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

def oddPointOrbit (Y : Subgroup G) : Set c.points :=
  {U | ∃ d ∈ c.D, U.val = Y.conjBy d}

theorem oddPointOrbit_card {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W) :
    Nat.card (c.oddPointOrbit Y) = 243 := by
  let f : c.oddPointOrbit Y → {U : Subgroup G // ∃ d ∈ c.D, U = Y.conjBy d} :=
    fun U => ⟨U.val.val, U.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro U U' he
      have hh : U.val.val = U'.val.val :=
        congrArg (fun a : {U : Subgroup G // ∃ d ∈ c.D, U = Y.conjBy d} => a.val) he
      exact Subtype.ext (Subtype.ext hh)
    · rintro ⟨U, d, hd, he⟩
      have hu : U ∈ c.points := he ▸ c.point_conjugate_mem
        (c.cubic_in_oppositeFactor_is_point hYL hY) d
      exact ⟨⟨⟨U, hu⟩, d, hd, he⟩, rfl⟩
  rw [Nat.card_eq_of_bijective f hf]
  exact c.opposite_cubic_orbit_card hYL hY hne

theorem mem_oddPointOrbit_distance_two {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W)
    {U : c.points} (hU : U ∈ c.oddPointOrbit Y) :
    c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2 := by
  obtain ⟨d, hd, he⟩ := hU
  have hu : U = ⟨Y.conjBy d,
      c.point_conjugate_mem (c.cubic_in_oppositeFactor_is_point hYL hY) d⟩ := Subtype.ext he
  rw [hu]
  exact c.opposite_cubic_conjugate_distance_two hYL hY hne d hd

theorem oddPointOrbit_common_neighbors_card {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W)
    (hK : c.K ≤ normalizer (Y : Set G)) {U : c.points} (hU : U ∈ c.oddPointOrbit Y) :
    Nat.card (c.collinearity.commonNeighbors ⟨c.W, c.point_mem⟩ U) = 4 := by
  obtain ⟨d, hd, he⟩ := hU
  have hu : U = ⟨Y.conjBy d,
      c.point_conjugate_mem (c.cubic_in_oppositeFactor_is_point hYL hY) d⟩ := Subtype.ext he
  rw [hu]
  exact c.opposite_conjugate_common_neighbors_card hYL hY hne hK d hd

/-- Every point at distance two belongs to the actual free D-orbit. -/
theorem distance_two_mem_oddPointOrbit {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W)
    (hK : c.K ≤ normalizer (Y : Set G)) {U : c.points}
    (hU : c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2) : U ∈ c.oddPointOrbit Y := by
  classical
  let W : c.points := ⟨c.W, c.point_mem⟩
  let O := c.oddPointOrbit Y
  let T := Σ X : O, c.collinearity.commonNeighbors W X.val
  have ht : Nat.card T = 972 := by
    let : Fintype O := Fintype.ofFinite _
    change Nat.card (Σ X : O, c.collinearity.commonNeighbors W X.val) = 972
    rw [Nat.card_sigma]
    have hc (X : O) : Nat.card (c.collinearity.commonNeighbors W X.val) = 4 :=
      c.oddPointOrbit_common_neighbors_card hYL hY hne hK X.property
    simp_rw [hc]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [← Nat.card_eq_fintype_card, c.oddPointOrbit_card hYL hY hne]
  have hdist (X : O) := c.collinearity.edist_eq_two_iff.mp
    (c.mem_oddPointOrbit_distance_two hYL hY hne X.property)
  let f : T → c.twoSteps W := fun a =>
    ⟨⟨a.2.val, a.2.property.1⟩,
      ⟨a.1.val, ⟨c.collinearity.adj_symm a.2.property.2, (hdist a.1).2.1⟩,
        Ne.symm (hdist a.1).1⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨X, Z⟩ ⟨X', Z'⟩ he
    have heX : X = X' := Subtype.ext (congrArg (fun a : c.twoSteps W => a.2.val) he)
    subst X'
    have heZ : Z = Z' := Subtype.ext (congrArg (fun a : c.twoSteps W => a.1.val) he)
    subst Z'
    rfl
  let : Finite (c.twoSteps W) := by unfold twoSteps; infer_instance
  have hsurj : Function.Surjective f :=
    (hf.bijective_of_nat_card_le (by rw [c.twoSteps_card, ht])).2
  obtain ⟨hneU, hnaU, Z, hWZ, hUZ⟩ := c.collinearity.edist_eq_two_iff.mp hU
  let a : c.twoSteps W := ⟨⟨Z, hWZ⟩,
    ⟨U, ⟨c.collinearity.adj_symm hUZ, hnaU⟩, Ne.symm hneU⟩⟩
  obtain ⟨b, hb⟩ := hsurj a
  have he : b.1.val = U := congrArg (fun a : c.twoSteps W => a.2.val) hb
  exact he ▸ b.1.property

theorem distance_two_sphere_card : Nat.card
    {U : c.points // c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2} = 243 := by
  obtain ⟨Y, hYL, hY, hne, -, hK⟩ := c.exists_complement_fixed_opposite_cubic
  have he : {U : c.points | c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2} =
      c.oddPointOrbit Y := by
    ext U
    exact ⟨c.distance_two_mem_oddPointOrbit hYL hY hne hK,
      c.mem_oddPointOrbit_distance_two hYL hY hne⟩
  change Nat.card {U : c.points | c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2} = 243
  rw [he]
  exact c.oddPointOrbit_card hYL hY hne

theorem distance_two_common_neighbors_card {U : c.points}
    (hU : c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2) :
    Nat.card (c.collinearity.commonNeighbors ⟨c.W, c.point_mem⟩ U) = 4 := by
  obtain ⟨Y, hYL, hY, hne, -, hK⟩ := c.exists_complement_fixed_opposite_cubic
  exact c.oddPointOrbit_common_neighbors_card hYL hY hne hK
    (c.distance_two_mem_oddPointOrbit hYL hY hne hK hU)

theorem distance_two_pair_model {U : c.points}
    (hU : c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2) :
    Nonempty ((c.W ⊔ U.val : Subgroup G) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  obtain ⟨Y, hYL, hY, hne, hgen, hK⟩ := c.exists_complement_fixed_opposite_cubic
  obtain ⟨d, hd, he⟩ := c.distance_two_mem_oddPointOrbit hYL hY hne hK hU
  have hw : c.W.conjBy d = c.W :=
    mem_normalizer_iff_map_conj_eq.mp (c.complement_product.ge (mem_sup_left hd))
  have hj : (c.W ⊔ Y).map (MulAut.conj d).toMonoidHom = c.W ⊔ U.val := by
    rw [Subgroup.map_sup]
    change c.W.conjBy d ⊔ Y.conjBy d = c.W ⊔ U.val
    rw [hw, ← he]
  obtain ⟨e⟩ := c.oppositeFactor_model
  exact ⟨(MulEquiv.subgroupCongr hj).symm.trans
    (((c.W ⊔ Y).equivMapOfInjective (MulAut.conj d).toMonoidHom
      (MulAut.conj d).injective).symm.trans ((MulEquiv.subgroupCongr hgen).trans e))⟩

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
