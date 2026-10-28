module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.OppositeFactor

/-!
# The regular extraspecial orbit of the original opposite cubic

The selected second cubic is an actual conjugate of W inside its SL₂(3)
factor. An element of D normalizing that cubic centralizes it, because
its cube is one and the cubic automorphism group has order two. It also
centralizes W, hence the generated SL₂(3) and its central involution z.
The source identity D ∩ C(z) = W puts it in the center of SL₂(3), where
its order divides two and three. Thus the stabilizer in D is trivial.
The original complement stabilizes the selected point, giving a regular
orbit of size 243 and the exact full point-normalizer intersection.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 45.10(6)–(7), p.248.
The identification of this orbit with the entire distance-two sphere is
separate; no such identification is assumed here.
-/

public section
open Subgroup
open scoped Pointwise

private theorem cubic_conjugate_in_twenty_four {G : Type*} [Group G] [Finite G]
    (L X Y : Subgroup G) (hL : Nat.card L = 24) (hXL : X ≤ L) (hYL : Y ≤ L)
    (hX : Nat.card X = 3) (hY : Nat.card Y = 3) :
    ∃ g ∈ L, X.conjBy g = Y := by
  have sylow (Z : Subgroup G) (hZL : Z ≤ L) (hZ : Nat.card Z = 3) :
      ∃ T : Sylow 3 L, (T : Subgroup L) = Z.subgroupOf L := by
    have hc : Nat.card (Z.subgroupOf L) = 3 :=
      (Nat.card_congr (subgroupOfEquivOfLe hZL).toEquiv).trans hZ
    have hi : ¬3 ∣ (Z.subgroupOf L).index := by
      have hh := (Z.subgroupOf L).card_mul_index
      rw [hc, hL] at hh
      have he : (Z.subgroupOf L).index = 8 := by omega
      rw [he]
      decide
    exact ⟨(IsPGroup.of_card (n := 1) hc).toSylow hi, rfl⟩
  obtain ⟨S, hS⟩ := sylow X hXL hX
  obtain ⟨T, hT⟩ := sylow Y hYL hY
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L S T
  have hh := congrArg Sylow.toSubgroup hg
  change (S : Subgroup L).map (MulAut.conj g).toMonoidHom = (T : Subgroup L) at hh
  rw [hS, hT] at hh
  have hm := congrArg (fun Z : Subgroup L => Z.map L.subtype) hh
  have hcomm : L.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp L.subtype := by
    ext x
    rfl
  rw [map_map, hcomm, ← map_map, map_subgroupOf_eq_of_le hXL,
    map_subgroupOf_eq_of_le hYL] at hm
  exact ⟨g, g.property, hm⟩

private theorem cube_normalizer_centralizes_cubic {G : Type*} [Group G] [Finite G]
    (Y : Subgroup G) (hY : Nat.card Y = 3) (x : G) (hx : x ^ 3 = 1)
    (hn : x ∈ normalizer (Y : Set G)) : x ∈ Subgroup.centralizer (Y : Set G) := by
  let : IsCyclic Y := isCyclic_of_prime_card hY
  let a := Y.normalizerMonoidHom ⟨x, hn⟩
  have ha3 : a ^ 3 = 1 := by
    change (Y.normalizerMonoidHom ⟨x, hn⟩) ^ 3 = 1
    rw [← map_pow]
    have hh : (⟨x, hn⟩ : normalizer (Y : Set G)) ^ 3 = 1 := Subtype.ext hx
    rw [hh, map_one]
  have hc : Nat.card (MulAut Y) = 2 := by rw [IsCyclic.card_mulAut, hY]; decide
  have ha2 : a ^ 2 = 1 := hc ▸ pow_card_eq_one' (x := a)
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha2) (orderOf_dvd_of_pow_eq_one ha3)
  have ha : a = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  intro y hy
  have he := congrArg (fun f : MulAut Y => (f ⟨y, hy⟩ : G)) ha
  change x * y * x⁻¹ = y at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

theorem oppositeFactor_cubic_conjugate {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) :
    ∃ g ∈ c.oppositeFactor, c.W.conjBy g = Y :=
  cubic_conjugate_in_twenty_four c.oppositeFactor c.W Y
    c.oppositeFactor_card le_sup_right hYL c.line_card hY

theorem cubic_in_oppositeFactor_is_point {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) : Y ∈ c.points := by
  obtain ⟨g, _, he⟩ := c.oppositeFactor_cubic_conjugate hYL hY
  exact ⟨g, he.symm⟩

theorem oppositeFactor_center_card : Nat.card (center c.oppositeFactor) = 2 := by
  let e := c.oppositeFactor_model.some.trans
    GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.symm
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact GLS3.Chapter5.SchurPresentation.binaryTetrahedral_center_card

theorem opposite_cubic_odd_stabilizer {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W) :
    c.D ⊓ normalizer (Y : Set G) = ⊥ := by
  have hgen := (SL23CubicGeometry.geometry_of_equiv c.oppositeFactor c.W
    c.oppositeFactor_model.some le_sup_right c.line_card).2.1 ⟨Y, hYL, hY, hne⟩
  apply bot_unique
  intro d hd
  have hdW := CubicLine.oddKernel_centralizes c.W c.line_card hd.1
  have hdY := cube_normalizer_centralizes_cubic Y hY d (c.odd_cube d hd.1) hd.2
  have hLd : c.oppositeFactor ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [← hgen]
    exact sup_le (fun w hw => mem_centralizer_singleton_iff.mpr (hdW w hw))
      (fun y hy => mem_centralizer_singleton_iff.mpr (hdY y hy))
  have hdz : d ∈ centralizer z := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hLd c.involution_mem_oppositeFactor)).symm
  have hdL : d ∈ c.oppositeFactor := mem_sup_right (c.odd_fixed.le ⟨hd.1, hdz⟩)
  let a : center c.oppositeFactor := ⟨⟨d, hdL⟩, mem_center_iff.mpr (fun l =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (hLd l.property)))⟩
  have hd2 : d ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := a)
    rw [c.oppositeFactor_center_card] at hh
    exact congrArg (fun x : center c.oppositeFactor => ((x : c.oppositeFactor) : G)) hh
  have hdiv := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hd2)
    (orderOf_dvd_of_pow_eq_one (c.odd_cube d hd.1))
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdiv)

/-- The selected opposite point has a free D-orbit of size 243. -/
theorem opposite_cubic_orbit_card {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W) :
    Nat.card {U : Subgroup G // ∃ d ∈ c.D, U = Y.conjBy d} = 243 := by
  classical
  let : MulAction G (Subgroup G) := MulAction.compHom (Subgroup G) MulAut.conj
  have hs : MulAction.stabilizer c.D Y = ⊥ := by
    apply bot_unique
    intro d hd
    have hn : (d : G) ∈ normalizer (Y : Set G) := mem_normalizer_iff_map_conj_eq.mpr hd
    have hd0 : (d : G) ∈ (⊥ : Subgroup G) :=
      c.opposite_cubic_odd_stabilizer hYL hY hne ▸ ⟨d.property, hn⟩
    exact Subtype.ext (mem_bot.mp hd0)
  have he : {U : Subgroup G | ∃ d ∈ c.D, U = Y.conjBy d} = MulAction.orbit c.D Y := by
    ext U
    exact ⟨fun ⟨d, hd, he⟩ => ⟨⟨d, hd⟩, he.symm⟩,
      fun ⟨d, hd⟩ => ⟨d, d.property, hd.symm⟩⟩
  change Nat.card {U : Subgroup G | ∃ d ∈ c.D, U = Y.conjBy d} = 243
  rw [he, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer c.D Y)]
  change (MulAction.stabilizer c.D Y).index = 243
  rw [hs, index_bot, c.odd_card]

theorem opposite_cubic_not_collinear {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W) :
    Y ∉ c.neighbors c.W := by
  intro hn
  have hc := le_centralizer_iff.mp (c.neighbor_centralizes hn)
  have hDW : c.W ≤ c.D := c.odd_fixed.ge.trans inf_le_left
  have hW0 : c.W ≤ ⊥ := by
    rw [← c.opposite_cubic_odd_stabilizer hYL hY hne]
    exact le_inf hDW ((le_centralizer_iff.mp hc).trans (centralizer_le_normalizer _))
  have hh := card_le_of_le hW0
  rw [c.line_card, card_bot] at hh
  omega

/-- Actual source selection, retaining the original complement and SL₂(3) pair. -/
theorem exists_regular_opposite_orbit :
    ∃ Y : Subgroup G, Y ∈ c.points ∧ Y ≠ c.W ∧ Y ∉ c.neighbors c.W ∧
      c.K ≤ normalizer (Y : Set G) ∧
      Nonempty ((c.W ⊔ Y : Subgroup G) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      c.D ⊓ normalizer (Y : Set G) = ⊥ ∧
      Nat.card {U : Subgroup G // ∃ d ∈ c.D, U = Y.conjBy d} = 243 := by
  obtain ⟨Y, hYL, hY, hne, hgen, hK⟩ := c.exists_complement_fixed_opposite_cubic
  exact ⟨Y, c.cubic_in_oppositeFactor_is_point hYL hY, hne,
    c.opposite_cubic_not_collinear hYL hY hne, hK, hgen.symm ▸ c.oppositeFactor_model,
    c.opposite_cubic_odd_stabilizer hYL hY hne, c.opposite_cubic_orbit_card hYL hY hne⟩

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
