module

public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.MarkedPlane
public import Theory.SpecificGroups.Symplectic.BinaryTransvectionCentralizers

/-!
# Marked commuting transvection products in the original C₃ system

The center of the point vertex fixes every neighboring point. In the
faithful symplectic marking it therefore fixes the orthogonal hyperplane,
so each nonidentity central element is the transvection at the base point.
Two distinct commuting conjugates correspond to distinct collinear points.

The original chamber preserves its base line and fixes its base point.
It consequently permutes the other two points and centralizes the product
of their transvections. Neighbor transitivity carries any collinear pair
to that pair. This proves precisely the intrinsic commuting-product input
used in Aschbacher–Smith 13.4.9, printed pp.906–907, while retaining the
original chamber. No ambient fusion or centralizer containment is assumed.
-/

public noncomputable section

namespace Quasithin.I5.C3Recognition
open Subgroup Matrix Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G] {S : DSystem .C3 G}
namespace SymplecticMark
variable (m : SymplecticMark S)

/-- The nonidentity center of the original point vertex is the marked transvection. -/
theorem point_center_transvection {a : S.family 0} (ha : a ∈ center (S.family 0))
    (ha1 : a ≠ 1) :
    m.hom a.val = Matrix.PSp4Three.transvection (m.point S.basePoint) 1 := by
  apply (Matrix.PSp4Three.binary_eq_one_or_transvection_of_fixes_perp
    (m.point S.basePoint) (m.point_nonzero _) (m.hom a.val) ?_).resolve_left
  · intro hh
    apply ha1
    apply Subtype.ext
    exact m.hom_injective (hh.trans (map_one _).symm)
  · intro y hy
    by_cases hy0 : y = 0
    · subst y
      exact map_zero (toLinear (m.hom a.val))
    obtain ⟨x, hx⟩ := m.point_bijective.surjective ⟨y, hy0⟩
    have hxy : m.point x = y := congrArg Subtype.val hx
    rw [← hxy] at hy ⊢
    change (m.hom a.val).val *ᵥ m.point x = m.point x
    rw [m.equivariant, S.neighborCore_fixes (S.point_center_mem_neighborCore ha)
      ((m.orthogonal _ _).mp hy)]

private theorem transvection_conj (g : G) (x : S.Point) :
    m.hom g * Matrix.PSp4Three.transvection (m.point x) 1 * (m.hom g)⁻¹ =
      Matrix.PSp4Three.transvection (m.point (g • x)) 1 := by
  rw [Matrix.PSp4Three.transvection_conjugate]
  congr 1
  exact m.equivariant g x

private theorem adjacent_pairs_transitive (x y u v : S.Point)
    (hxy : x ≠ y) (huv : u ≠ v) (hcxy : S.Collinear x y) (hcuv : S.Collinear u v) :
    ∃ g : G, g • x = u ∧ g • y = v := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G x u
  obtain ⟨b, hbu, hbv⟩ := S.point_neighbor_transporter
    (ha ▸ hcxy.smul S a) hcuv
    (fun he => hxy ((MulAction.injective a) (ha.trans he))) huv
  exact ⟨b * a, by rw [mul_smul, ha, hbu], by rw [mul_smul, hbv]⟩

/-- Every distinct collinear pair of marked transvections has a product
conjugate to an element centralized by the original chamber. -/
theorem transvection_pair_chamber (x y : S.Point) (hxy : x ≠ y)
    (hcxy : S.Collinear x y) :
    ∃ c : G, ∀ t ∈ S.T,
      Commute (m.hom t)
        (Matrix.PSp4Three.transvection (m.point (c • x)) 1 *
         Matrix.PSp4Three.transvection (m.point (c • y)) 1) := by
  let A : Set S.Point := {u | S.Inc u S.baseLine ∧ S.basePoint ≠ u}
  have hc : A.ncard = 2 := S.line_other_points_card
    (show S.Inc S.basePoint S.baseLine from ⟨1, rfl, rfl⟩)
  obtain ⟨u, v, huv, hA⟩ := Set.ncard_eq_two.mp hc
  have hu : u ∈ A := by rw [hA]; simp
  have hv : v ∈ A := by rw [hA]; simp
  have hcuv : S.Collinear u v := ⟨S.baseLine, hu.1, hv.1⟩
  have hcomm : Commute (Matrix.PSp4Three.transvection (m.point u) (1 : ZMod 2))
      (Matrix.PSp4Three.transvection (m.point v) 1) :=
    Matrix.PSp4Three.transvection_commute ((m.orthogonal _ _).mpr hcuv) _ _
  obtain ⟨c, hcx, hcy⟩ := adjacent_pairs_transitive (S := S) x y u v hxy huv hcxy hcuv
  refine ⟨c, ?_⟩
  intro t ht
  rw [hcx, hcy]
  have htp : t • S.basePoint = S.basePoint := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [S.stabilizer_basePoint]
    exact S.T_le 0 ht
  have htl : t • S.baseLine = S.baseLine := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [S.stabilizer_baseLine]
    exact S.T_le 1 ht
  have hpres {w : S.Point} (hw : w ∈ A) : t • w = u ∨ t • w = v := by
    have hh : t • w ∈ A := ⟨by simpa only [htl] using hw.1.smul S t,
      fun he => hw.2 ((MulAction.injective t) (htp.trans he))⟩
    simpa only [hA, Set.mem_insert_iff, Set.mem_singleton_iff] using hh
  have htu := hpres hu
  have htv := hpres hv
  have htuv : t • u ≠ t • v := (MulAction.injective t).ne huv
  have hprod : m.hom t *
      (Matrix.PSp4Three.transvection (m.point u) 1 *
       Matrix.PSp4Three.transvection (m.point v) 1) * (m.hom t)⁻¹ =
      Matrix.PSp4Three.transvection (m.point u) 1 *
       Matrix.PSp4Three.transvection (m.point v) 1 := by
    calc
      _ = (m.hom t * Matrix.PSp4Three.transvection (m.point u) 1 * (m.hom t)⁻¹) *
          (m.hom t * Matrix.PSp4Three.transvection (m.point v) 1 * (m.hom t)⁻¹) := by group
      _ = Matrix.PSp4Three.transvection (m.point (t • u)) 1 *
          Matrix.PSp4Three.transvection (m.point (t • v)) 1 := by
            rw [m.transvection_conj, m.transvection_conj]
      _ = _ := by
        rcases htu with hu' | hu' <;> rcases htv with hv' | hv'
        · exact (htuv (hu'.trans hv'.symm)).elim
        · rw [hu', hv']
        · rw [hu', hv']; exact hcomm.eq.symm
        · exact (htuv (hu'.trans hv'.symm)).elim
  exact mul_inv_eq_iff_eq_mul.mp hprod

/-- Intrinsic commuting products for the center of the original point vertex. -/
theorem point_center_commuting_product (m : SymplecticMark S) {a : S.family 0}
    (ha : a ∈ center (S.family 0)) (ha1 : a ≠ 1)
    (b : G) (hab : IsConj a.val b) (habc : Commute a.val b) (habn : b ≠ a.val) :
    ∃ c : G, S.T ≤ centralizer ({MulAut.conj c (a.val * b)} : Set G) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  have haτ := m.point_center_transvection ha ha1
  have hbτ : m.hom b = Matrix.PSp4Three.transvection (m.point (g • S.basePoint)) 1 := by
    rw [← hg, map_mul, map_mul, map_inv, haτ, m.transvection_conj]
  have hne : S.basePoint ≠ g • S.basePoint := by
    intro he
    apply habn
    apply m.hom_injective
    rw [hbτ, ← he, haτ]
  have hcol : S.Collinear S.basePoint (g • S.basePoint) := by
    apply (m.orthogonal _ _).mp
    apply (Matrix.PSp4Three.binary_transvection_commute_iff _ _).mp
    rw [← haτ, ← hbτ]
    exact habc.map m.hom
  obtain ⟨c, hc⟩ := m.transvection_pair_chamber _ _ hne hcol
  refine ⟨c, ?_⟩
  intro t ht
  apply mem_centralizer_singleton_iff.mpr
  apply m.hom_injective
  have he : m.hom (MulAut.conj c (a.val * b)) =
      Matrix.PSp4Three.transvection (m.point (c • S.basePoint)) 1 *
      Matrix.PSp4Three.transvection (m.point (c • (g • S.basePoint))) 1 := by
    rw [map_mul (MulAut.conj c), map_mul]
    change m.hom (c * a.val * c⁻¹) * m.hom (c * b * c⁻¹) = _
    simp only [map_mul, map_inv, haτ, hbτ, m.transvection_conj]
  simpa only [map_mul m.hom, he] using (hc t ht).eq
end SymplecticMark

/-- The original C₃ system supplies the marking used for the product calculation. -/
theorem point_center_commuting_product (S : DSystem .C3 G) {a : S.family 0}
    (ha : a ∈ center (S.family 0)) (ha1 : a ≠ 1)
    (b : G) (hab : IsConj a.val b) (habc : Commute a.val b) (habn : b ≠ a.val) :
    ∃ c : G, S.T ≤ centralizer ({MulAut.conj c (a.val * b)} : Set G) := by
  let d := S.source_local_polar_facts
  obtain ⟨m⟩ := exists_symplecticMark S
    ⟨S.c3_points_card d, S.faithful_points, S.c3_exists_noncollinear,
      fun x y h => S.source_one_or_all_triples d x y h⟩
  exact m.point_center_commuting_product ha ha1 b hab habc habn
end Quasithin.I5.C3Recognition
