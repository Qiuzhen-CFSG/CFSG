module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceIncidence

/-!
# Triangles in the original cubic incidence graph

A source point on V other than W supplements D in the original Sylow
group. Conjugation gives the same statement on every line through W.
Two commuting other points therefore generate, together with D, a
3-group containing the Sylow groups attached to both lines. Sylow
maximality and the unique maximum abelian subgroup identify the lines.
After transporting an arbitrary incident pair, this says that every
collinearity triangle lies on one source line.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 45.10, p.248.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

omit [Finite G] in
theorem point_card {U : Subgroup G} (hU : U ∈ c.points) : Nat.card U = 3 := by
  obtain ⟨g, rfl⟩ := hU
  change Nat.card (c.W.map (MulAut.conj g).toMonoidHom) = 3
  rw [card_map_of_injective (MulAut.conj g).injective, c.line_card]

omit [Finite G] in
theorem line_cardinality {L : Subgroup G} (hL : L ∈ c.lines) : Nat.card L = 81 := by
  obtain ⟨g, rfl⟩ := hL
  change Nat.card (c.V.map (MulAut.conj g).toMonoidHom) = 81
  rw [card_map_of_injective (MulAut.conj g).injective, c.kernel_card]

omit [Finite G] in
theorem line_commutative {L : Subgroup G} (hL : L ∈ c.lines) : IsMulCommutative L := by
  obtain ⟨g, rfl⟩ := hL
  let : IsMulCommutative c.V := c.kernel_elementary.toIsMulCommutative
  change IsMulCommutative (c.V.map (MulAut.conj g).toMonoidHom)
  infer_instance

omit [Finite G] in
theorem points_on_line_commute {U U' L : Subgroup G} (hL : L ∈ c.lines)
    (hUL : U ≤ L) (hU'L : U' ≤ L) : U ≤ Subgroup.centralizer (U' : Set G) := by
  let : IsMulCommutative L := c.line_commutative hL
  exact hUL.trans (L.le_centralizer.trans (centralizer_le hU'L))

omit [Finite G] in
theorem neighbor_centralizes {U U' : Subgroup G} (hn : U' ∈ c.neighbors U) :
    U ≤ Subgroup.centralizer (U' : Set G) := by
  obtain ⟨_, _, L, hL, hUL, hU'L⟩ := hn
  exact c.points_on_line_commute hL hUL hU'L

theorem odd_join_other_point {U : Subgroup G}
    (hU : U ∈ c.pointsOn c.V) (hne : U ≠ c.W) : c.D ⊔ U = c.Q := by
  let R := c.D ⊔ U
  have hRQ : R ≤ c.Q := sup_le le_sup_right (hU.2.trans le_sup_left)
  have hi : c.D.relIndex c.Q = 3 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) c.D c.Q bot_le le_sup_right
    simp only [relIndex_bot_left, c.odd_card, c.sylow_card] at hh
    omega
  have hm := relIndex_mul_relIndex c.D R c.Q le_sup_left hRQ
  rw [hi] at hm
  have hn : c.D.relIndex R ≠ 1 := by
    intro he
    have hUD : U ≤ c.D := le_sup_right.trans (relIndex_eq_one.mp he)
    exact hne ((c.kernelLines_le_odd_iff (c.pointsOn_base ▸ hU)).mp hUD)
  have hd : c.D.relIndex R ∣ 3 := ⟨R.relIndex c.Q, hm.symm⟩
  have he := ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left hn
  rw [he] at hm
  exact le_antisymm hRQ (relIndex_eq_one.mp (by omega : R.relIndex c.Q = 1))

/-- The second point of a line through W supplies its entire line over D. -/
theorem line_le_odd_join_other_point {U L : Subgroup G}
    (hU : U ∈ c.points) (hne : U ≠ c.W)
    (hL : L ∈ c.linesThrough c.W) (hUL : U ≤ L) : L ≤ c.D ⊔ U := by
  obtain ⟨g, hg, rfl⟩ := c.linesThrough_base ▸ hL
  have hUg : U.conjBy g⁻¹ ≤ c.V := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hUL
    change U.conjBy g⁻¹ ≤ (c.V.conjBy g).conjBy g⁻¹ at hh
    simpa only [conjBy_inv] using hh
  have hne' : U.conjBy g⁻¹ ≠ c.W := by
    intro he
    have hh := congrArg (fun A : Subgroup G => A.conjBy g) he
    have hw : c.W.conjBy g = c.W := mem_normalizer_iff_map_conj_eq.mp hg
    exact hne (by simpa only [conjBy_inv', hw] using hh)
  have he := c.odd_join_other_point ⟨c.point_conjugate_mem hU g⁻¹, hUg⟩ hne'
  have hb : c.V ≤ c.D ⊔ U.conjBy g⁻¹ := he.symm ▸ le_sup_left
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hb
  have hd : c.D.conjBy g = c.D := mem_normalizer_iff_map_conj_eq.mp
    (CubicLine.normalizer_normalizes_oddKernel c.W hg)
  change c.V.conjBy g ≤ (c.D ⊔ U.conjBy g⁻¹).conjBy g at hh
  change c.V.conjBy g ≤ c.D ⊔ U
  change c.V.conjBy g ≤ (c.D ⊔ U.conjBy g⁻¹).map (MulAut.conj g).toMonoidHom at hh
  rw [Subgroup.map_sup] at hh
  change c.V.conjBy g ≤ c.D.conjBy g ⊔ (U.conjBy g⁻¹).conjBy g at hh
  simpa only [hd, conjBy_inv'] using hh

theorem lines_equal_in_common_three_group {L L' R : Subgroup G}
    (hL : L ∈ c.linesThrough c.W) (hL' : L' ∈ c.linesThrough c.W)
    (hR : IsPGroup 3 R) (hDR : c.D ≤ R) (hLR : L ≤ R) (hL'R : L' ≤ R) : L' = L := by
  obtain ⟨g, hg, rfl⟩ := c.linesThrough_base ▸ hL
  let T := c.sylow.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hT : (T : Subgroup G) = c.Q.conjBy g := by
    change (c.sylow : Subgroup G).map (MulAut.conj g).toMonoidHom = _
    rw [c.sylow_eq]
    rfl
  have hd : c.D.conjBy g = c.D := mem_normalizer_iff_map_conj_eq.mp
    (CubicLine.normalizer_normalizes_oddKernel c.W hg)
  have hTR : (T : Subgroup G) ≤ R := by
    rw [hT]
    change (c.V ⊔ c.D).map (MulAut.conj g).toMonoidHom ≤ R
    rw [Subgroup.map_sup]
    change c.V.conjBy g ⊔ c.D.conjBy g ≤ R
    rw [hd]
    exact sup_le hLR hDR
  have heR : R = c.Q.conjBy g := (T.is_maximal' hR hTR).trans hT
  have hLQ : L'.conjBy g⁻¹ ≤ c.Q := by
    rw [heR] at hL'R
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hL'R
    change L'.conjBy g⁻¹ ≤ (c.Q.conjBy g).conjBy g⁻¹ at hh
    simpa only [conjBy_inv] using hh
  have hcomm := c.line_commutative (c.line_conjugate_mem hL'.1 g⁻¹)
  have he := (c.maximum (L'.conjBy g⁻¹) hcomm hLQ).2 (by
    rw [c.line_cardinality (c.line_conjugate_mem hL'.1 g⁻¹)])
  have hh := congrArg (fun A : Subgroup G => A.conjBy g) he
  simpa only [conjBy_inv'] using hh

/-- Commuting neighbors of W belong to the same source line through W. -/
theorem commuting_neighbors_line {U U' : Subgroup G}
    (hU : U ∈ c.neighbors c.W) (hU' : U' ∈ c.neighbors c.W)
    (hcomm : U ≤ Subgroup.centralizer (U' : Set G)) :
    ∃ L ∈ c.lines, c.W ≤ L ∧ U ≤ L ∧ U' ≤ L := by
  obtain ⟨hUp, hUne, L, hL, hWL, hUL⟩ := hU
  obtain ⟨hU'p, hU'ne, L', hL', hWL', hU'L'⟩ := hU'
  let R := c.D ⊔ (U ⊔ U')
  have hp : IsPGroup 3 (U ⊔ U' : Subgroup G) :=
    (IsPGroup.of_card (n := 1) (c.point_card hUp)).to_sup_of_normal_right'
      (IsPGroup.of_card (n := 1) (c.point_card hU'p))
      (hcomm.trans (centralizer_le_normalizer _))
  have hUN : U ≤ normalizer (c.W : Set G) :=
    (c.points_on_line_commute hL hUL hWL).trans (centralizer_le_normalizer _)
  have hU'N : U' ≤ normalizer (c.W : Set G) :=
    (c.points_on_line_commute hL' hU'L' hWL').trans (centralizer_le_normalizer _)
  have hR : IsPGroup 3 R := (IsPGroup.of_card (n := 5) c.odd_card).to_sup_of_normal_left'
    hp ((sup_le hUN hU'N).trans (CubicLine.normalizer_normalizes_oddKernel c.W))
  have hLR : L ≤ R := (c.line_le_odd_join_other_point hUp hUne ⟨hL, hWL⟩ hUL).trans
    (sup_le_sup_left le_sup_left _)
  have hL'R : L' ≤ R := (c.line_le_odd_join_other_point hU'p hU'ne ⟨hL', hWL'⟩ hU'L').trans
    (sup_le_sup_left le_sup_right _)
  have he := c.lines_equal_in_common_three_group ⟨hL, hWL⟩ ⟨hL', hWL'⟩ hR le_sup_left hLR hL'R
  exact ⟨L, hL, hWL, hUL, he ▸ hU'L'⟩

omit [Finite G] in
theorem neighbor_conjugate {U U' : Subgroup G} (hn : U' ∈ c.neighbors U) (g : G) :
    U'.conjBy g ∈ c.neighbors (U.conjBy g) := by
  obtain ⟨hU', hne, L, hL, hUL, hU'L⟩ := hn
  refine ⟨c.point_conjugate_mem hU' g, ?_, L.conjBy g,
    c.line_conjugate_mem hL g, map_mono hUL, map_mono hU'L⟩
  intro he
  exact hne (map_injective (MulAut.conj g).injective he)

/-- Every triangle of the original collinearity graph lies on a single line. -/
theorem triangle_on_line (U U' U'' : c.points)
    (h01 : c.collinearity.Adj U U') (h02 : c.collinearity.Adj U U'')
    (h12 : c.collinearity.Adj U' U'') :
    ∃ L ∈ c.lines, U.val ≤ L ∧ U'.val ≤ L ∧ U''.val ≤ L := by
  obtain ⟨g, hg⟩ := U.property
  have hUg : U.val.conjBy g⁻¹ = c.W := by rw [hg, conjBy_inv]
  have h1 := c.neighbor_conjugate h01 g⁻¹
  have h2 := c.neighbor_conjugate h02 g⁻¹
  rw [hUg] at h1 h2
  have hc := c.neighbor_centralizes (c.neighbor_conjugate h12 g⁻¹)
  obtain ⟨L, hL, hWL, h1L, h2L⟩ := c.commuting_neighbors_line h1 h2 hc
  refine ⟨L.conjBy g, c.line_conjugate_mem hL g, ?_, ?_, ?_⟩
  · rw [hg]
    exact map_mono hWL
  · have hh := map_mono (f := (MulAut.conj g).toMonoidHom) h1L
    change (U'.val.conjBy g⁻¹).conjBy g ≤ L.conjBy g at hh
    simpa only [conjBy_inv'] using hh
  · have hh := map_mono (f := (MulAut.conj g).toMonoidHom) h2L
    change (U''.val.conjBy g⁻¹).conjBy g ≤ L.conjBy g at hh
    simpa only [conjBy_inv'] using hh

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
