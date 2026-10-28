module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.OppositeDistance

/-!
# Four common neighbors of the original opposite pair

The odd subgroup D fixes every line through W. Hence the order-48
complement is transitive on those four lines. Since this complement
fixes the selected opposite cubic, conjugates of the second cubic axis
supply a common neighbor on each line. The triangle theorem and unique
line property allow at most one common neighbor on each line.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 45.10(6), p.248.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

omit [Finite G] in
theorem odd_normalizes_kernel : c.D ≤ normalizer (c.V : Set G) := by
  have hd : c.D ≤ (c.sylow : Subgroup G) := c.sylow_eq.symm ▸ le_sup_right
  exact (hd.trans (c.sylow : Subgroup G).le_normalizer).trans
    (c.common_normalizer.le.trans inf_le_left)

theorem odd_fixes_incident_line {L : Subgroup G} (hL : L ∈ c.linesThrough c.W) :
    c.D ≤ normalizer (L : Set G) := by
  obtain ⟨g, hg, rfl⟩ := c.linesThrough_base ▸ hL
  have hd : c.D.conjBy g = c.D := mem_normalizer_iff_map_conj_eq.mp
    (CubicLine.normalizer_normalizes_oddKernel c.W hg)
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom) c.odd_normalizes_kernel
  rw [map_equiv_normalizer_eq] at hh
  change c.D.conjBy g ≤ normalizer (c.V.conjBy g : Set G) at hh
  rwa [hd] at hh

/-- The actual complement acts transitively on the four lines through W. -/
theorem complement_incident_line {L : Subgroup G} (hL : L ∈ c.linesThrough c.W) :
    ∃ k ∈ c.K, L = c.V.conjBy k := by
  obtain ⟨g, hg, rfl⟩ := c.linesThrough_base ▸ hL
  have hn : c.K ≤ normalizer (c.D : Set G) :=
    (c.complement_le.trans inf_le_right).trans (CubicLine.normalizer_normalizes_oddKernel c.W)
  have hm : g ∈ (c.K : Set G) * (c.D : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right c.K c.D hn, sup_comm, ← c.complement_product]
    exact hg
  obtain ⟨k, hk, d, hd, he⟩ := hm
  change k * d = g at he
  refine ⟨k, hk, ?_⟩
  rw [← he, conjBy_mul]
  exact congrArg (fun A : Subgroup G => A.conjBy k)
    (mem_normalizer_iff_map_conj_eq.mp (c.odd_normalizes_kernel hd))

/-- For a noncollinear pair, a line through its first point contains at most
one common neighbor. -/
theorem common_neighbors_on_line_unique (U U' Z Z' : c.points)
    (hna : ¬c.collinearity.Adj U U') (hne : U ≠ U')
    (hZ : Z ∈ c.collinearity.commonNeighbors U U')
    (hZ' : Z' ∈ c.collinearity.commonNeighbors U U')
    {L : Subgroup G} (hL : L ∈ c.linesThrough U.val)
    (hZL : Z.val ≤ L) (hZ'L : Z'.val ≤ L) : Z = Z' := by
  by_contra hzz
  have hzzv : Z'.val ≠ Z.val := fun he => hzz (Subtype.ext he.symm)
  have hZZ : c.collinearity.Adj Z Z' := ⟨Z'.property, hzzv, L, hL.1, hZL, hZ'L⟩
  obtain ⟨M, hM, hU'M, hZM, hZ'M⟩ := c.triangle_on_line U' Z Z' hZ.2 hZ'.2 hZZ
  have he : M = L := c.line_unique Z.property Z'.property hL.1 hM hzzv
    hZL hZM hZ'L hZ'M
  exact hna ⟨U'.property, fun he => hne (Subtype.ext he.symm), L, hL.1,
    hL.2, he ▸ hU'M⟩

private noncomputable def commonNeighborsLinesEquiv (U U' : c.points)
    (hna : ¬c.collinearity.Adj U U') (hne : U ≠ U')
    (hex : ∀ L : c.linesThrough U.val, ∃ Z : c.collinearity.commonNeighbors U U',
      Z.val.val ≤ L.val) :
    c.collinearity.commonNeighbors U U' ≃ c.linesThrough U.val := by
  classical
  have hs (Z : c.collinearity.commonNeighbors U U') :
      ∃ L : c.linesThrough U.val, Z.val.val ≤ L.val := by
    obtain ⟨-, -, L, hL, hUL, hZL⟩ := Z.property.1
    exact ⟨⟨L, hL, hUL⟩, hZL⟩
  let f (Z : c.collinearity.commonNeighbors U U') : c.linesThrough U.val := (hs Z).choose
  have hf (Z : c.collinearity.commonNeighbors U U') : Z.val.val ≤ (f Z).val := (hs Z).choose_spec
  apply Equiv.ofBijective f
  constructor
  · intro Z Z' he
    apply Subtype.ext
    exact c.common_neighbors_on_line_unique U U' Z.val Z'.val hna hne
      Z.property Z'.property (f Z).property (hf Z) (he ▸ hf Z')
  · intro L
    obtain ⟨Z, hZL⟩ := hex L
    refine ⟨Z, Subtype.ext ?_⟩
    exact (c.line_unique U.property Z.val.property (f Z).property.1 L.property.1
      Z.property.1.2.1 (f Z).property.2 L.property.2 (hf Z) hZL).symm

theorem opposite_common_neighbor_on_each_line {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W)
    (hK : c.K ≤ normalizer (Y : Set G))
    (L : c.linesThrough c.W) :
    ∃ Z : c.collinearity.commonNeighbors ⟨c.W, c.point_mem⟩
      ⟨Y, c.cubic_in_oppositeFactor_is_point hYL hY⟩, Z.val.val ≤ L.val := by
  obtain ⟨k, hk, he⟩ := c.complement_incident_line L.property
  have hw : c.W.conjBy k = c.W :=
    mem_normalizer_iff_map_conj_eq.mp ((c.complement_le hk).2)
  have hy : Y.conjBy k = Y := mem_normalizer_iff_map_conj_eq.mp (hK hk)
  have hWZ := c.neighbor_conjugate c.otherAxis_neighbor k
  rw [hw] at hWZ
  have hAY : c.collinearity.Adj ⟨c.otherAxis, c.otherAxis_is_point⟩
      ⟨Y, c.cubic_in_oppositeFactor_is_point hYL hY⟩ :=
    c.opposite_cubic_common_neighbor hYL hY hne
  have hYZ := c.neighbor_conjugate (c.collinearity.adj_symm hAY) k
  rw [hy] at hYZ
  refine ⟨⟨⟨c.otherAxis.conjBy k, c.point_conjugate_mem c.otherAxis_is_point k⟩, hWZ, hYZ⟩, ?_⟩
  rw [he]
  exact map_mono c.otherAxis_le_kernel

theorem opposite_common_neighbors_card {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W)
    (hK : c.K ≤ normalizer (Y : Set G)) :
    Nat.card (c.collinearity.commonNeighbors ⟨c.W, c.point_mem⟩
      ⟨Y, c.cubic_in_oppositeFactor_is_point hYL hY⟩) = 4 := by
  rw [Nat.card_congr (c.commonNeighborsLinesEquiv ⟨c.W, c.point_mem⟩
    ⟨Y, c.cubic_in_oppositeFactor_is_point hYL hY⟩
    (c.opposite_cubic_not_collinear hYL hY hne)
    (fun he => hne (congrArg Subtype.val he).symm)
    (c.opposite_common_neighbor_on_each_line hYL hY hne hK))]
  exact c.linesThrough_base_card

omit [Finite G] in
def conjugatePoint (U : c.points) (g : G) : c.points :=
  ⟨U.val.conjBy g, c.point_conjugate_mem U.property g⟩

omit [Finite G] in
def commonNeighborsConjugateEquiv (U U' : c.points) (g : G) :
    c.collinearity.commonNeighbors U U' ≃
      c.collinearity.commonNeighbors (c.conjugatePoint U g) (c.conjugatePoint U' g) where
  toFun Z := ⟨c.conjugatePoint Z.val g,
    c.neighbor_conjugate Z.property.1 g, c.neighbor_conjugate Z.property.2 g⟩
  invFun Z := ⟨c.conjugatePoint Z.val g⁻¹, by
    constructor
    · have hh := c.neighbor_conjugate Z.property.1 g⁻¹
      change Z.val.val.conjBy g⁻¹ ∈ c.neighbors ((U.val.conjBy g).conjBy g⁻¹) at hh
      change Z.val.val.conjBy g⁻¹ ∈ c.neighbors U.val
      simpa only [conjBy_inv] using hh
    · have hh := c.neighbor_conjugate Z.property.2 g⁻¹
      change Z.val.val.conjBy g⁻¹ ∈ c.neighbors ((U'.val.conjBy g).conjBy g⁻¹) at hh
      change Z.val.val.conjBy g⁻¹ ∈ c.neighbors U'.val
      simpa only [conjBy_inv] using hh⟩
  left_inv Z := Subtype.ext (Subtype.ext (conjBy_inv _ _))
  right_inv Z := Subtype.ext (Subtype.ext (conjBy_inv' _ _))

theorem opposite_conjugate_common_neighbors_card {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W)
    (hK : c.K ≤ normalizer (Y : Set G)) (d : G) (hd : d ∈ c.D) :
    Nat.card (c.collinearity.commonNeighbors ⟨c.W, c.point_mem⟩
      ⟨Y.conjBy d, c.point_conjugate_mem (c.cubic_in_oppositeFactor_is_point hYL hY) d⟩) = 4 := by
  have hw : c.conjugatePoint ⟨c.W, c.point_mem⟩ d = ⟨c.W, c.point_mem⟩ :=
    Subtype.ext (mem_normalizer_iff_map_conj_eq.mp (c.complement_product.ge (mem_sup_left hd)))
  have hh := Nat.card_congr (c.commonNeighborsConjugateEquiv ⟨c.W, c.point_mem⟩
    ⟨Y, c.cubic_in_oppositeFactor_is_point hYL hY⟩ d)
  rw [hw, c.opposite_common_neighbors_card hYL hY hne hK] at hh
  exact hh.symm

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
