module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.KernelLines

/-!
# The original cubic point–line incidence

The points and lines are the actual ambient conjugates of W and V. The
unique maximum abelian subgroup of the source Sylow group controls fusion,
so points on V are exactly its ten already constructed kernel lines.
Every incident pair is conjugate to (W,V). The point normalizer has order
243·48 and the common normalizer has order 2916, giving four lines through
each point. No orthogonal-space model or recognition premise is used.

Source: Aschbacher, *Sporadic Groups* (1994), 45.9 and 45.10(4), pp.247–248.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

/-- The source point orbit Wᴳ. -/
def points : Set (Subgroup G) := {U | ∃ g : G, U = c.W.conjBy g}

/-- The source line orbit Vᴳ. -/
def lines : Set (Subgroup G) := {L | ∃ g : G, L = c.V.conjBy g}

def pointsOn (L : Subgroup G) : Set (Subgroup G) := {U | U ∈ c.points ∧ U ≤ L}

def linesThrough (U : Subgroup G) : Set (Subgroup G) := {L | L ∈ c.lines ∧ U ≤ L}

omit [Finite G] in
theorem point_mem : c.W ∈ c.points := ⟨1, (conjBy_one _).symm⟩

omit [Finite G] in
theorem line_mem : c.V ∈ c.lines := ⟨1, (conjBy_one _).symm⟩

omit [Finite G] in
theorem point_conjugate_mem {U : Subgroup G} (hU : U ∈ c.points) (g : G) :
    U.conjBy g ∈ c.points := by
  obtain ⟨a, rfl⟩ := hU
  exact ⟨g * a, conjBy_conjBy _ _ _⟩

omit [Finite G] in
theorem line_conjugate_mem {L : Subgroup G} (hL : L ∈ c.lines) (g : G) :
    L.conjBy g ∈ c.lines := by
  obtain ⟨a, rfl⟩ := hL
  exact ⟨g * a, conjBy_conjBy _ _ _⟩

theorem pointsOn_base : c.pointsOn c.V = c.kernelLines := by
  ext U
  constructor
  · rintro ⟨⟨g, rfl⟩, hg⟩
    obtain ⟨n, hn, he⟩ := (h.cubic_kernel_source_fusion P c.actors c.actors_eq
      c.odd_split c.odd_card c.odd_extraspecial c.sylow c.sylow_eq).2.2
      c.W (c.W.conjBy g) c.line_le_kernel hg g rfl
    exact (c.mem_kernelLines_iff _).mpr ⟨n, hn, he.symm⟩
  · intro hU
    obtain ⟨g, hg, he⟩ := (c.mem_kernelLines_iff _).mp hU
    exact ⟨⟨g, he⟩, c.kernelLines_le hU⟩

/-- The global source incidence is flag transitive. -/
theorem incident_pair_conjugate {U L : Subgroup G}
    (hU : U ∈ c.points) (hL : L ∈ c.lines) (hUL : U ≤ L) :
    ∃ g : G, U = c.W.conjBy g ∧ L = c.V.conjBy g := by
  obtain ⟨a, rfl⟩ := hL
  have hUa : U.conjBy a⁻¹ ≤ c.V := by
    have hh := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hUL
    change U.conjBy a⁻¹ ≤ (c.V.conjBy a).conjBy a⁻¹ at hh
    simpa only [conjBy_inv] using hh
  have hm : U.conjBy a⁻¹ ∈ c.kernelLines := c.pointsOn_base ▸
    ⟨c.point_conjugate_mem hU a⁻¹, hUa⟩
  obtain ⟨n, hn, he⟩ := (c.mem_kernelLines_iff _).mp hm
  refine ⟨a * n, ?_, ?_⟩
  · calc
      U = (U.conjBy a⁻¹).conjBy a := (conjBy_inv' _ _).symm
      _ = (c.W.conjBy n).conjBy a := congrArg (fun R : Subgroup G => R.conjBy a) he
      _ = c.W.conjBy (a * n) := conjBy_conjBy _ _ _
  · rw [conjBy_mul]
    exact congrArg (fun R : Subgroup G => R.conjBy a)
      (mem_normalizer_iff_map_conj_eq.mp hn).symm

theorem linesThrough_base : c.linesThrough c.W =
    {L | ∃ g ∈ normalizer (c.W : Set G), L = c.V.conjBy g} := by
  ext L
  constructor
  · rintro ⟨hL, hWL⟩
    obtain ⟨g, hgW, hgL⟩ := c.incident_pair_conjugate c.point_mem hL hWL
    exact ⟨g, mem_normalizer_iff_map_conj_eq.mpr hgW.symm, hgL⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, ?_⟩
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) c.line_le_kernel
    have he : c.W.conjBy g = c.W := mem_normalizer_iff_map_conj_eq.mp hg
    change c.W.conjBy g ≤ c.V.conjBy g at hh
    rwa [he] at hh

omit [Finite G] in
theorem point_normalizer_card : Nat.card (normalizer (c.W : Set G)) = 11664 := by
  rw [c.complement_product, card_sup_eq_mul_of_normalizes_of_disjoint c.D c.K
    (c.complement_le.trans inf_le_right |>.trans (CubicLine.normalizer_normalizes_oddKernel c.W))
    c.complement_disjoint, c.odd_card, c.complement_card]

theorem linesThrough_base_card : Nat.card (c.linesThrough c.W) = 4 := by
  classical
  let N := normalizer (c.W : Set G)
  let : MulAction G (Subgroup G) := MulAction.compHom (Subgroup G) MulAut.conj
  have he : c.linesThrough c.W = MulAction.orbit N c.V := by
    rw [c.linesThrough_base]
    ext L
    exact ⟨fun ⟨g, hg, he⟩ => ⟨⟨g, hg⟩, he.symm⟩,
      fun ⟨g, hg⟩ => ⟨g, g.property, hg.symm⟩⟩
  have hs : MulAction.stabilizer N c.V = (normalizer (c.V : Set G)).subgroupOf N := by
    ext g
    exact mem_normalizer_iff_map_conj_eq.symm
  have hNN : normalizer (c.sylow : Set G) ≤ N := c.common_normalizer.le.trans inf_le_right
  have hc : Nat.card (MulAction.stabilizer N c.V) = 2916 := by
    rw [hs]
    have hh : (normalizer (c.V : Set G)).subgroupOf N =
        (normalizer (c.sylow : Set G)).subgroupOf N := by
      rw [c.common_normalizer]
      ext x
      change (x : G) ∈ normalizer (c.V : Set G) ↔
        (x : G) ∈ normalizer (c.V : Set G) ∧ (x : G) ∈ N
      exact ⟨fun hx => ⟨hx, x.property⟩, And.left⟩
    rw [hh, Nat.card_congr (subgroupOfEquivOfLe hNN).toEquiv]
    exact c.normalizer_card
  have hh := (MulAction.stabilizer N c.V).index_mul_card
  rw [hc, c.point_normalizer_card] at hh
  rw [he, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer N c.V)]
  change (MulAction.stabilizer N c.V).index = 4
  omega

def pointsOnConjugateEquiv (L : Subgroup G) (g : G) :
    c.pointsOn L ≃ c.pointsOn (L.conjBy g) where
  toFun U := ⟨U.val.conjBy g, c.point_conjugate_mem U.property.1 g, map_mono U.property.2⟩
  invFun U := ⟨U.val.conjBy g⁻¹, c.point_conjugate_mem U.property.1 g⁻¹, by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) U.property.2
    change U.val.conjBy g⁻¹ ≤ (L.conjBy g).conjBy g⁻¹ at hh
    simpa only [conjBy_inv] using hh⟩
  left_inv U := Subtype.ext (conjBy_inv _ _)
  right_inv U := Subtype.ext (conjBy_inv' _ _)

def linesThroughConjugateEquiv (U : Subgroup G) (g : G) :
    c.linesThrough U ≃ c.linesThrough (U.conjBy g) where
  toFun L := ⟨L.val.conjBy g, c.line_conjugate_mem L.property.1 g, map_mono L.property.2⟩
  invFun L := ⟨L.val.conjBy g⁻¹, c.line_conjugate_mem L.property.1 g⁻¹, by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) L.property.2
    change (U.conjBy g).conjBy g⁻¹ ≤ L.val.conjBy g⁻¹ at hh
    simpa only [conjBy_inv] using hh⟩
  left_inv L := Subtype.ext (conjBy_inv _ _)
  right_inv L := Subtype.ext (conjBy_inv' _ _)

/-- Asc94 45.10(4): every original line has ten original points. -/
theorem pointsOn_card {L : Subgroup G} (hL : L ∈ c.lines) : Nat.card (c.pointsOn L) = 10 := by
  obtain ⟨g, rfl⟩ := hL
  rw [← Nat.card_congr (c.pointsOnConjugateEquiv c.V g), c.pointsOn_base]
  exact c.kernelLines_card

/-- Asc94 45.10(4): every original point is on four original lines. -/
theorem linesThrough_card {U : Subgroup G} (hU : U ∈ c.points) :
    Nat.card (c.linesThrough U) = 4 := by
  obtain ⟨g, rfl⟩ := hU
  rw [← Nat.card_congr (c.linesThroughConjugateEquiv c.W g)]
  exact c.linesThrough_base_card

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
