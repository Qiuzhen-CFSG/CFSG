module

public import CFSG.Quasithin.ChapterG.Section03.Recognition.RootGeometry

/-!
# A fixed-vector obstruction to the requested G.3.1 recognition

A full linear action in dimension at least two has no nonzero common fixed
vector. We prove this directly, then apply it to the actual point stabilizer
in the binary four-space, with `Δ` its orbit on a second basis vector.
Two explicitly constructed roots show that the fixed vector belongs to the
span of the canonical generated-group orbit. Thus `FullAction G Δ` is false.

The companion `FixedVectorObstruction/point_stabilizer.g` checks the remaining
source hypotheses and the failure of the proposed dimension-three enlargement.
In block-matrix notation the stabilizer is `2³ : GL₃(2)`; its two-core is the
`2³` radical, and each root group on the 14-point orbit maps injectively to an
elementary abelian group of order four in the quotient. The roots generate the
whole stabilizer. These GAP calculations are diagnostic, not a Lean certificate
of `Hypotheses G Δ`; that premise has not been asserted as a theorem here.

The failed sentence in the source is the assertion on printed p.338 that the
new root group does not stabilize `C_V(K)` when this space is nonzero. Here
`K` acts as `GL₃(2)` on a complementary hyperplane, but both `K` and the new
root group fix the same line. The genuine source inputs require clarification
before the unconditional recognition theorem can be supplied.

Source: Aschbacher--Smith, G.3.1, printed pp.337--338 (PDF pp.348--349).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section03
open BinaryLinear BinaryTransvectionGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem linear_transitive [FiniteDimensional (ZMod 2) V]
    {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) : ∃ e : GL V, e v = w := by
  let d := (LinearEquiv.coord (ZMod 2) V v hv).trans
    (LinearEquiv.coord (ZMod 2) V w hw).symm
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq d
  refine ⟨e, ?_⟩
  have hh := he ⟨v, Submodule.mem_span_singleton_self v⟩
  have hd : d ⟨v, Submodule.mem_span_singleton_self v⟩ =
      ⟨w, Submodule.mem_span_singleton_self w⟩ := by
    apply (LinearEquiv.coord (ZMod 2) V w hw).injective
    simp [d, LinearEquiv.coord_self]
  rw [hd] at hh
  exact hh.symm

/-- A full action in dimension at least two has no nonzero common fixed vector. -/
theorem FullAction.eq_zero_of_fixed {G : Subgroup (GL V)} [Finite G]
    {Δ : Set V} (hfull : FullAction G Δ) (i : OrbitBlock G Δ)
    {v : V} (hv : v ∈ blockSpace G Δ i)
    (hfix : ∀ g ∈ blockGroup G Δ i, g v = v) : v = 0 := by
  let W := blockSpace G Δ i
  let v' : W := ⟨v, hv⟩
  by_contra hv0
  have hv' : v' ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hline : centerLine v' ≠ ⊤ := by
    intro he
    have hd : Module.finrank (ZMod 2) (centerLine v') = 1 := finrank_span_singleton hv'
    rw [he, finrank_top] at hd
    have hd' := hfull.dimension_ge_two i
    change 2 ≤ Module.finrank (ZMod 2) W at hd'
    omega
  obtain ⟨w, _, hw⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hline)
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (Submodule.zero_mem _)
  obtain ⟨e, he⟩ := linear_transitive hv' hw0
  obtain ⟨g, hg⟩ := hfull.surjective i e
  apply hw
  have hgv : e v' = v' := by
    rw [← hg]
    exact Subtype.ext (hfix g.val g.property)
  rw [← he, hgv]
  exact Submodule.mem_span_singleton_self v'

/-- A nonzero fixed vector lying in a block span obstructs the requested conclusion. -/
theorem not_fullAction_of_fixed_vector {G : Subgroup (GL V)} [Finite G]
    {Δ : Set V} (i : OrbitBlock G Δ) {v : V}
    (hv : v ∈ blockSpace G Δ i) (hv0 : v ≠ 0)
    (hfix : ∀ g ∈ G, g v = v) : ¬ FullAction G Δ := by
  intro hfull
  exact hv0 (hfull.eq_zero_of_fixed i hv (fun g hg => hfix g (generated_le G i.val hg)))

namespace PointStabilizerObstruction

abbrev Space := Fin 4 → ZMod 2

def c : Space := Pi.single 0 1
def x : Space := Pi.single 1 1
def y : Space := Pi.single 2 1

def G : Subgroup (GL Space) := pointwiseFixer (centerLine c)
def Δ : Set Space := MulAction.orbit G x

def block : OrbitBlock G Δ :=
  ⟨MulAction.orbit (generated G Δ) x, x, MulAction.mem_orbit_self x, rfl⟩

private theorem mem_G {g : GL Space} (hg : g c = c) : g ∈ G := by
  intro v hv
  rcases (mem_centerLine_iff c v).mp hv with rfl | rfl
  · exact g.map_zero
  · exact hg

private def φ₁ : Space →ₗ[ZMod 2] ZMod 2 := LinearMap.proj 1
private def φ₂ : Space →ₗ[ZMod 2] ZMod 2 := LinearMap.proj 2

private def a : GL Space := transvection x φ₂ (by simp [x, φ₂])
private def b : GL Space := transvection y φ₁ (by simp [y, φ₁])
private def d : GL Space := transvection c φ₂ (by simp [c, φ₂])
private def b' : GL Space := transvection (y + c) φ₁ (by simp [y, c, φ₁])

private theorem ac : a c = c := by simp [a, transvection, φ₂, c]
private theorem bc : b c = c := by simp [b, transvection, φ₁, c]
private theorem dc : d c = c := by simp [d, transvection, φ₂, c]
private theorem b'c : b' c = c := by simp [b', transvection, φ₁, c]

private theorem abx : (a * b) x = y := by
  ext j
  fin_cases j <;> decide

private theorem dy : d y = y + c := by simp [d, transvection, φ₂, y]

private theorem bb'x : (b * b') x = x + c := by
  ext j
  fin_cases j <;> decide

private theorem y_mem : y ∈ Δ :=
  MulAction.mem_orbit_iff.mpr ⟨⟨a * b, G.mul_mem (mem_G ac) (mem_G bc)⟩, abx⟩

private theorem yc_mem : y + c ∈ Δ := by
  refine MulAction.mem_orbit_iff.mpr
    ⟨⟨d * (a * b), G.mul_mem (mem_G dc) (G.mul_mem (mem_G ac) (mem_G bc))⟩, ?_⟩
  change d ((a * b) x) = y + c
  rw [abx, dy]

private theorem b_root : b ∈ rootGroup G y :=
  ⟨mem_G bc, transvection_mem (Submodule.mem_span_singleton_self y)
    (Submodule.span_le.mpr (by simp [φ₁, y]))⟩

private theorem b'_root : b' ∈ rootGroup G (y + c) :=
  ⟨mem_G b'c, transvection_mem (Submodule.mem_span_singleton_self (y + c))
    (Submodule.span_le.mpr (by simp [φ₁, y, c]))⟩

/-- The chosen orbit consists of nonzero vectors, as required in G.3.1. -/
theorem centers_nonzero : ∀ v ∈ Δ, v ≠ 0 := by
  intro v hv hz
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hv
  have hx0 : x = 0 := g.val.map_eq_zero_iff.mp hz
  have hh := congrFun hx0 1
  norm_num [x] at hh

/-- The fixed vector lies in the span of the canonical generated-group orbit. -/
theorem fixed_vector_mem_block : c ∈ blockSpace G Δ block := by
  have hx : x ∈ block.val := MulAction.mem_orbit_self x
  have hxc : x + c ∈ block.val := by
    refine MulAction.mem_orbit_iff.mpr ⟨⟨b * b', (generated G Δ).mul_mem
      (rootGroup_le_generated G y_mem b_root)
      (rootGroup_le_generated G yc_mem b'_root)⟩, bb'x⟩
  have hs := (blockSpace G Δ block).sub_mem
    (Submodule.subset_span hxc) (Submodule.subset_span hx)
  simpa only [add_sub_cancel_left] using hs

/-- The requested full-action conclusion fails for this actual point stabilizer. -/
theorem not_fullAction : ¬ FullAction G Δ := by
  apply not_fullAction_of_fixed_vector block fixed_vector_mem_block
  · intro hz
    have hh := congrFun hz 0
    norm_num [c] at hh
  · intro g hg
    exact hg c (Submodule.mem_span_singleton_self c)

end PointStabilizerObstruction

end CFSG.Quasithin.ChapterG.Section03
