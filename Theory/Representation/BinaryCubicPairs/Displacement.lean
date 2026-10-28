module

public import Theory.Representation.BinaryCubicPairs.Cocycle
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Pi
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The ambient displacement bound of a checked involution word

For a cubic actor every displacement satisfies the three-term cocycle
identity. In the distinguished binary plane this places it in the first two
coordinates. For the other actor it is itself a displacement of a vector
inside the supporting space. The square-one relation for the checked word
then supplies exactly the final premise of its certificate.

Consequently every ambient cocycle takes this involution into one fixed
space of dimension at most two. This is the step that rules out the
nonsemisimple four-dimensional PSL₃(2) pair as well as pairs whose involution
already has rank two on the supporting space. Source application:
Aschbacher--Smith E.6.24, printed p.255.
-/

public section
namespace BinaryCubicPairs
open Packed

private theorem low_of_cubic_sum (x : BitVec 4)
    (h : x ^^^ mv cubic x ^^^ mv (mm cubic cubic) x = 0) :
    ∃ r : Fin 4, BitVec.ofNat 4 r.val = x := by
  have hcheck : ∀ x : BitVec 4,
      x ^^^ mv cubic x ^^^ mv (mm cubic cubic) x = 0 →
      ∃ r : Fin 4, BitVec.ofNat 4 r.val = x := by decide +kernel
  exact hcheck x h

private theorem in_range_of_cubic_sum (m : BitVec 16) (x : BitVec 4)
    (h : x ^^^ mv m x ^^^ mv (mm m m) x = 0) :
    mv m (mv m x) ^^^ mv m x = x := by
  apply toVec_injective
  have hh := congrArg toVec h
  simp only [toVec_xor, toVec_mv, toMat_mm, toVec_zero] at hh ⊢
  rw [Matrix.mulVec_mulVec]
  have hn : -toVec x = toVec x := CharTwo.neg_eq _
  calc
    _ = -(toVec x) := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa only [add_assoc, add_comm, add_left_comm] using hh
    _ = _ := hn

variable {G : Type*} [Group G] (μ : G →* CoordinateMatrix)
  (δ : G → CoordinateVector) (hδ1 : δ 1 = 0)
  (hδ : ∀ g h : G, δ (g * h) = δ g + (μ g).mulVec (δ h))
include hδ1 hδ

private theorem cocycle_cube (g : G) (hg : g ^ 3 = 1) :
    δ g + (μ g).mulVec (δ g) + (μ g * μ g).mulVec (δ g) = 0 := by
  have hh := congrArg δ hg
  simpa only [pow_succ, pow_zero, one_mul, hδ, map_mul, hδ1] using hh

private theorem cocycle_square (g : G) (hg : g ^ 2 = 1) :
    (μ g).mulVec (δ g) = δ g := by
  have hh := congrArg δ hg
  simp only [pow_two, hδ, hδ1] at hh
  have he : (μ g).mulVec (δ g) = -δ g := eq_neg_of_add_eq_zero_right hh
  exact he.trans (CharTwo.neg_eq _)

/-- Every cocycle has its value at the checked involution in the same
space spanned by the two certificate vectors. -/
theorem cocycle_mem_span (hμ : Function.Injective μ)
    (c d : G) (m : BitVec 16)
    (hc : μ c = toMat cubic) (hd : μ d = toMat m)
    (hm : mm (mm m m) m = ident) {k : Certificate} (hk : Valid m k) :
    δ (groupWord c d k.sequence) ∈
      Submodule.span (ZMod 2) {toVec k.first, toVec k.second} := by
  have hc3 : c ^ 3 = 1 := by
    apply hμ
    rw [map_pow, hc, map_one]
    have hh : mm (mm cubic cubic) cubic = ident := by decide +kernel
    rw [← toMat_one]
    simpa only [toMat_mm, ident, pow_succ, pow_zero, one_mul] using congrArg toMat hh
  have hd3 : d ^ 3 = 1 := by
    apply hμ
    rw [map_pow, hd, map_one]
    rw [← toMat_one]
    simpa only [toMat_mm, ident, pow_succ, pow_zero, one_mul] using congrArg toMat hm
  obtain ⟨x, hx⟩ := toVec_surjective (δ c)
  obtain ⟨y, hy⟩ := toVec_surjective (δ d)
  have hcx : x ^^^ mv cubic x ^^^ mv (mm cubic cubic) x = 0 := by
    apply toVec_injective
    simpa only [toVec_xor, toVec_mv, toMat_mm, hx, toVec_zero, hc]
      using cocycle_cube μ δ hδ1 hδ c hc3
  have hdy : y ^^^ mv m y ^^^ mv (mm m m) y = 0 := by
    apply toVec_injective
    simpa only [toVec_xor, toVec_mv, toMat_mm, hy, toVec_zero, hd]
      using cocycle_cube μ δ hδ1 hδ d hd3
  obtain ⟨r, hr⟩ := low_of_cubic_sum x hcx
  let z := mv m y
  have hz : mv m z ^^^ z = y := in_range_of_cubic_sum m y hdy
  let u := mv k.leftCoefficient (BitVec.ofNat 4 r.val) ^^^ mv k.rightCoefficient y
  have hu : toVec u = δ (groupWord c d k.sequence) := by
    have hh := cocycle_groupWord μ c d m hc hd δ hδ1 hδ k.sequence
    rw [hk.coefficients_eq] at hh
    simpa only [u, toVec_xor, toVec_mv, hr, hx, hy] using hh.symm
  have ht2 : (groupWord c d k.sequence) ^ 2 = 1 := by
    rw [← orderOf_groupWord μ c d m hc hd hμ hk]
    exact pow_orderOf_eq_one _
  have hfix : mv k.actor u = u := by
    apply toVec_injective
    rw [toVec_mv, hu]
    have hh := cocycle_square μ δ hδ1 hδ _ ht2
    rwa [matrix_groupWord μ c d m hc hd, hk.word_eq] at hh
  have hv := hk.displacement r z
  dsimp only at hv
  rw [hz] at hv
  have hp : toVec k.first ∈ Submodule.span (ZMod 2) {toVec k.first, toVec k.second} :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hq : toVec k.second ∈ Submodule.span (ZMod 2) {toVec k.first, toVec k.second} :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rw [← hu]
  dsimp only [u]
  rcases hv hfix with he | he | he | he
  · rw [he, toVec_zero]; exact Submodule.zero_mem _
  · rw [he]; exact hp
  · rw [he]; exact hq
  · rw [he, toVec_xor]; exact Submodule.add_mem _ hp hq

end BinaryCubicPairs
