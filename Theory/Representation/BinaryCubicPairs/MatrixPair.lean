module

public import Theory.Representation.BinaryCubicPairs.Ambient
public import Theory.Representation.BinaryCubicPairs.Checks
public import Theory.Representation.BinaryCubicPairs.Ready
public import Theory.Representation.BinaryCubicPairs.Normalization
public import Theory.Representation.BinaryCubicPairs.ChangeCoordinates

/-!
# Arbitrarily marked binary cubic pairs on four-dimensional support

The first actor is put into its canonical two-dimensional moving block by
a checked invertible coordinate change. The full-support predicate supplies
the second actor's certificate. The original embedding, changed by the
inverse matrix, then gives an involution of ambient fixed codimension at
most two. The theorem refers throughout to the original representation.

This is the finite small-module inference for Aschbacher--Smith E.6.24,
printed p.255; it has no fixed-space TI premise.
-/

public section
namespace BinaryCubicPairs
open Packed Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem exists_involution_of_matrix_pair
    (ρ : Representation (ZMod 2) G V)
    (j : CoordinateVector →ₗ[ZMod 2] V) (hj : Function.Injective j)
    (μ : G →* CoordinateMatrix) (hμ : Function.Injective μ)
    (haction : ∀ g x, ρ g (j x) = j ((μ g).mulVec x))
    (hquotient : ∀ g v, ∃ x, ρ g v - v = j x)
    (c d : G) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hcfix : Module.finrank (ZMod 2) (fixedKernel (μ c)) = 2)
    (hdfix : Module.finrank (ZMod 2) (fixedKernel (μ d)) = 2)
    (hfull : ∀ v : CoordinateVector, ∃ x y : CoordinateVector,
      (μ c).mulVec x - x + ((μ d).mulVec y - y) = v)
    (hnc : ¬ Commute c d) :
    ∃ t : G, orderOf t = 2 ∧ fixedCodim ρ (Subgroup.zpowers t) ≤ 2 := by
  let a := pack (μ c)
  have ha : toMat a = μ c := toMat_pack _
  have hcubic : cubicB a = true := by
    have hp : mm (mm a a) a = ident := by
      apply toMat_injective
      simp only [toMat_mm, ha, ident, toMat_one]
      have hp' : (μ c) ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
      simpa only [pow_succ, pow_zero, one_mul] using hp' 
    have hf := fixed_count_four a (by rw [ha]; exact hcfix)
    simp only [cubicB, hp, hf, beq_self_eq_true, Bool.and_self]
  obtain ⟨g₀, h₀, hgh₀, hhg₀, hconj⟩ := exists_normalization a hcubic
  let g := toMat g₀
  let h := toMat h₀
  have hgh : g * h = 1 := by simpa only [toMat_mm, ident, toMat_one] using congrArg toMat hgh₀
  have hhg : h * g = 1 := by simpa only [toMat_mm, ident, toMat_one] using congrArg toMat hhg₀
  let ν := conjugatedHom μ g h hgh hhg
  let j' : CoordinateVector →ₗ[ZMod 2] V := j.comp h.mulVecLin
  have hg_inj : Function.Injective (Matrix.mulVec h) := by
    intro x y he
    have hh := congrArg (Matrix.mulVec g) he
    simpa only [Matrix.mulVec_mulVec, hgh, Matrix.one_mulVec] using hh
  have hj' : Function.Injective j' := hj.comp hg_inj
  have hν : Function.Injective ν := conjugatedHom_injective μ g h hgh hhg hμ
  have hact : ∀ k x, ρ k (j' x) = j' ((ν k).mulVec x) := by
    intro k x
    change ρ k (j (h.mulVec x)) = j (h.mulVec ((g * μ k * h).mulVec x))
    rw [haction]
    apply congrArg j
    have he : h * (g * μ k * h) = μ k * h := by
      rw [← mul_assoc, ← mul_assoc, hhg, one_mul]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, he]
  have hquot : ∀ k v, ∃ x, ρ k v - v = j' x := by
    intro k v
    obtain ⟨x, hx⟩ := hquotient k v
    refine ⟨g.mulVec x, ?_⟩
    change ρ k v - v = j (h.mulVec (g.mulVec x))
    rw [Matrix.mulVec_mulVec, hhg, Matrix.one_mulVec]
    exact hx
  have hcν : ν c = toMat cubic := by
    change g * μ c * h = _
    simpa only [toMat_mm, ha] using congrArg toMat hconj
  let m := pack (ν d)
  have hm : toMat m = ν d := toMat_pack _
  have hp : (toMat m) ^ 3 = 1 := by rw [hm, ← map_pow, hd3, map_one]
  have hf : Module.finrank (ZMod 2) (fixedKernel (toMat m)) = 2 := by
    rw [hm]
    change Module.finrank (ZMod 2) (fixedKernel (g * μ d * h)) = 2
    rw [← (fixedKernelEquiv g h hgh hhg (μ d)).finrank_eq]
    exact hdfix
  have hr := ready_of_matrices m hp hf (by
    simpa only [← hcν, hm] using conjugated_full μ g h hgh hhg c d hfull) (by
      intro he
      apply hnc
      apply hν
      simpa only [map_mul, hcν, ← hm] using he)
  obtain ⟨k, hk⟩ := exists_certificate m hr
  have hmp : mm (mm m m) m = ident := by
    apply toMat_injective
    simpa only [toMat_mm, ident, toMat_one, pow_succ, pow_zero, one_mul] using hp
  exact exists_involution_of_certificate ρ j' hj' ν hν hact hquot c d m hcν hm.symm hmp hk

end BinaryCubicPairs
