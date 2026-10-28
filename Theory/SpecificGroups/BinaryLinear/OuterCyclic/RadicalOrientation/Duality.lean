module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic

/-!
# Inverse transpose exchanges hyperplane and point radicals

The actual matrix action satisfies
`⟨graphLinear g x, g y⟩ = ⟨x, y⟩` for the coordinate dot product.
For a nonzero functional `f`, its coordinate normal vector is
`w i = f (Pi.single i 1)`. The pairing identity shows that inverse transpose
carries the radical of `ker f` into the radical of the line spanned by `w`:
it fixes this line pointwise, and every displacement annihilates `ker f`.
The self-centralizing property of the original radical gives equality.

This proves the hyperplane-to-point step used in radical orientation for
dimensions four and five, without a classification of automorphisms or of
transvection subgroups.

Source: GLS3, Theorem 2.5.12 and §2.7,
`refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115. The source's graph formula
is inverse transpose followed by a fixed inner conjugation. Here we compute
the pure inverse transpose defined in `OuterCyclic.Model`.
-/

@[expose] public section

open Matrix

namespace BinaryLinear.OuterCyclic

/-- Inverse transpose preserves the pairing between the dual and natural actions. -/
theorem graphLinear_dotProduct {n : ℕ} (g : LinearGroup n) (x y : Space n) :
    dotProduct (graphLinear n g x) (g y) = dotProduct x y := by
  obtain ⟨A, rfl⟩ := (slEquivLinear n).surjective g
  rw [graphLinear_slEquivLinear]
  rw [slEquivLinear_apply n A]
  rw [← dotProduct_transpose_mulVec, dotProduct_comm y]
  change dotProduct (slEquivLinear n (Matrix.SpecialLinearGroup.transpose A)
    (slEquivLinear n (Matrix.SpecialLinearGroup.transpose A)⁻¹ x)) y = _
  simp only [map_inv]
  exact congrArg (fun z => dotProduct z y) ((slEquivLinear n
    (Matrix.SpecialLinearGroup.transpose A)).apply_symm_apply x)

private theorem duality_pairing_inv {n : ℕ} (g : LinearGroup n) (x y : Space n) :
    dotProduct (graphLinear n g x) y = dotProduct x (g⁻¹ y) := by
  simpa only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using
    graphLinear_dotProduct g x (g⁻¹ y)

private theorem duality_normal_pairing {n : ℕ}
    (f : Space n →ₗ[ZMod 2] ZMod 2) (x : Space n) :
    dotProduct (fun i => f (Pi.single i 1)) x = f x := by
  conv_rhs => rw [pi_eq_sum_univ' x]
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The annihilator of a hyperplane is its coordinate normal line. -/
private theorem duality_mem_normal_span {n : ℕ}
    (f : Space n →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) (z : Space n)
    (hz : ∀ x ∈ f.ker, dotProduct z x = 0) :
    z ∈ Submodule.span (ZMod 2) {fun i => f (Pi.single i 1)} := by
  have hu : ∃ u, f u ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext h)
  obtain ⟨u, hu⟩ := hu
  have hu1 : f u = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hu
  have hpair (x : Space n) : dotProduct z x = f x * dotProduct z u := by
    have hx : x - f x • u ∈ f.ker := by
      change f (x - f x • u) = 0
      simp only [map_sub, map_smul, hu1, smul_eq_mul, mul_one, sub_self]
    have h := hz (x - f x • u) hx
    simpa only [dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] using h
  apply Submodule.mem_span_singleton.mpr
  refine ⟨dotProduct z u, ?_⟩
  ext i
  have h := hpair (Pi.single i 1)
  simpa only [dotProduct_single, mul_one, Pi.smul_apply, smul_eq_mul, mul_comm] using h.symm

private theorem duality_map_le {n : ℕ} (f : Space n →ₗ[ZMod 2] ZMod 2)
    (hf : f ≠ 0) :
    (hyperplaneRadical n f).map (graphLinear n).toMonoidHom ≤
      pointRadical n (fun i => f (Pi.single i 1)) := by
  rintro t ⟨s, hs, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom]
  have hsi := (hyperplaneRadical n f).inv_mem hs
  refine ⟨?_, ?_⟩
  · have hfix : graphLinear n s (fun i => f (Pi.single i 1)) =
        (fun i => f (Pi.single i 1)) := by
      have he (x : Space n) :
          dotProduct (graphLinear n s (fun i => f (Pi.single i 1))) x =
            dotProduct (fun i => f (Pi.single i 1)) x := by
        rw [duality_pairing_inv, duality_normal_pairing, duality_normal_pairing]
        have h := hsi.2 x
        change f (s⁻¹ x - x) = 0 at h
        exact sub_eq_zero.mp (by simpa only [map_sub] using h)
      funext i
      simpa only [dotProduct_single, mul_one] using he (Pi.single i 1)
    intro v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simpa only [map_smul] using congrArg (a • ·) hfix
  · intro x
    apply duality_mem_normal_span f hf
    intro z hz
    rw [sub_dotProduct, duality_pairing_inv, hsi.1 z hz, sub_self]

/-- Actual inverse transpose sends every hyperplane radical to a point radical. -/
theorem graph_hyperplaneRadical {n : ℕ} (hn : n = 4 ∨ n = 5)
    (f : Space n →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) :
    ∃ w : Space n, w ≠ 0 ∧
      (hyperplaneRadical n f).map (graphLinear n).toMonoidHom = pointRadical n w := by
  let w : Space n := fun i => f (Pi.single i 1)
  have hw : w ≠ 0 := by
    intro hw0
    apply hf
    apply LinearMap.ext
    intro x
    change f x = 0
    rw [← duality_normal_pairing]
    change dotProduct w x = 0
    rw [hw0, zero_dotProduct]
  refine ⟨w, hw, ?_⟩
  have hker0 : f.ker ≠ ⊥ := by
    intro hker
    have hdim := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hker)
    have hdim' : n ≤ 1 := by simpa [Space] using hdim
    omega
  have hker1 : f.ker ≠ ⊤ := mt LinearMap.ker_eq_top.mp hf
  have hle := duality_map_le f hf
  apply le_antisymm hle
  intro t ht
  apply centralizer_map_radical_le f.ker hker0 hker1 (graphLinear n)
  exact Subgroup.mem_centralizer_iff.mpr
    (fun s hs => radical_commute (Submodule.span (ZMod 2) {w}) (hle hs) ht)

end BinaryLinear.OuterCyclic
