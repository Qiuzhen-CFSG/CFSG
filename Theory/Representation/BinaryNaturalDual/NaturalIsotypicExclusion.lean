module
public import Theory.Representation.BinaryNaturalDual.Action
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic

/-!
# Natural-isotypic exclusion for the binary natural-plus-dual action

Two transvections with the same displacement force every equivariant map
from the natural module to its dual to vanish in dimension at least three.
Applying this to each pair of summands makes every invariant bilinear form
on repeated natural modules zero. The evaluation pairing on the doubled
module is nonzero, so it cannot admit such a marking, even after an
arbitrary automorphism of the actor group.

Source: the natural-isotypic exclusion in Aschbacher--Smith, 12.1.9(1),
printed p.793, applying the alternatives of 4.4.3(i.a), printed p.619.
-/

public noncomputable section
open BinaryLinear.OuterCyclic
open scoped BigOperators
namespace BinaryNaturalDual

/-- Two different transvections with the same displacement separate the natural and dual actions. -/
theorem natural_to_dual_eq_zero {n : ℕ} (hn : 3 ≤ n)
    (e : BinaryLinear.OuterCyclic.Space n →ₗ[ZMod 2]
      Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))
    (he : ∀ (g : LinearGroup n) v, e (g v) = g.symm.dualMap (e v)) : e = 0 := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let k : Fin n := ⟨2, by omega⟩
  let b : BinaryLinear.OuterCyclic.Space n := Pi.single i 1
  let v : BinaryLinear.OuterCyclic.Space n := Pi.single j 1 + Pi.single k 1
  let qj : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n) := LinearMap.proj j
  let qk : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n) := LinearMap.proj k
  have hj : qj b = 0 := by simp [qj, b, i, j]
  have hk : qk b = 0 := by simp [qk, b, i, k]
  let tj := BinaryLinear.transvection b qj hj
  let tk := BinaryLinear.transvection b qk hk
  have hvj : tj v = v + b := by
    change v + qj v • b = v + b
    simp [qj, v, j, k]
  have hvk : tk v = v + b := by
    change v + qk v • b = v + b
    simp [qk, v, j, k]
  have hr (w) : e b w = qj w * e v b := by
    have hh := LinearMap.congr_fun (he tj v) w
    rw [hvj, map_add] at hh
    change e v w + e b w = e v (w + qj w • b) at hh
    simpa only [map_add, map_smul, smul_eq_mul, add_right_inj] using hh
  have hs (w) : e b w = qk w * e v b := by
    have hh := LinearMap.congr_fun (he tk v) w
    rw [hvk, map_add] at hh
    change e v w + e b w = e v (w + qk w • b) at hh
    simpa only [map_add, map_smul, smul_eq_mul, add_right_inj] using hh
  have hz : e v b = 0 := by
    have hh := (hr (Pi.single j 1)).symm.trans (hs (Pi.single j 1))
    simpa [qj, qk, j, k] using hh
  have hb : e b = 0 := by ext w; simp [hr, hz]
  have hb0 : b ≠ 0 := by
    intro hh
    have hh' := congrFun hh i
    simp [b] at hh'
  apply LinearMap.ext
  intro w
  apply LinearMap.ext
  intro z
  by_cases hw : w = 0
  · simp [hw]
  obtain ⟨g,hg⟩ := exists_linearEquiv_apply_eq hb0 hw
  rw [← hg, he, hb, map_zero]
  rfl

/-- No bilinear form on repeated binary natural modules is invariant under the full linear group. -/
theorem natural_copies_invariant_bilinear_eq_zero {n : ℕ} (hn : 3 ≤ n)
    {ι : Type*} [Fintype ι]
    (b : LinearMap.BilinForm (ZMod 2) (ι → BinaryLinear.OuterCyclic.Space n))
    (hb : ∀ (g : LinearGroup n) v w,
      b (fun i => g (v i)) (fun i => g (w i)) = b v w) : b = 0 := by
  classical
  have single_action (g : LinearGroup n) (i : ι) (v : BinaryLinear.OuterCyclic.Space n) :
      (fun j => g ((Pi.single i v : ι → BinaryLinear.OuterCyclic.Space n) j)) = Pi.single i (g v) := by
    funext j
    by_cases h : i = j
    · subst j; simp
    · simp [Ne.symm h]
  have hsingle (i j : ι) (v w : BinaryLinear.OuterCyclic.Space n) :
      b (Pi.single i v) (Pi.single j w) = 0 := by
    let e := b.compl₁₂ (LinearMap.single (ZMod 2) _ i) (LinearMap.single (ZMod 2) _ j)
    have he : e = 0 := natural_to_dual_eq_zero hn e (by
      intro g v
      apply LinearMap.ext
      intro w
      have hh := hb g (Pi.single i v) (Pi.single j (g.symm w))
      rw [single_action, single_action, g.apply_symm_apply] at hh
      exact hh)
    exact LinearMap.congr_fun (LinearMap.congr_fun he v) w
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  have hv : v = ∑ i, Pi.single i (v i) := by
    funext i
    simp only [Finset.sum_apply, Pi.single_apply]
    simp
  have hw : w = ∑ i, Pi.single i (w i) := by
    funext i
    simp only [Finset.sum_apply, Pi.single_apply]
    simp
  rw [hv, hw]
  simp only [map_sum, LinearMap.sum_apply, hsingle, Finset.sum_const_zero,
    LinearMap.zero_apply]

/-- An arbitrary actor marking cannot identify the doubled module with repeated natural copies. -/
theorem no_natural_copies_equiv {n : ℕ} (hn : 3 ≤ n)
    {ι : Type*} [Fintype ι]
    (a : MulAut (LinearGroup n))
    (e : CoordinateSpace n ≃ₗ[ZMod 2] (ι → BinaryLinear.OuterCyclic.Space n))
    (he : ∀ (g : LinearGroup n) v,
      e (naturalDualRepresentation g v) = fun i => a g (e v i)) : False := by
  let b := (quadratic (V := BinaryLinear.OuterCyclic.Space n)).polarBilin.compl₁₂
    e.symm.toLinearMap e.symm.toLinearMap
  have htrans (g : LinearGroup n) (v : ι → BinaryLinear.OuterCyclic.Space n) :
      e.symm (fun i => a g (v i)) = naturalDualRepresentation g (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  have hb : b = 0 := natural_copies_invariant_bilinear_eq_zero hn b (by
    intro g v w
    obtain ⟨g,rfl⟩ := a.surjective g
    change quadratic.polarBilin (e.symm (fun i => a g (v i)))
      (e.symm (fun i => a g (w i))) = quadratic.polarBilin (e.symm v) (e.symm w)
    rw [htrans, htrans]
    simp only [naturalDualRepresentation_apply, polar_apply,
      LinearEquiv.dualMap_apply,
      LinearEquiv.symm_apply_apply])
  let i : Fin n := ⟨0,by omega⟩
  let x : BinaryLinear.OuterCyclic.Space n := Pi.single i 1
  let f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n) := LinearMap.proj i
  have hh := LinearMap.congr_fun (LinearMap.congr_fun hb (e (x,0))) (e (0,f))
  change quadratic.polarBilin (e.symm (e (x,0))) (e.symm (e (0,f))) = 0 at hh
  rw [e.symm_apply_apply,e.symm_apply_apply,polar_apply] at hh
  simp [x,f] at hh

end BinaryNaturalDual
