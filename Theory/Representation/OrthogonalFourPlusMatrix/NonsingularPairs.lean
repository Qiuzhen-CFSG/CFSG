module
public import Theory.Representation.OrthogonalFourPlusMatrix.SmallActors
public import Theory.LinearAlgebra.AlternatingPlane

/-!
# Nonsingular pairs in large binary tensor subspaces

A binary subspace consisting of singular matrices spans an isotropic field
subspace for the determinant polarization, so its binary dimension is at
most four. If all nonsingular matrices of a binary subspace lie on one field
line, pairing with one of them has kernel inside that line. Its kernel and
image both have binary dimension at most two, giving the same bound.

Thus every binary subspace of dimension at least five contains nonsingular
matrices on two distinct field lines. This is the matrix input for the
pair-centralizer argument in Aschbacher–Smith 9.4.2–3, printed p.736.
-/

public section

open Module Matrix Submodule
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

private theorem rank_restrict (E : Submodule F V) :
    finrank (ZMod 2) (E.restrictScalars (ZMod 2)) = 2 * finrank F E := by
  rw [((Submodule.restrictScalarsEquiv (ZMod 2) F V E).restrictScalars (ZMod 2)).finrank_eq,
    ← Module.finrank_mul_finrank (ZMod 2) F E, finrank_field]

private theorem singular_subspace_rank (U : Submodule (ZMod 2) V)
    (hU : ∀ x ∈ U, x.det = 0) : finrank (ZMod 2) U ≤ 4 := by
  let B := (determinantForm (F := F)).polarBilin
  have hB (x y : V) (hx : x ∈ U) (hy : y ∈ U) : B x y = 0 := by
    simp only [B, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      determinantForm_apply, hU _ hx, hU _ hy, hU _ (U.add_mem hx hy), sub_zero]
  let E := Submodule.span F (U : Set V)
  have hE (x y : V) (hx : x ∈ E) (hy : y ∈ E) : B x y = 0 := by
    have hleft (u : V) (hu : u ∈ U) : E ≤ (B u).ker :=
      Submodule.span_le.mpr (fun v hv => hB u v hu hv)
    have hright : E ≤ (B.flip y).ker := by
      apply Submodule.span_le.mpr
      intro u hu
      change (B.flip y) u = 0
      rw [LinearMap.flip_apply]
      exact hleft u hu hy
    have hh : (B.flip y) x = 0 := hright hx
    simpa only [LinearMap.flip_apply] using hh
  have hnon : B.Nondegenerate := by
    refine ⟨determinant_polar_separating, ?_⟩
    intro y hy
    apply determinant_polar_separating y
    intro x
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact hy x
  have hd := LinearMap.BilinForm.twice_finrank_le_of_isotropic B hnon E (fun x hx y hy => hE x y hx hy)
  have hdimV : finrank F V = 4 := by
    change finrank F (Fin 2 → Fin 2 → F) = 4
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    simp only [Fin.sum_univ_two, Module.finrank_self]
    decide
  rw [hdimV] at hd
  have hUE : U ≤ E.restrictScalars (ZMod 2) := fun x hx => Submodule.subset_span hx
  have hu := Submodule.finrank_mono hUE
  rw [rank_restrict] at hu
  exact hu.trans hd

/-- Every binary subspace of dimension at least five meets two nonsingular field lines. -/
theorem exists_nonsingular_pair_of_finrank_gt_four (U : Submodule (ZMod 2) V)
    (hU : 4 < finrank (ZMod 2) U) :
    ∃ x ∈ U, ∃ y ∈ U, x.det ≠ 0 ∧ y.det ≠ 0 ∧
      y ∉ Submodule.span F ({x} : Set V) := by
  obtain ⟨x,hx,hxn⟩ : ∃ x ∈ U, x.det ≠ 0 := by
    by_contra! hall
    exact (not_lt_of_ge (singular_subspace_rank U hall)) hU
  by_contra! hall
  have hline (y : V) (hy : y ∈ U) (hyn : y.det ≠ 0) :
      y ∈ Submodule.span F ({x} : Set V) := hall x hx y hy hxn hyn
  let E := Submodule.span F ({x} : Set V)
  let B := (determinantForm (F := F)).polarBilin
  let f : U →ₗ[ZMod 2] F := ((B x).restrictScalars (ZMod 2)).comp U.subtype
  have hk (v : f.ker) : ((v : U) : V) ∈ E := by
    by_contra hn
    have hv0 : ((v : U) : V).det = 0 := not_not.mp (fun hv => hn (hline _ v.val.property hv))
    have hxvnot : x + (v : U) ∉ E := by
      intro he
      apply hn
      have hxE : x ∈ E := Submodule.subset_span (by simp)
      simpa only [add_sub_cancel_left] using E.sub_mem he hxE
    have hxv0 : (x + (v : U)).det = 0 :=
      not_not.mp (fun hv => hxvnot (hline _ (U.add_mem hx v.val.property) hv))
    have hp : B x (v : U) = 0 := v.property
    have hh := QuadraticMap.map_add determinantForm x ((v : U) : V)
    simp only [determinantForm_apply, ← QuadraticMap.polarBilin_apply_apply] at hh
    change (x + (v : U)).det = x.det + ((v : U) : V).det + B x (v : U) at hh
    rw [hxv0, hv0, hp, add_zero, add_zero] at hh
    exact hxn hh.symm
  let i : f.ker →ₗ[ZMod 2] E.restrictScalars (ZMod 2) :=
    { toFun v := ⟨((v : U) : V),hk v⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : E.restrictScalars (ZMod 2) => (z : V)) hab
  have hker := LinearMap.finrank_le_finrank_of_injective hi
  have hxn0 : x ≠ 0 := by
    intro he
    exact hxn (by rw [he]; simp)
  have hE : finrank F E = 1 := finrank_span_singleton hxn0
  rw [rank_restrict] at hker
  have hrange : finrank (ZMod 2) f.range ≤ 2 := by
    have h := Submodule.finrank_le f.range
    rwa [finrank_field] at h
  have hf := f.finrank_range_add_finrank_ker
  omega

end ClassicalOrthogonal.FourPlusMatrix.Binary
