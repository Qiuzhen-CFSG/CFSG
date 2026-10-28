module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.SplitModels.Coordinates
public import Mathlib.GroupTheory.IndexNormal

/-!
# An extending constituent excludes a split irreducible module

Let an index-two restriction split into two exchanged nonzero constituents.
If the left constituent extends to the full group, transfer its projection
across the two cosets. The transferred map is equivariant and restricts to
the given equivalence on the left constituent. Irreducibility would make
this nonzero map injective, contradicting the strict dimension inequality.

This supplies the extension argument for the orthogonal constituent in
Aschbacher–Smith B.4.2(10), used in 13.8.25, printed pp.86 and 959–960.
It works over the original field and needs no algebraic-closure or Schur-field
hypothesis.
-/

@[expose] public section

open Representation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction
namespace RestrictionSplit
variable {F H U : Type*} [Field F] [Group H] [AddCommGroup U] [Module F U]
  {ρ : Representation F H U} {K : Subgroup H} (d : RestrictionSplit ρ K)

/-- A constituent of an irreducible split restriction cannot extend to the
whole index-two overgroup. -/
theorem not_extends [FiniteDimensional F U] (hindex : K.index = 2)
    (hi : IsIrreducible ρ)
    {E : Type*} [AddCommGroup E] [Module F E]
    (τ : Representation F H E) (e : d.left.toSubmodule ≃ₗ[F] E)
    (he : ∀ k : K, ∀ v, e (d.left.toRepresentation k v) = τ k (e v)) : False := by
  classical
  let : K.Normal := K.normal_of_index_eq_two hindex
  let : IsIrreducible ρ := hi
  let : FiniteDimensional F E := e.finiteDimensional
  let f : U →ₗ[F] E := e.toLinearMap.comp d.leftProjection
  have hf (k : K) (v : U) : f (ρ k v) = τ k (f v) := by
    exact (congrArg e (d.leftProjection_intertwines k v)).trans (he k _)
  let t := d.swapper
  let T : U →ₗ[F] E := f + (τ t⁻¹).comp (f.comp (ρ t))
  have hT (v : U) : T v = f v + τ t⁻¹ (f (ρ t v)) := rfl
  have hTk (k : K) (v : U) : T (ρ k v) = τ k (T v) := by
    let k' : K := ⟨t * k * t⁻¹, (inferInstance : K.Normal).conj_mem _ k.property t⟩
    have hh : f (ρ t (ρ k v)) = τ k' (f (ρ t v)) := by
      have hh := hf k' (ρ t v)
      simpa only [k', ← Module.End.mul_apply, ← map_mul, mul_assoc,
        inv_mul_cancel, mul_one] using hh
    rw [hT, hT, hf, hh, map_add]
    congr 1
    simp only [k', ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  have hTt (v : U) : T (ρ t v) = τ t (T v) := by
    let t2 : K := ⟨t * t, K.mul_self_mem_of_index_two hindex t⟩
    have hh : f (ρ t (ρ t v)) = τ (t * t) (f v) := by
      simpa only [t2, map_mul, Module.End.mul_apply] using hf t2 v
    rw [hT, hT, hh, map_add]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left,
      mul_inv_cancel, map_one, Module.End.one_apply]
    exact add_comm _ _
  let Φ : ρ.IntertwiningMap τ := ⟨T, fun g => by
    ext v
    by_cases hg : g ∈ K
    · exact hTk ⟨g, hg⟩ v
    · have hk : t⁻¹ * g ∈ K := (K.mul_mem_iff_of_index_two hindex).mpr
        (iff_of_false (by simpa only [Subgroup.inv_mem_iff] using d.outside) hg)
      have hg' : g = t * (t⁻¹ * g) := by group
      change T (ρ g v) = τ g (T v)
      rw [hg', map_mul, Module.End.mul_apply, hTt, hTk ⟨_, hk⟩,
        map_mul, Module.End.mul_apply]
      simp [← Module.End.mul_apply, ← map_mul]⟩
  have hne : Φ ≠ 0 := by
    intro hz
    have hiL := (Subrepresentation.irreducible_iff_isAtom d.left).mpr d.left_atom
    let := hiL
    let := Subrepresentation.irreducible_module_nontrivial d.left.toRepresentation
    obtain ⟨v, hv⟩ := exists_ne (0 : d.left.toSubmodule)
    have hh : T (v : U) = 0 := congrArg (fun a : ρ.IntertwiningMap τ => a (v : U)) hz
    have hp : d.leftProjection (ρ t (v : U)) = 0 :=
      Submodule.projectionOnto_apply_of_mem_right d.complementary_submodules
        (d.apply_swapper_mem_right v)
    have hh' : e v = 0 := by simpa [hT, f, hp] using hh
    exact hv (e.injective (hh'.trans e.map_zero.symm))
  have hinj := (IsIrreducible.injective_or_eq_zero Φ).resolve_right hne
  have hdim := LinearMap.finrank_le_finrank_of_injective (f := Φ.toLinearMap) hinj
  have hedim := e.finrank_eq
  have hlt := d.finrank_left_lt
  omega
end RestrictionSplit
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction
