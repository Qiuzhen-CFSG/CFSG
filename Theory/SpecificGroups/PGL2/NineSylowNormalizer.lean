module

public import Theory.SpecificGroups.PGL2.NineSylowNormalizer.ActionCoordinates
public import Theory.SpecificGroups.PGL2.NineSylowNormalizer.Coordinates
public import Theory.AtlasPort.ExceptionalIsomorphisms.NineCoordinates

/-!
# The Sylow three-normalizer action in PGL₂(9)

The upper-root group has order nine and index eighty, hence is a Sylow
three-subgroup. Its full normalizer factors as the upper-root group times
the diagonal field units. The units form a cyclic group of order eight;
the literal conjugation formula makes its action faithful and transitive
on nonidentity root elements. Sylow conjugacy transports these coordinates
to every Sylow three-subgroup of the specified nine-element-field model.

This discharges the projective model calculation underlying Aschbacher,
*Sporadic Groups* (1994), 47.3(3), printed p.262. The covering-group lift,
extraspecial structure and weak closure are separate consumer results.
-/

public section

open Subgroup
open scoped Pointwise
noncomputable section
namespace GorensteinWalter.PGL2NineSylowNormalizer
variable {K G : Type*} [Field K] [Finite K] [Group G]

private lemma conjugateAction (e : PGL2 K ≃* G) :
    Nonempty (NormalizerComplementAction
      ((root (K := K)).range.map e.toMonoidHom) (Nat.card K - 1)) := by
  let r : Multiplicative K →* G := e.toMonoidHom.comp root
  let t : Kˣ →* G := e.toMonoidHom.comp torus
  have hc (k : Kˣ) (x : K) : t k * r (Multiplicative.ofAdd x) * (t k)⁻¹ =
      r (Multiplicative.ofAdd ((k : K) * x)) := by
    simpa only [r, t, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_mul, map_inv] using congrArg e (torus_root k x)
  have hf (g : G) (hg : g ∈ normalizer (r.range : Set G)) :
      ∃ x k, r x * t k = g := by
    have hm : e.symm g ∈ normalizer ((root (K := K)).range : Set (PGL2 K)) := by
      apply (mem_map_equiv (f := e)).mp
      rw [map_equiv_normalizer_eq]
      simpa only [r, MonoidHom.range_comp] using hg
    obtain ⟨x, k, h⟩ := normalizer_factor (e.symm g) hm
    refine ⟨x, k, ?_⟩
    simpa only [r, t, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_mul, e.apply_symm_apply] using congrArg e h
  have h := action_of_coordinates r t (e.injective.comp root_injective)
    (e.injective.comp torus_injective) hc hf
  simpa only [r, MonoidHom.range_comp] using h

omit [Finite K] in
private lemma root_card : Nat.card (root (K := K)).range = Nat.card K := by
  calc
    Nat.card (root (K := K)).range = Nat.card (Multiplicative K) :=
      (Nat.card_congr (Equiv.ofInjective root root_injective)).symm
    _ = Nat.card K := Nat.card_congr Multiplicative.toAdd

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Every Sylow three-subgroup of the literal PGL₂(9) model has a cyclic
eight-complement in its full normalizer, acting faithfully and transitively
on its nonidentity elements by the normalizer's conjugation homomorphism. -/
theorem sylowNormalizerAction
    (Q : Sylow 3 (PGL2 Atlas.Comparisons.Exceptional.Nine.F)) :
    Nonempty (NormalizerComplementAction
      (Q : Subgroup (PGL2 Atlas.Comparisons.Exceptional.Nine.F)) 8) := by
  let K := Atlas.Comparisons.Exceptional.Nine.F
  have hK : Nat.card K = 9 := Atlas.Comparisons.Exceptional.Nine.card
  let : Finite (PGL2 K) := Nat.finite_of_card_ne_zero (by
    rw [pgl2_card_formula, hK]
    decide)
  have hp : IsPGroup 3 (root (K := K)).range := IsPGroup.of_card (n := 2) (by
    rw [root_card, hK]
    norm_num)
  have hi : (root (K := K)).range.index = 80 := by
    have h := (root (K := K)).range.index_mul_card
    rw [root_card, pgl2_card_formula, hK] at h
    omega
  let P : Sylow 3 (PGL2 K) := hp.toSylow (by rw [hi]; decide)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PGL2 K) P Q
  have hQ : (root (K := K)).range.map (MulAut.conj g).toMonoidHom =
      (Q : Subgroup (PGL2 K)) := by
    change ((g • P : Sylow 3 (PGL2 K)) : Subgroup (PGL2 K)) = (Q : Subgroup (PGL2 K))
    rw [hg]
  have h := conjugateAction (MulAut.conj g)
  rw [hQ, hK] at h
  exact h
end GorensteinWalter.PGL2NineSylowNormalizer
