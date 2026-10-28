module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.NormIdeal
public import Theory.Representation.FactorDegreeFiltration

/-!
# The literal eleven-coset quotient for a nonzero M₁₁ norm

The geometric sum of the marked element of order eleven maps into its fixed
space. A nonzero image vector extends by orbit transport to an equivariant
map from functions on the actual left cosets. Irreducibility makes this map
surjective. The coset module has dimension 720. No normality of the cyclic
subgroup, semisimplicity of restriction, or degree bound is assumed.

This supplies the nonzero-norm branch of the binary M₁₁ degree-window
argument. Its finite-module filtration remains a separate obligation.
Source context: James, *The modular characters of the Mathieu groups*,
J. Algebra 27 (1973), 57–111. The norm uses the existing native AB marking.
-/

@[expose] public section
open scoped BigOperators MonoidAlgebra
open Sporadic.Mathieu
open Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
open Representation.BinaryOffender
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees

abbrev ElevenCoset := M11 ⧸ Subgroup.zpowers m11Sylow11Generator
noncomputable instance elevenCosetFintype : Fintype ElevenCoset := Fintype.ofFinite _
noncomputable def cosetRepresentation :
    Representation (ZMod 2) M11 (ElevenCoset → ZMod 2) :=
  (BinaryPermutation.representation ElevenCoset).comp (MulAction.toPermHom M11 ElevenCoset)

theorem card_elevenCoset : Fintype.card ElevenCoset = 720 := by
  have h := (Subgroup.zpowers m11Sylow11Generator).card_mul_index
  rw [Nat.card_zpowers, m11Sylow11Generator_order, m11_order] at h
  change 11 * Nat.card ElevenCoset = 7920 at h
  rw [Nat.card_eq_fintype_card] at h
  omega

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem elevenNorm_mem_fixedSpace (τ : Representation (ZMod 2) M11 V) (v : V) :
    τ.asAlgebraHom elevenNorm v ∈ fixedSpace τ (Subgroup.zpowers m11Sylow11Generator) := by
  have hp : (τ m11Sylow11Generator) ^ 11 = 1 := by
    have hc : m11Sylow11Generator ^ 11 = 1 := by
      simpa only [m11Sylow11Generator_order] using pow_orderOf_eq_one m11Sylow11Generator
    rw [← map_pow, hc, map_one]
  have h := mul_geom_sum (τ m11Sylow11Generator) 11
  rw [hp, sub_self, sub_mul, one_mul, sub_eq_zero] at h
  have hn : τ.asAlgebraHom elevenNorm =
      ∑ i ∈ Finset.range 11, (τ m11Sylow11Generator) ^ i := by
    simp [elevenNorm, map_pow]
  rw [mem_fixedSpace_zpowers_iff, hn]
  exact LinearMap.congr_fun h v

theorem exists_coset_map_of_fixed
    (τ : Representation (ZMod 2) M11 V) [τ.IsIrreducible]
    (v : V) (hv : v ∈ fixedSpace τ (Subgroup.zpowers m11Sylow11Generator))
    (hv0 : v ≠ 0) :
    ∃ f : cosetRepresentation.IntertwiningMap τ, Function.Surjective f := by
  classical
  let value (q : ElevenCoset) : V := τ q.out v
  have hvalue (g : M11) : value (QuotientGroup.mk g) = τ g v := by
    obtain ⟨p, hp⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.zpowers m11Sylow11Generator) g
    change τ (QuotientGroup.mk g : ElevenCoset).out v = _
    rw [hp, map_mul, Module.End.mul_apply]
    exact congrArg (τ g) (hv p)
  have hcov (g : M11) (q : ElevenCoset) : value (g • q) = τ g (value q) := by
    induction q using Quotient.inductionOn with
    | h a =>
      change value (QuotientGroup.mk (g * a)) = _
      rw [hvalue, hvalue, map_mul, Module.End.mul_apply]
  let f : cosetRepresentation.IntertwiningMap τ := {
    toLinearMap := {
      toFun a := ∑ q : ElevenCoset, a q • value q
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      change (∑ q : ElevenCoset, a (g⁻¹ • q) • value q) =
        τ g (∑ q : ElevenCoset, a q • value q)
      rw [map_sum]
      simp only [map_smul, ← hcov]
      exact (Equiv.sum_comp (MulAction.toPerm g)
        (fun q => a (g⁻¹ • q) • value q)).symm.trans (by simp) }
  have hf : f (Pi.single (QuotientGroup.mk (1 : M11)) 1) = v := by
    change (∑ q : ElevenCoset,
      (Pi.single (QuotientGroup.mk (1 : M11)) (1 : ZMod 2) : ElevenCoset → ZMod 2) q •
        value q) = v
    simp [hvalue]
  refine ⟨f, (IsIrreducible.surjective_or_eq_zero f).resolve_right ?_⟩
  intro hz
  exact hv0 (hf.symm.trans
    (congrArg (fun k : cosetRepresentation.IntertwiningMap τ =>
      k (Pi.single (QuotientGroup.mk (1 : M11)) 1)) hz))

theorem exists_coset_map_of_elevenNorm_ne_zero
    (τ : Representation (ZMod 2) M11 V) [τ.IsIrreducible]
    (hn : τ.asAlgebraHom elevenNorm ≠ 0) :
    ∃ f : cosetRepresentation.IntertwiningMap τ, Function.Surjective f := by
  have hn' : ∃ v, τ.asAlgebraHom elevenNorm v ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (LinearMap.ext h)
  obtain ⟨v, hv⟩ := hn'
  exact exists_coset_map_of_fixed τ _ (elevenNorm_mem_fixedSpace τ v) hv

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees
