module
public import Theory.Representation.BinaryNaturalDual.FirstCohomology
public import Theory.Representation.BinaryNaturalDual.NaturalIsotypicExclusion
public import Theory.Representation.IrreduciblePairBound
public import Theory.Representation.SL2FourNaturalOrbits.BorelDualCore
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryOffender.DualDisplacement
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# Obstructions to containing a doubled natural module

The natural module and its dual are inequivalent simple modules in degree at
least three. Pulling them back along the same surjective actor preserves this
property. The small-pair bound therefore excludes their sum from repetitions
of any module smaller than their combined dimension.

Separately, counting displacement maps bounds the rank of a faithful actor by
the product of its fixed codimensions on a module and its dual. Rank at least
two forces total fixed codimension at least three.

The original residual action and radical in Aschbacher--Smith C.4.8 and
12.1.9 (printed pp.154,793) supply the applications in NormalizerFourModuleExclusion.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryNaturalDual
open BinaryLinear.OuterCyclic

private theorem natural_irreducible {n : ℕ} (hn : 0 < n) :
    IsIrreducible (linearNatural n) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  apply Representation.SL2FourNatural.BorelFactors.irreducible_of_transitive
  intro v w hv hw
  exact exists_linearEquiv_apply_eq hv hw

/-- The original natural and dual simple factors cannot embed into repetitions
of a module smaller than their sum, for any surjective original actor. -/
theorem no_small_repeated_embedding {F Y ι : Type*} [Group F]
    [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
    {n : ℕ} (hn : 3 ≤ n) (p : F →* LinearGroup n) (hp : Function.Surjective p)
    (σ : Representation (ZMod 2) F Y)
    (τ : Representation (ZMod 2) F (ι → Y))
    (hτ : ∀ x v i, τ x v i = σ x (v i))
    (hd : Module.finrank (ZMod 2) Y < 2*n)
    (f : CoordinateSpace n →ₗ[ZMod 2] (ι → Y)) (hf : Function.Injective f)
    (he : ∀ x v, f (naturalDualRepresentation (p x) v) = τ x (f v)) : False := by
  let ρ : Representation (ZMod 2) F (BinaryLinear.OuterCyclic.Space n) := (linearNatural n).comp p
  let η : Representation (ZMod 2) F (Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) := (linearNatural n).dual.comp p
  let : IsIrreducible (linearNatural n) := natural_irreducible (by omega)
  let : IsIrreducible (linearNatural n).dual :=
    Representation.SL2FourNatural.BorelDualCore.dual_irreducible _
  let : IsIrreducible ρ := (irreducible_comp_surjective_iff p hp _).mpr inferInstance
  let : IsIrreducible η := (irreducible_comp_surjective_iff p hp _).mpr inferInstance
  let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  have hz (b : ρ.IntertwiningMap η) : b = 0 := by
    have hb : b.toLinearMap = 0 := natural_to_dual_eq_zero hn b.toLinearMap (by
      intro g v
      obtain ⟨x,rfl⟩ := hp g
      exact LinearMap.congr_fun (b.isIntertwining' x) v)
    exact IntertwiningMap.ext hb
  let j : (η.prod ρ).IntertwiningMap τ := {
    toLinearMap := f.comp (LinearEquiv.prodComm (ZMod 2) _ _).toLinearMap
    isIntertwining' := by
      intro x
      apply LinearMap.ext
      intro v
      change f (p x v.2, (linearNatural n).dual (p x) v.1) = τ x (f (v.2,v.1))
      have hh := he x (v.2,v.1)
      rw [naturalDualRepresentation_apply] at hh
      convert hh using 1
      congr 2 }
  apply no_small_repeated_inequivalent_pair hz (σ := σ) _ τ hτ j
    (hf.comp (LinearEquiv.prodComm (ZMod 2) _ _).injective)
  simpa [BinaryLinear.OuterCyclic.Space,Module.finrank_prod,two_mul] using hd

/-- A subgroup of rank at least two cannot fix a subspace of codimension at
most two in a faithful module together with its dual. -/
theorem three_le_fixedCodim_prod_dual {F Y : Type*} [Group F] [Finite F]
    [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
    (ρ : Representation (ZMod 2) F Y) (hf : Function.Injective ρ)
    (A : Subgroup F) (hr : 2 ≤ rank A) :
    3 ≤ fixedCodim (ρ.prod ρ.dual) A := by
  have hne : A ≠ ⊥ := by
    intro he
    simp [he,rank] at hr
  have ha := fixedCodim_pos_of_faithful ρ hf hne
  have hb := fixedCodim_pos_of_faithful ρ.dual (faithful_dual ρ hf) hne
  have hc := rank_le_fixedCodim_mul_dual ρ hf A
  rw [fixedCodim_prod]
  by_contra h
  have ha1 : fixedCodim ρ A = 1 := by omega
  have hb1 : fixedCodim ρ.dual A = 1 := by omega
  rw [ha1,hb1] at hc
  omega
end BinaryNaturalDual
