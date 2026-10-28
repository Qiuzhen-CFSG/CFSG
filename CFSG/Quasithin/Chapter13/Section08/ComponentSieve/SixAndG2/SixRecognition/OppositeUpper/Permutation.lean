module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.OppositeUpper.Seed
public import Theory.Representation.SixLetterRadicalDisplacement.PermutationQuotients.QuadraticKernels

/-!
# Reindexing the original upper quotient by synthemes

A marking of the original parabolic induces an equivariant equivalence of
its actual left cosets with the fifteen synthemes. Reindexing binary functions
therefore gives the permutation surjection on the displayed upper carrier.
The existing invariant-kernel calculation excludes quadratic action of D0
on every noncentral quotient, without first selecting an irreducible quotient.

Source: Aschbacher–Smith 13.8.4(5–6), used in 13.8.26 and 13.8.34.
The reindexing proof follows the more specialized source adapter in
`A6Endgame.ActionAnalysis34.MarkedQuotient`.
-/

@[expose] public section

open Subgroup Representation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.OppositeUpper
open Representation.SixLetterRadicalDisplacement.PermutationQuotients

private def cosets {J : Type*} [Group J] (e : J ≃* S)
    (P : Subgroup J) (hm : P.map e.toMonoidHom = H2) : J ⧸ P ≃ S ⧸ H2 :=
  Quotient.congr e.toEquiv (by
    intro a b
    simp only [QuotientGroup.leftRel_apply]
    change a⁻¹ * b ∈ P ↔ (e a)⁻¹ * e b ∈ H2
    simp only [← hm, ← map_inv, ← map_mul, mem_map_equiv, e.symm_apply_apply])

private theorem cosets_equivariant {J : Type*} [Group J] (e : J ≃* S)
    (P : Subgroup J) (hm : P.map e.toMonoidHom = H2) (a : J) (x : J ⧸ P) :
    cosets e P hm (a • x) = e a • cosets e P hm x := by
  induction x using Quotient.inductionOn with | h b =>
    change QuotientGroup.mk (e (a * b)) = QuotientGroup.mk (e a * e b)
    rw [map_mul]

private def reindex {Ω Ψ : Type*} (c : Ω ≃ Ψ) :
    (Ψ → ZMod 2) ≃ₗ[ZMod 2] (Ω → ZMod 2) where
  toFun v x := v (c x)
  invFun v x := v (c.symm x)
  left_inv v := by ext x; simp
  right_inv v := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {J F : Type*} [Group J] [AddCommGroup F] [Module (ZMod 2) F]

/-- The surjection is onto the original upper carrier, with the actual actor
equivalence used to mark its parabolic. -/
theorem IsParabolicCyclic.syntheme_surjection
    {τ : Representation (ZMod 2) J F} {P : Subgroup J}
    [Fintype (J ⧸ P)] (h : IsParabolicCyclic τ P)
    (e : J ≃* S) (hm : P.map e.toMonoidHom = H2) :
    ∃ f : (Fin 15 → ZMod 2) →ₗ[ZMod 2] F, Function.Surjective f ∧
      ∀ a v, f (rho (e a) v) = τ a (f v) := by
  obtain ⟨f, hf⟩ := h.permutation_surjection
  let c := (cosets e P hm).trans cosetEquiv
  have hc (a : J) (x : J ⧸ P) : c (a • x) = synthemeHom (e a) (c x) := by
    change cosetEquiv (cosets e P hm (a • x)) = _
    rw [cosets_equivariant, cosetEquiv_equivariant]
    rfl
  refine ⟨f.toLinearMap.comp (reindex c).toLinearMap,
    hf.comp (reindex c).surjective, ?_⟩
  intro a v
  have hh : reindex c (rho (e a) v) =
      BinaryPermutation.representation (J ⧸ P)
        (MulAction.toPermHom J (J ⧸ P) a) (reindex c v) := by
    ext x
    change v ((synthemeHom (e a)).symm (c x)) = v (c (a⁻¹ • x))
    have hx := hc a⁻¹ x
    rw [map_inv, map_inv] at hx
    exact congrArg v hx.symm
  change f (reindex c (rho (e a) v)) = _
  rw [hh]
  exact Representation.IntertwiningMap.isIntertwining _ _ f a (reindex c v)

open Representation.BinaryOffender

/-- Quadraticity is transported by the actual conjugator on the original
upper representation; its carrier is not changed. -/
theorem quadratic_conjugate (τ : Representation (ZMod 2) J F)
    (A : Subgroup J) (h : J) (hq : IsQuadratic τ A) :
    IsQuadratic τ (A.map (MulAut.conj h).toMonoidHom) := by
  have hinv (v : F) : τ h⁻¹ (τ h v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  obtain ⟨w, rfl⟩ := (τ.apply_bijective h).surjective v
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
    Module.End.mul_apply, map_sub, hinv] using congrArg (τ h) (hq a ha b hb w)

/-- A noncentral actual upper quotient excludes any actor containing the
even transvection cube in the same syntheme marking. -/
theorem not_quadratic_of_parabolic_cyclic
    (τ : Representation (ZMod 2) J F) (P A : Subgroup J)
    [Fintype (J ⧸ P)] (e : J ≃* S)
    (hm : P.map e.toMonoidHom = H2) (h : IsParabolicCyclic τ P)
    (hnc : ∃ a v, τ a v ≠ v) (hD : D0 ≤ A.map e.toMonoidHom) :
    ¬ IsQuadratic τ A := by
  obtain ⟨f, hf, he⟩ := h.syntheme_surjection e hm
  intro hq
  apply not_quadratic_D0 (τ.comp e.symm.toMonoidHom) f hf
    (fun g v => by simpa using he (e.symm g) v)
    (by obtain ⟨g, v, hv⟩ := hnc; exact ⟨e g, v, by simpa using hv⟩)
  intro a ha b hb v
  exact hq _ (mem_map_equiv.mp (hD ha)) _ (mem_map_equiv.mp (hD hb)) v

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.OppositeUpper
end
