module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourChiefMultiplicity
public import Theory.Representation.ScalarMultiplicity.Normalizer
public import Theory.Representation.SL2NaturalOffenders.NormalizerImplementer
public import Theory.GroupTheory.PCoreNormalizerAction

/-!
# Normalizer transport on the original Hermitian chief section

Conjugation by H on R/O₂(R) determines an actual automorphism of the
marked SL₂(4). Its semilinear natural implementer and the original action
on the chief section give an invertible semilinear coefficient operator.
This operator implements conjugation on the same O²(H)V multiplicity
representation. Both operators retain the identical field coefficient.

No faithfulness or kernel assertion for all of H is needed. The companion
Chapter12 application supplies every normalization and coordinate premise.
Source: Aschbacher–Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree
open scoped IsMulCommutative commutatorElement MatrixGroups Matrix
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] {J R A H : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) J W}
set_option backward.isDefEq.respectTransparency false

/-- Every actual H-actor on the homogeneous natural chief section induces
an honest semilinear map on the same multiplicity space. It implements
conjugation on A, with the original quotient and conjugation conventions. -/
theorem natural_coordinates_normalizer
    (hRJ : R ≤ J) (hAJ : A ≤ J) (hHJ : H ≤ J)
    (hHR : H ≤ normalizer (R : Set G)) (hHA : H ≤ normalizer (A : Set G))
    (m : ℕ) (eR : (R ⧸ pCore 2 R) ≃* SL(2,E 1))
    (e : W ≃ₗ[ZMod 2] (Fin m → (Fin 2 → E 1)))
    (he : ∀ r w, e (ρ (inclusion hRJ r) w) =
      fun i => (eR (QuotientGroup.mk' (pCore 2 R) r)).val *ᵥ (e w i))
    (μ : Representation (E 1) A (Fin m → E 1))
    (hμ : ∀ a c z, e (ρ (inclusion hAJ a) (e.symm (fun i => c i • z))) =
      fun i => μ a c i • z) (t : H) :
    ∃ (τ : E 1 ≃+* E 1)
      (s : (Fin 2 → E 1) ≃ₗ[ZMod 2] (Fin 2 → E 1))
      (f : (Fin m → E 1) ≃ₗ[ZMod 2] (Fin m → E 1)),
      (∀ r z, s ((eR (QuotientGroup.mk' (pCore 2 R) r)).val *ᵥ z) =
        (eR (QuotientGroup.mk' (pCore 2 R)
          (R.normalizerMonoidHom (inclusion hHR t) r))).val *ᵥ s z) ∧
      (∀ c z, s (c • z) = τ c • s z) ∧
      (∀ c z, e (ρ (inclusion hHJ t) (e.symm (fun i => c i • z))) =
        fun i => f c i • s z) ∧
      (∀ c z, f (c • z) = τ c • f z) ∧
      (∀ a c, f (μ a c) = μ (A.normalizerMonoidHom (inclusion hHA t) a) (f c)) := by
  let α := MulAut.congr eR (pCoreNormalizerAction 2 R (inclusion hHR t))
  have hα (r : R) : α (eR (QuotientGroup.mk' (pCore 2 R) r)) =
      eR (QuotientGroup.mk' (pCore 2 R) (R.normalizerMonoidHom (inclusion hHR t) r)) := by
    change eR (pCoreNormalizerAction 2 R (inclusion hHR t)
      (eR.symm (eR (QuotientGroup.mk' (pCore 2 R) r)))) = _
    rw [eR.symm_apply_apply,pCoreNormalizerAction_mk]
  obtain ⟨τ,s,hs,hsemi⟩ := SL2NaturalOffenders.exists_semilinear_implementer α
  let u : (Fin m → (Fin 2 → E 1)) ≃ₗ[ZMod 2] (Fin m → (Fin 2 → E 1)) :=
    e.symm.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv
      (ρ.asGroupHom (inclusion hHJ t))).trans e)
  have hu (x) : u x = e (ρ (inclusion hHJ t) (e.symm x)) := rfl
  let σ : Representation (ZMod 2) SL(2,E 1) (Fin 2 → E 1) := {
    toFun g := (specialLinearNatural 2 g).toAddMonoidHom.toZModLinearMap 2
    map_one' := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (map_one (specialLinearNatural 2)) v
    map_mul' g h := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (map_mul (specialLinearNatural 2) g h) v }
  have hconj {P : Subgroup G} (hPJ : P ≤ J)
      (hHP : H ≤ normalizer (P : Set G)) (p : P) (w : W) :
      ρ (inclusion hHJ t) (ρ (inclusion hPJ p) w) =
        ρ (inclusion hPJ (P.normalizerMonoidHom (inclusion hHP t) p))
          (ρ (inclusion hHJ t) w) := by
    rw [←Module.End.mul_apply,←Module.End.mul_apply,←map_mul,←map_mul]
    congr 1
    apply congrArg ρ
    apply Subtype.ext
    change (t : G) * (p : G) = ((t : G) * (p : G) * (t : G)⁻¹) * (t : G)
    group
  have hdiag (d : SL(2,E 1)) (x : Fin m → (Fin 2 → E 1)) :
      u (fun i => σ d (x i)) = fun i => σ (α d) (u x i) := by
    obtain ⟨r,rfl⟩ := eR.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 R)) d
    have hi : e.symm (fun i => σ (eR (QuotientGroup.mk' (pCore 2 R) r)) (x i)) =
        ρ (inclusion hRJ r) (e.symm x) := by
      apply e.injective
      rw [e.apply_symm_apply,he,e.apply_symm_apply]
      rfl
    dsimp only [Function.comp_apply]
    rw [hu,hi,hconj hRJ hHR,he,hα]
    rfl
  obtain ⟨f,hf,hfsemi⟩ := ScalarMultiplicity.exists_semilinear_multiplicity_equiv σ
    (fun l hl => SL2NaturalOffenders.centralizer_scalar l.toAddMonoidHom hl)
    α u s hdiag hs τ hsemi
  refine ⟨τ,s,f,?_,hsemi,hf,hfsemi,?_⟩
  · intro r z
    simpa only [hα] using hs (eR (QuotientGroup.mk' (pCore 2 R) r)) z
  · let κ : Representation (ZMod 2) A (Fin m → (Fin 2 → E 1)) :=
      (e.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp (ρ.comp (inclusion hAJ))
    apply ScalarMultiplicity.multiplicity_equiv_intertwines κ μ hμ
      (A.normalizerMonoidHom (inclusion hHA t)) u s f hf
    intro a x
    change e (ρ (inclusion hHJ t) (e.symm (e (ρ (inclusion hAJ a) (e.symm x))))) =
      e (ρ (inclusion hAJ (A.normalizerMonoidHom (inclusion hHA t) a))
        (e.symm (e (ρ (inclusion hHJ t) (e.symm x)))))
    rw [e.symm_apply_apply,e.symm_apply_apply,hconj hAJ hHA]
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
