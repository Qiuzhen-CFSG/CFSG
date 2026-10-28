module
public import Theory.SpecificGroups.MinusExtraspecial.ActionConjugacy
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.CoreComplement

/-!
# Recognizing the split Hall--Janko endpoint with its core marking

Faithful alternating actions on the minus extraspecial core are conjugate
by an inner core automorphism. Apply this to the actual native A₅ complement,
then undo that inner conjugation in the full native endpoint. The resulting
isomorphism fixes the prescribed core coordinates exactly.

Source: DGS, Groups and Graphs (1985), (5.16), p.117 and the J₂ exercise
following (10.9), p.163. This recognizes one split endpoint, not an amalgam.
-/

public noncomputable section
open Subgroup
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
open MinusExtraspecial MinusExtraspecial.AlternatingAction

/-- Every faithful split A₅ extension of the minus core is the native first
endpoint, with the literal core inclusion square. -/
theorem faithful_split_equiv
    (φ : alternatingGroup (Fin 5) →* MulAut Model) (hφ : Function.Injective φ) :
    ∃ f : Model ⋊[φ] alternatingGroup (Fin 5) ≃* Seed.l₁,
      ∀ q : Model, f (SemidirectProduct.inl q) = (coreModelEquiv.symm q : Seed.l₁) := by
  obtain ⟨C,hC,⟨eC⟩⟩ := exists_core_complement
  let N := pCore 2 Seed.l₁
  let ψ := complementAction N coreModelEquiv C eC
  have hψ : Function.Injective ψ :=
    complementAction_injective N coreModelEquiv core_selfCentralizing C hC eC
  obtain ⟨d,n,hn⟩ := MinusExtraspecial.ActionConjugacy.exists_faithful_conjugacy φ ψ hφ hψ
  let a := MulAut.conj n
  let s : Model ⋊[φ] alternatingGroup (Fin 5) ≃* Model ⋊[ψ] alternatingGroup (Fin 5) :=
    SemidirectProduct.congr a d (fun g => MulEquiv.ext fun q => DFunLike.congr_fun (hn g) q)
  let t := (splitEquiv N coreModelEquiv C hC eC).symm
  let m : Seed.l₁ := coreModelEquiv.symm n
  let f := s.trans (t.trans (MulAut.conj m⁻¹))
  refine ⟨f,fun q => ?_⟩
  have hs : s (SemidirectProduct.inl q) = SemidirectProduct.inl (a q) := by
    apply SemidirectProduct.ext <;> simp [s,SemidirectProduct.congr]
  change m⁻¹ * t (s (SemidirectProduct.inl q)) * (m⁻¹)⁻¹ = _
  rw [hs]
  have ht : t (SemidirectProduct.inl (a q)) = (coreModelEquiv.symm (a q) : Seed.l₁) := by
    change (coreModelEquiv.symm (a q) : Seed.l₁) * (eC.symm 1 : Seed.l₁) = _
    rw [map_one,Subgroup.coe_one,mul_one]
  rw [ht]
  change (coreModelEquiv.symm n : Seed.l₁)⁻¹ *
    (coreModelEquiv.symm (n*q*n⁻¹) : Seed.l₁) *
      ((coreModelEquiv.symm n : Seed.l₁)⁻¹)⁻¹ = _
  simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv]
  group

end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
