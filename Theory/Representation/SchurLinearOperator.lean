module

public import Theory.Representation.EndFieldDegree

/-!
# Operators over the actual Schur field

An operator commuting with all component endomorphisms acts linearly on the
original endomorphism-field module. Its square and automorphism intertwining
equations persist. The identical displacement range has dimension multiplied
by the Schur degree, so any displacement-to-dimension ratio descends.
Source application: Guralnick--Malle II, Section 3.5 and Lemma 8.6.
-/

@[expose] public noncomputable section
open scoped MonoidAlgebra
namespace Representation
namespace SchurOperator
variable {E G W : Type*} [Field E] [Group G] [AddCommGroup W] [Module E W]
  (τ : Representation E G W) (T : Module.End E W)
  (hc : ∀ (f : IntertwiningMap τ τ) (v : W), T (f v) = f (T v))

def linear : Module.End (Module.End E[G] τ.asModule) τ.asModule where
  toFun v := τ.asModuleEquiv.symm (T (τ.asModuleEquiv v))
  map_add' v w := by simp
  map_smul' c v := congrArg τ.asModuleEquiv.symm
    (hc ((IntertwiningMap.equivAlgEnd τ).symm c) (τ.asModuleEquiv v))

theorem linear_apply (v : τ.asModule) :
    τ.asModuleEquiv (linear τ T hc v) = T (τ.asModuleEquiv v) := rfl

theorem linear_square (hT : T*T=1) : linear τ T hc * linear τ T hc = 1 := by
  ext v
  exact congrArg τ.asModuleEquiv.symm (LinearMap.congr_fun hT (τ.asModuleEquiv v))

theorem linear_intertwines (α : MulAut G)
    (he : ∀ g v, T (τ g v) = τ (α g) (T v)) (g : G) (v : τ.asModule) :
    linear τ T hc (τ.endFieldRep g v) = τ.endFieldRep (α g) (linear τ T hc v) :=
  congrArg τ.asModuleEquiv.symm (he g (τ.asModuleEquiv v))

variable [Finite E] [FiniteDimensional E W] [τ.IsIrreducible]

private def rangeEquiv :
    LinearMap.range (linear τ T hc - LinearMap.id) ≃ₗ[E]
      LinearMap.range (T - LinearMap.id) where
  toFun v := ⟨τ.asModuleEquiv v, by
    obtain ⟨w,hw⟩ := v.property
    exact ⟨τ.asModuleEquiv w, congrArg τ.asModuleEquiv hw⟩⟩
  invFun v := ⟨τ.asModuleEquiv.symm v, by
    obtain ⟨w,hw⟩ := v.property
    exact ⟨τ.asModuleEquiv.symm w, congrArg τ.asModuleEquiv.symm hw⟩⟩
  left_inv v := Subtype.ext (τ.asModuleEquiv.symm_apply_apply v)
  right_inv v := Subtype.ext (τ.asModuleEquiv.apply_symm_apply v)
  map_add' v w := Subtype.ext (map_add τ.asModuleEquiv (v : τ.asModule) (w : τ.asModule))
  map_smul' c v := Subtype.ext (map_smul τ.asModuleEquiv c (v : τ.asModule))

theorem displacement_eq_schur_mul :
    Module.finrank E (LinearMap.range (T - LinearMap.id)) =
      Module.finrank E (Module.End E[G] τ.asModule) *
        Module.finrank (Module.End E[G] τ.asModule)
          (LinearMap.range (linear τ T hc - LinearMap.id)) := by
  rw [Module.finrank_mul_finrank]
  exact (rangeEquiv τ T hc).finrank_eq.symm

theorem ratio_descent (a b : ℕ)
    (h : a * Module.finrank (Module.End E[G] τ.asModule) τ.asModule ≤
      b * Module.finrank (Module.End E[G] τ.asModule)
        (LinearMap.range (linear τ T hc - LinearMap.id))) :
    a * Module.finrank E W ≤ b * Module.finrank E (LinearMap.range (T - LinearMap.id)) := by
  rw [finrank_eq_endField_mul τ, displacement_eq_schur_mul τ T hc]
  have hh := Nat.mul_le_mul_left (Module.finrank E (Module.End E[G] τ.asModule)) h
  nlinarith

end SchurOperator
end Representation
