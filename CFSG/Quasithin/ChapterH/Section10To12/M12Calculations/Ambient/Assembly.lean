module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.Centralizer
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.AmbientInput
public import Theory.Mathieu.M12.ValueBoundParabolics.Ambient
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Ambient conjugation and extension transport for the M₁₂ heart

The native scalar-centralizer calculation makes conjugation on the solvable
residual faithful. Two operators implementing the same automorphism differ by
an operator centralizing the residual. They therefore coincide over F₂. Thus
any faithful extension of the native heart representation supplies the exact
ambient witness, including the original residual and module markings.

The construction of that native extension is a separate input here.
Source: Aschbacher–Smith H.11.1, printed pp.392–393 (1 March 2004 manuscript).
-/

public section

namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient
open Sporadic.Mathieu
open LinearMap.GeneralLinearGroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V} (h : M12ModuleInput ρ)

/-- Conjugation on the solvable residual in its prescribed native marking. -/
noncomputable def embedding : G →* MulAut M12 :=
  (MulAut.congr h.residualEquiv).toMonoidHom.comp
    (MulAut.conjNormal (H := Subgroup.solvableResidual G))

/-- The conjugation homomorphism preserves each marked residual element. -/
theorem embedding_residual (t : Subgroup.solvableResidual G) :
    embedding h (t : G) = MulAut.conj (h.residualEquiv t) := by
  change MulAut.congr h.residualEquiv (MulAut.conjNormal (t : G)) = _
  rw [MulAut.conjNormal_val, MulAut.congr_conj]

private noncomputable def transported : Representation (ZMod 2) G M12Heart :=
  h.moduleEquiv.toLinearEquiv.conjRingEquiv.toMonoidHom.comp ρ

private theorem transported_residual (t : Subgroup.solvableResidual G) :
    transported h (t : G) = m12HeartRepresentation (h.residualEquiv t) :=
  Representation.Equiv.conj_apply_self t h.moduleEquiv

private theorem transported_intertwines (g : G) (x : M12) (v : M12Heart) :
    transported h g (m12HeartRepresentation x v) =
      m12HeartRepresentation (embedding h g x) (transported h g v) := by
  let t := h.residualEquiv.symm x
  let s := MulAut.conjNormal (H := Subgroup.solvableResidual G) g t
  have ht : h.residualEquiv t = x := h.residualEquiv.apply_symm_apply x
  have hs : h.residualEquiv s = embedding h g x := rfl
  have hg : g * (t : G) = (s : G) * g := by
    change g * (t : G) = (g * (t : G) * g⁻¹) * g
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  have he : transported h g * m12HeartRepresentation x =
      m12HeartRepresentation (embedding h g x) * transported h g := by
    calc
      _ = transported h g * transported h (t : G) := by rw [transported_residual, ht]
      _ = transported h (g * (t : G)) := (map_mul _ _ _).symm
      _ = transported h ((s : G) * g) := congrArg (transported h) hg
      _ = transported h (s : G) * transported h g := map_mul _ _ _
      _ = _ := by rw [transported_residual, hs]
  exact congrArg (fun f : Module.End (ZMod 2) M12Heart => f v) he

/-- Faithfulness follows from the trivial linear centralizer of the residual. -/
theorem embedding_injective : Function.Injective (embedding h) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have he := heart_centralizer (toLinearEquiv ((transported h).asGroupHom g)) (by
    intro x v
    change transported h g (m12HeartRepresentation x v) =
      m12HeartRepresentation x (transported h g v)
    simpa only [hg, MulAut.one_apply] using transported_intertwines h g x v)
  have hq : transported h g = transported h 1 := by
    rw [map_one]
    apply LinearMap.ext
    intro v
    exact congrArg (fun f : M12Heart ≃ₗ[ZMod 2] M12Heart => f v) he
  apply h.faithful
  exact h.moduleEquiv.toLinearEquiv.conjRingEquiv.injective hq

include h in
/-- The actual relative centralizer of the solvable residual is trivial. -/
theorem centralizer_residual_eq_bot :
    Subgroup.centralizer (Subgroup.solvableResidual G : Set G) = ⊥ := by
  rw [← MulAut.conjNormal_ker_eq_centralizer]
  apply (MonoidHom.ker_eq_bot_iff _).mpr
  intro a b hab
  apply embedding_injective h
  exact congrArg (MulAut.congr h.residualEquiv) hab

private theorem extension_intertwines
    (σ : Representation (ZMod 2) (MulAut M12) M12Heart)
    (hi : σ.comp MulAut.conj = m12HeartRepresentation)
    (a : MulAut M12) (x : M12) (v : M12Heart) :
    σ a (m12HeartRepresentation x v) = m12HeartRepresentation (a x) (σ a v) := by
  have hin (t : M12) : σ (MulAut.conj t) = m12HeartRepresentation t :=
    congrArg (fun τ : Representation (ZMod 2) M12 M12Heart => τ t) hi
  have ha : a * MulAut.conj x = MulAut.conj (a x) * a := by
    ext y
    simp [MulAut.conj_apply]
  have he : σ a * m12HeartRepresentation x = m12HeartRepresentation (a x) * σ a := by
    rw [← hin, ← hin, ← map_mul, ← map_mul, ha]
  exact congrArg (fun f : Module.End (ZMod 2) M12Heart => f v) he

/-- Transport a native faithful extension using the original module equivalence. -/
noncomputable def extensionOfRepresentation
    (σ : Representation (ZMod 2) (MulAut M12) M12Heart)
    (hf : Function.Injective σ) (hi : σ.comp MulAut.conj = m12HeartRepresentation) :
    AmbientExtension ρ h where
  automorphismRepresentation := σ
  automorphismRepresentation_faithful := hf
  inner_action := hi
  embedding := embedding h
  embedding_injective := embedding_injective h
  embedding_residual := embedding_residual h
  equivariant := by
    intro g v
    have he := heart_intertwiner_unique (embedding h g)
      (toLinearEquiv ((transported h).asGroupHom g))
      (toLinearEquiv (σ.asGroupHom (embedding h g)))
      (transported_intertwines h g) (extension_intertwines σ hi (embedding h g))
    have hv := congrArg (fun f : M12Heart ≃ₗ[ZMod 2] M12Heart =>
      f (h.moduleEquiv.toLinearEquiv v)) he
    change h.moduleEquiv.toLinearEquiv
      (ρ g (h.moduleEquiv.toLinearEquiv.symm (h.moduleEquiv.toLinearEquiv v))) =
      σ (embedding h g) (h.moduleEquiv.toLinearEquiv v) at hv
    simpa only [LinearEquiv.symm_apply_apply] using hv

include h in
/-- The ambient group is the native M₁₂ or its full abstract automorphism group.
This uses the existing self-centralizing ambient reduction and degree-24 model. -/
theorem group_equiv_alternatives :
    Nonempty (G ≃* M12) ∨ Nonempty (G ≃* MulAut M12) := by
  rcases M12SmallPair.ValueBoundParabolics.Ambient.ambient_equiv_alternatives
    (Subgroup.solvableResidual G) (centralizer_residual_eq_bot h) h.residualEquiv with
    ⟨_, he⟩ | ⟨e, _⟩
  · exact Or.inl he
  · exact Or.inr ⟨e.trans M12ExceptionalExtension.automorphismEquiv⟩

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient
