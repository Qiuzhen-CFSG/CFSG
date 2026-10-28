module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.TwoFactorReconstruction.Source
public import Theory.Representation.BinaryPermutation.FiveNaturalNormalizer
public import Theory.Representation.BinaryOffender.ComponentSum

/-!
# The ambient stabilizer of the two reconstructed factors

On a binary linear natural module every invertible operator is already an
actor. The five-letter natural normalizer has the same property for operators
normalizing S₅. Transport these calculations along the actual marked models.
An ambient element preserving both factors consequently agrees on each moved
space with an element of that factor. Cross centralization and the full sum
identify it with the product of those two elements by faithfulness.

Source: Aschbacher–Smith, G.6.4(3), printed p.346.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06.TwoFactorReconstruction
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

private theorem realize_model_normalizer (A : Subgroup G) (U : Submodule (ZMod 2) V)
    {B W : Type*} [Group B] [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) B W) (hmodel : HasModelOn ρ A U τ)
    (hn : ∀ (f : W ≃ₗ[ZMod 2] W) (φ : MulAut B),
      (∀ b w, f (τ b w) = τ (φ b) (f w)) → ∃ b : B, ∀ w, f w = τ b w)
    (g : G) (hA : A.map (MulAut.conj g).toMonoidHom = A)
    (hU : U.map (ρ g) = U) :
    ∃ a : A, ∀ v : U, ρ g v = ρ a v := by
  obtain ⟨eA, eU, hs, he⟩ := hmodel
  let q : V ≃ₗ[ZMod 2] V :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V (ρ.asGroupHom g)
  let R : U ≃ₗ[ZMod 2] U := q.ofSubmodules U U hU
  let ψ : MulAut A := ((MulAut.conj g).subgroupMap A).trans (MulEquiv.subgroupCongr hA)
  let f := eU.symm.trans (R.trans eU)
  let φ : MulAut B := eA.symm.trans (ψ.trans eA)
  have hψ (a : A) : (ψ a : G) = g * a * g⁻¹ := rfl
  have hf (b : B) (w : W) : f (τ b w) = τ (φ b) (f w) := by
    obtain ⟨a, rfl⟩ := eA.surjective b
    obtain ⟨v, rfl⟩ := eU.surjective w
    simp only [f, φ, LinearEquiv.trans_apply, MulEquiv.trans_apply,
      eA.symm_apply_apply, eU.symm_apply_apply]
    rw [← he a v, eU.symm_apply_apply, ← he (ψ a) (R v)]
    apply congrArg eU
    apply Subtype.ext
    change ρ g (ρ a v) = ρ (ψ a) (ρ g v)
    rw [hψ]
    simp only [map_mul, Module.End.mul_apply, ρ.inv_self_apply]
  obtain ⟨b, hb⟩ := hn f φ hf
  refine ⟨eA.symm b, fun v => ?_⟩
  have hh := hb (eU v)
  simp only [f, LinearEquiv.trans_apply, eU.symm_apply_apply] at hh
  have ha := he (eA.symm b) v
  rw [eA.apply_symm_apply] at ha
  exact congrArg Subtype.val (eU.injective (hh.trans ha.symm))

/-- Every ambient normalizer acts on a small moved factor as one of its actors. -/
theorem smallFactor_realize_normalizer (A : Subgroup G)
    (hmodel : SmallFactorModel ρ A (subspaceCommutator ρ ⊤ A))
    (g : G) (hA : A.map (MulAut.conj g).toMonoidHom = A) :
    ∃ a : A, ∀ v : subspaceCommutator ρ ⊤ A, ρ g v = ρ a v := by
  have hU : (subspaceCommutator ρ ⊤ A).map (ρ g) = subspaceCommutator ρ ⊤ A := by
    rw [moved_map_conjugate, hA]
  rcases hmodel with hmodel | hmodel | hmodel
  · apply realize_model_normalizer A _ (binaryLinearAction 2) hmodel ?_ g hA hU
    intro f _ _
    exact ⟨f, fun _ => rfl⟩
  · apply realize_model_normalizer A _ (binaryLinearAction 3) hmodel ?_ g hA hU
    intro f _ _
    exact ⟨f, fun _ => rfl⟩
  · exact realize_model_normalizer A _ (BinaryPermutation.naturalRepresentation (Fin 5))
      hmodel BinaryPermutation.FiveNaturalNormalizer.normalizer g hA hU

private theorem fixes_of_cross_commutator (A : Subgroup G) (U : Submodule (ZMod 2) V)
    (hc : subspaceCommutator ρ U A = ⊥) (a : A) (v : U) : ρ a v = v := by
  apply sub_eq_zero.mp
  apply hc.le
  exact Submodule.subset_span ⟨a, a.property, v, v.property, rfl⟩

/-- Faithfulness identifies the stabilizer of both actual factors with their join. -/
theorem mem_closure_of_preserves_factors {a : G} (d : TwoFactorModules ρ a)
    (hf : Function.Injective ρ) (g : G)
    (h₁ : d.first.map (MulAut.conj g).toMonoidHom = d.first)
    (h₂ : d.second.map (MulAut.conj g).toMonoidHom = d.second) :
    g ∈ normalClosure ({a} : Set G) := by
  obtain ⟨b₁, hb₁⟩ := smallFactor_realize_normalizer d.first d.first_model g h₁
  obtain ⟨b₂, hb₂⟩ := smallFactor_realize_normalizer d.second d.second_model g h₂
  have he : g = (b₁ : G) * b₂ := by
    apply hf
    apply LinearMap.ext
    intro v
    have hv : v ∈ subspaceCommutator ρ ⊤ d.first ⊔ subspaceCommutator ρ ⊤ d.second := by
      rw [d.space_sum]
      trivial
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
    have hfix₁ := fixes_of_cross_commutator d.second _ d.cross_second b₂ ⟨v₁, hv₁⟩
    have hfix₂ := fixes_of_cross_commutator d.first _ d.cross_first b₁ ⟨v₂, hv₂⟩
    have hcomm : ρ b₁ (ρ b₂ v₂) = ρ b₂ (ρ b₁ v₂) := by
      have hc : (b₁ : G) * b₂ = (b₂ : G) * b₁ :=
        (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp d.commute) b₁.property)
          b₂ b₂.property).symm
      simp only [← Module.End.mul_apply, ← map_mul, hc]
    simp only [map_mul, Module.End.mul_apply, map_add]
    rw [hb₁ ⟨v₁, hv₁⟩, hb₂ ⟨v₂, hv₂⟩, hfix₁, hcomm, hfix₂]
  rw [he, ← d.join_eq]
  exact (d.first ⊔ d.second).mul_mem (mem_sup_left b₁.property) (mem_sup_right b₂.property)

end CFSG.Quasithin.ChapterG.Section06.TwoFactorReconstruction
