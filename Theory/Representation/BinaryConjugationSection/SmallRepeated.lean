module
public import Theory.Representation.IrreduciblePairBound
public import Theory.Representation.BinaryConjugationSection.InvariantPreimage

/-!+# Inequivalent simple sections in a repeated containing action

Zero-kernel conjugation coordinates transport the actual subgroup inclusion
to an injective intertwiner. The inequivalent-pair dimension bound excludes
a natural--dual pair from repetitions of a space smaller than that pair.
Both the subgroup and its containing action keep their literal markings.

Source application: Aschbacher--Smith 10.2.9, printed p.752.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Representation.BinaryConjugationSection
variable {G W X : Type*} [Group G]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup X] [Module (ZMod 2) X]
  {L H A R : Subgroup G} [IsElementaryAbelian 2 A]
  {ρ : Representation (ZMod 2) L W}
  (r : BinaryConjugationSection L A ⊥ ρ)
  {τ : Representation (ZMod 2) H X}
  (s : BinaryConjugationSection H R ⊥ τ)

include r s in
/-- Literal subgroup inclusion gives an injective intertwiner when both
specified coordinate kernels are zero. -/
theorem exists_injective_intertwiner (hLH : L ≤ H) (hAR : A ≤ R) :
    ∃ f : ρ.IntertwiningMap (τ.comp (inclusion hLH)), Function.Injective f := by
  have hrinj : Function.Injective r.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [r.kernel_eq,bot_subgroupOf]
  have hsinj : Function.Injective s.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [s.kernel_eq,bot_subgroupOf]
  let a : Additive A ≃ₗ[ZMod 2] W := LinearEquiv.ofBijective
    (r.coordinates.toAdditiveLeft.toZModLinearMap 2) ⟨hrinj,r.onto⟩
  let b : Additive A →ₗ[ZMod 2] X :=
    (s.coordinates.comp (inclusion hAR)).toAdditiveLeft.toZModLinearMap 2
  let f : ρ.IntertwiningMap (τ.comp (inclusion hLH)) := {
    toLinearMap := b.comp a.symm.toLinearMap
    isIntertwining' := by
      intro l
      apply LinearMap.ext
      intro w
      obtain ⟨u,rfl⟩ := a.surjective w
      let z : A := ⟨(l:G)*u.toMul*(l:G)⁻¹,
        (mem_normalizer_iff.mp (r.normalized l.property) u.toMul).mp u.toMul.property⟩
      have he : ρ l (a u) = a (Additive.ofMul z) := (r.equivariant l u.toMul).symm
      change b (a.symm (ρ l (a u))) = τ (inclusion hLH l) (b (a.symm (a u)))
      rw [he,a.symm_apply_apply,a.symm_apply_apply]
      exact s.equivariant (inclusion hLH l) (inclusion hAR u.toMul) }
  refine ⟨f,?_⟩
  exact ((hsinj.comp (inclusion_injective hAR)).comp
    (show Function.Injective (fun x : Additive A => x.toMul) from Function.injective_id)).comp
      a.symm.injective

end Representation.BinaryConjugationSection
