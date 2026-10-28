module
public import Theory.Representation.IrreducibleDualBound
public import Theory.Representation.BinaryConjugationSection.InvariantPreimage
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Natural--dual obstructions for a literal generated orbit

Use the original zero-kernel section to embed its simple module in the
coordinates of its orbit. Every invariant subspace containing that image
pulls back to a subgroup containing the original generator and hence the
whole orbit. The small natural--dual generator obstruction then applies.

Source: Aschbacher--Smith 10.2.9, printed p.752.
-/

public noncomputable section
open scoped IsMulCommutative

open Subgroup
namespace Representation.BinaryConjugationSection
variable {G W X : Type*} [Group G]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X] [Nontrivial X]
  {L H A R : Subgroup G} [IsElementaryAbelian 2 A]
  {ρ : Representation (ZMod 2) L W} [IsIrreducible ρ]
  (r : BinaryConjugationSection L A ⊥ ρ)
  (σ : Representation (ZMod 2) H X)
  (s : BinaryConjugationSection H R ⊥ (σ.prod σ.dual))

include r s in
/-- A large simple section cannot generate the sum of a module and its dual. -/
theorem no_dual_sum_of_generates
    (hLH : L ≤ H) (hAR : A ≤ R) (hgen : R ≤ conjugateSpanBy A H)
    (hzero : ∀ b : ρ.IntertwiningMap ρ.dual, b = 0)
    (hd : Module.finrank (ZMod 2) X < 2 * Module.finrank (ZMod 2) W) : False := by
  have hrinj : Function.Injective r.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [r.kernel_eq,bot_subgroupOf]
  let a : Additive A ≃ₗ[ZMod 2] W := LinearEquiv.ofBijective
    (r.coordinates.toAdditiveLeft.toZModLinearMap 2) ⟨hrinj,r.onto⟩
  let b : Additive A →ₗ[ZMod 2] (X × Module.Dual (ZMod 2) X) :=
    (s.coordinates.comp (inclusion hAR)).toAdditiveLeft.toZModLinearMap 2
  have ha (w : A) : a (Additive.ofMul w) = (r.coordinates w).toAdd := rfl
  have hb (w : A) : b (Additive.ofMul w) =
      (s.coordinates (inclusion hAR w)).toAdd := rfl
  let f : ρ.IntertwiningMap ((σ.prod σ.dual).comp (inclusion hLH)) := {
    toLinearMap := b.comp a.symm.toLinearMap
    isIntertwining' := by
      intro l
      apply LinearMap.ext
      intro w
      obtain ⟨u,rfl⟩ := a.surjective w
      let z : A := ⟨(l:G)*u.toMul*(l:G)⁻¹,
        (mem_normalizer_iff.mp (r.normalized l.property) u.toMul).mp u.toMul.property⟩
      have he : ρ l (a u) = a (Additive.ofMul z) := (r.equivariant l u.toMul).symm
      change b (a.symm (ρ l (a u))) = (σ.prod σ.dual) (inclusion hLH l) (b (a.symm (a u)))
      rw [he,a.symm_apply_apply,a.symm_apply_apply]
      exact s.equivariant (inclusion hLH l) (inclusion hAR u.toMul) }
  apply no_small_simple_dual_generator σ (inclusion hLH) f hzero hd
  intro P hP
  have hAP : A ≤ s.invariantPreimage P := by
    intro w hw
    apply (s.mem_invariantPreimage P w).mpr
    refine ⟨hAR hw,?_⟩
    have hh := hP (a (Additive.ofMul (⟨w,hw⟩ : A)))
    change b (a.symm (a (Additive.ofMul (⟨w,hw⟩ : A)))) ∈ P.toSubmodule at hh
    rwa [a.symm_apply_apply] at hh
  have hRP : R ≤ s.invariantPreimage P := hgen.trans
    (conjugateSpanBy_le hAP (s.invariantPreimage_normalized P))
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro z _
  obtain ⟨u,rfl⟩ := s.onto (Multiplicative.ofAdd z)
  exact ((s.mem_invariantPreimage P u).mp (hRP u.property)).choose_spec
end Representation.BinaryConjugationSection
