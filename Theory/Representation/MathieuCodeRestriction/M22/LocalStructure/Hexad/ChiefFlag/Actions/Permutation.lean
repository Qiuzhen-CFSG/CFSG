module

public import Theory.Representation.BinaryPermutationNaturalDuality

/-!
# The six-point core and deleted-module dual

The dot product pairs the augmentation core perfectly with the quotient by
constants. Its permutation invariance supplies the concrete duality used in
Aschbacher--Smith H.16.4(3), printed p.403 (1 March 2004 manuscript).
-/

@[expose] public section
noncomputable section
open Module
namespace MathieuCode.Hexad.ChiefFlag.Actions
open BinaryPermutation
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω]

def coreDeletedPairing : core Ω →ₗ[ZMod 2] Module.Dual (ZMod 2) (Deleted Ω) where
  toFun v := (constants Ω).liftQ (dotProductEquiv (ZMod 2) Ω v.val) (by
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    change (∑ i, v.val i * (c * 1)) = 0
    simp only [mul_one, ← Finset.sum_mul]
    rw [show ∑ i, v.val i = 0 from v.property, zero_mul])
  map_add' v w := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with | _ x =>
    change (∑ i, (v.val i + w.val i) * x i) = _
    simp only [add_mul, Finset.sum_add_distrib]
    rfl
  map_smul' c v := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with | _ x =>
    change (∑ i, (c * v.val i) * x i) = c * ∑ i, v.val i * x i
    simp only [mul_assoc, Finset.mul_sum]

theorem coreDeletedPairing_apply (v : core Ω) (w : Full Ω) :
    coreDeletedPairing Ω v ((constants Ω).mkQ w) = ∑ i, v.val i * w i := rfl

theorem coreDeletedPairing_injective : Function.Injective (coreDeletedPairing Ω) := by
  intro v w h
  apply Subtype.ext
  ext i
  have hi := LinearMap.congr_fun h ((constants Ω).mkQ (Pi.single i 1))
  change dotProduct v.val (Pi.single i 1) = dotProduct w.val (Pi.single i 1) at hi
  simpa only [dotProduct_single, mul_one] using hi

variable [Nonempty Ω]

def coreDeletedDualEquiv : core Ω ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Deleted Ω) :=
  LinearEquiv.ofBijective (coreDeletedPairing Ω) ⟨coreDeletedPairing_injective Ω,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Subspace.dual_finrank_eq, finrank_core, finrank_deleted])).mp
      (coreDeletedPairing_injective Ω)⟩

theorem coreDeletedDualEquiv_equivariant (g : Equiv.Perm Ω) (v : core Ω) :
    coreDeletedDualEquiv Ω (coreRepresentation Ω g v) =
      (deletedRepresentation Ω).dual g (coreDeletedDualEquiv Ω v) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with | _ w =>
  change (∑ i, v.val (g.symm i) * w i) = ∑ i, v.val i * w (g i)
  simpa using Equiv.sum_comp g.symm (fun i => v.val i * w (g i))

end MathieuCode.Hexad.ChiefFlag.Actions
