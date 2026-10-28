module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.Frobenius
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.RootDuality

/-!
# The exact construction input for local Ree calculations

An exceptional endomorphism is an endomorphism of the actual split F4
matrix group, specified on every root generator by the long–short root
permutation and its prescribed parameter power. Those equations imply its
square is Frobenius. Injectivity and finiteness give an automorphism, and
composition with the m-th Frobenius power defines the standard twist over
F_(2^(2m+1)). We take its fixed subgroup.

This is a conditional construction interface, not a construction of the
exceptional endomorphism. It allows local subgroup calculations to proceed
while the model owner proves existence. The simple family uses m ≥ 1;
the Tits endpoint must continue to use its separate checked presentation.

Source: Steinberg, Lectures on Chevalley Groups, exceptional characteristic-two
construction; Aschbacher–Smith, Remark A.2.4 and 2.3.9(7), printed p.526.
-/

@[expose] public section

open Theory.AlgebraicGroup ReeF4
namespace ReeF4

/-- Construction input allowed in the local Ree calculation: an actual
endomorphism of the root-generated matrix group with the precise exceptional
root equations. No existence, local subgroup or classification conclusion is
assumed. Its square-Frobenius identity is proved below. -/
structure LocalBlockInput (m : ℕ) where
  hom : SplitGroup m →* SplitGroup m
  root_formula : ∀ (r : F4Chevalley.Root) (t : CoefficientField m),
    hom (rootGeneratorInGroup m r t) =
      rootGeneratorInGroup m (exceptionalRootPermutation r) (exceptionalParameter r t)

/-- Frobenius powers act by the corresponding powers on root parameters. -/
theorem localBlock_frobenius_pow_root (m n : ℕ)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    ((splitFrobeniusEquiv m : MulAut (SplitGroup m)) ^ n)
      (rootGeneratorInGroup m r t) = rootGeneratorInGroup m r (t ^ (2 ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, splitFrobeniusEquiv_rootGenerator,
      pow_succ 2 n, pow_mul]

/-- The field degree is a period of Frobenius on the concrete split carrier. -/
theorem localBlock_frobenius_period (m : ℕ) :
    (splitFrobeniusEquiv m : MulAut (SplitGroup m)) ^ (2 * m + 1) = 1 := by
  have he : (((splitFrobeniusEquiv m : MulAut (SplitGroup m)) ^
      (2 * m + 1)).toMonoidHom) = MonoidHom.id _ := by
    apply splitGroup_hom_ext
    intro r t
    change ((splitFrobeniusEquiv m : MulAut (SplitGroup m)) ^ (2 * m + 1))
      (rootGeneratorInGroup m r t) = rootGeneratorInGroup m r t
    rw [localBlock_frobenius_pow_root, field_pow]
  exact MulEquiv.ext (fun x => DFunLike.congr_fun he x)

namespace LocalBlockInput
variable {m : ℕ}

/-- The generator equations force the square to be entrywise Frobenius. -/
theorem square (d : LocalBlockInput m) :
    d.hom.comp d.hom = splitFrobenius m := by
  apply splitGroup_hom_ext
  intro r t
  change d.hom (d.hom (rootGeneratorInGroup m r t)) = _
  rw [d.root_formula, d.root_formula, exceptionalRootPermutation_involutive,
    exceptionalParameter_twice, splitFrobenius_rootGenerator]

theorem hom_injective (d : LocalBlockInput m) : Function.Injective d.hom := by
  intro x y h
  apply splitFrobenius_injective m
  have he := congrArg d.hom h
  change (d.hom.comp d.hom) x = (d.hom.comp d.hom) y at he
  rwa [d.square] at he

noncomputable def automorphism (d : LocalBlockInput m) : MulAut (SplitGroup m) :=
  MulEquiv.ofBijective d.hom (Finite.injective_iff_bijective.mp d.hom_injective)

@[simp] theorem automorphism_apply (d : LocalBlockInput m) (x : SplitGroup m) :
    d.automorphism x = d.hom x := rfl

theorem automorphism_sq (d : LocalBlockInput m) :
    d.automorphism ^ 2 = splitFrobeniusEquiv m := by
  apply MulEquiv.ext
  intro x
  change d.hom (d.hom x) = splitFrobenius m x
  exact DFunLike.congr_fun d.square x

noncomputable def twist (d : LocalBlockInput m) : MulAut (SplitGroup m) :=
  d.automorphism * (splitFrobeniusEquiv m) ^ m

/-- The genuine fixed subgroup of the exceptional field twist. At m = 0 this
is the full fixed-point construction, not a definition of the Tits simple group. -/
noncomputable def fixedGroup (d : LocalBlockInput m) : Subgroup (SplitGroup m) :=
  d.twist.toMonoidHom.eqLocus (MonoidHom.id _)

theorem twist_eq_pow (d : LocalBlockInput m) :
    d.twist = d.automorphism ^ (2 * m + 1) := by
  rw [twist, ← d.automorphism_sq, ← pow_mul, pow_succ']

@[simp] theorem mem_fixedGroup (d : LocalBlockInput m) (x : SplitGroup m) :
    x ∈ d.fixedGroup ↔ d.twist x = x := Iff.rfl

instance (d : LocalBlockInput m) : Finite d.fixedGroup := inferInstance

/-- The field twist retains the explicit exceptional root formula. -/
theorem twist_root (d : LocalBlockInput m)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    d.twist (rootGeneratorInGroup m r t) =
      rootGeneratorInGroup m (exceptionalRootPermutation r)
        (exceptionalParameter r (t ^ (2 ^ m))) := by
  change d.automorphism (((splitFrobeniusEquiv m : MulAut (SplitGroup m)) ^ m)
    (rootGeneratorInGroup m r t)) = _
  rw [localBlock_frobenius_pow_root, automorphism_apply, d.root_formula]

/-- Over the chosen finite field the exceptional field twist squares to one. -/
theorem twist_sq (d : LocalBlockInput m) : d.twist ^ 2 = 1 := by
  rw [d.twist_eq_pow, ← pow_mul, Nat.mul_comm (2 * m + 1) 2, pow_mul,
    d.automorphism_sq]
  exact localBlock_frobenius_period m

end LocalBlockInput
end ReeF4

end
