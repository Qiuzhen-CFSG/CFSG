module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Ambient
public import Theory.SpecificGroups.SymmetricFive.AutomorphismRank
public import Theory.GroupTheory.PCoreSurjective

/-!
# Intrinsic kernels of the two Rudvalis local actions

The certified orders of the fixed max4 and max6 word subgroups are
344064 and 245760. A surjection to PSL₃(2), respectively S₅, therefore has
kernel of order 2048. Both targets have trivial two-core, so p-core lifting
identifies the kernel with the intrinsic two-core of the word subgroup.
The first isomorphism theorem gives the actual quotient equivalence and
preserves its projection map. No splitting is asserted or needed.

The surjections remain explicit inputs here: orders alone do not identify
the quotients. The concrete action constructions discharge these inputs.
Source: GLS3 Table 5.3r and its max4 justification, printed pp.291–292;
Aschbacher–Smith E.1.14(5), printed p.214, citing Asc82a, Lemma 4.9.
-/

namespace Rudvalis.CoreQuotients

open Subgroup SylowOvergroups

/-- Any surjection from the marked max4 group to PSL₃(2) has kernel order 2048. -/
public theorem max4_kernel_card (f : max4 →* Matrix.PSL3Two.PSL)
    (hf : Function.Surjective f) : Nat.card f.ker = 2048 := by
  have hi : f.ker.index = 168 := by
    rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf, Subgroup.card_top,
      Matrix.PSL3Two.card_PSL]
  have hc := f.ker.card_mul_index
  rw [hi, max4_card] at hc
  omega

/-- Any surjection from the marked max6 group to S₅ has kernel order 2048. -/
public theorem max6_kernel_card (f : max6 →* Equiv.Perm (Fin 5))
    (hf : Function.Surjective f) : Nat.card f.ker = 2048 := by
  have hi : f.ker.index = 120 := by
    rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf, Subgroup.card_top,
      Nat.card_perm, Nat.card_fin]
    decide
  have hc := f.ker.card_mul_index
  rw [hi, max6_card] at hc
  omega

/-- The max4 action kernel is its intrinsic two-core, without a split-extension premise. -/
public theorem max4_kernel_eq_pCore (f : max4 →* Matrix.PSL3Two.PSL)
    (hf : Function.Surjective f) : f.ker = pCore 2 max4 := by
  have hp : IsPGroup 2 f.ker := IsPGroup.of_card (n := 11) (max4_kernel_card f hf)
  have he := f.comap_pCore_of_ker_isPGroup hf hp
  rw [Matrix.PSL3Two.pCore_two_PSL_eq_bot] at he
  exact he

/-- The max6 action kernel is its intrinsic two-core, without a split-extension premise. -/
public theorem max6_kernel_eq_pCore (f : max6 →* Equiv.Perm (Fin 5))
    (hf : Function.Surjective f) : f.ker = pCore 2 max6 := by
  have hp : IsPGroup 2 f.ker := IsPGroup.of_card (n := 11) (max6_kernel_card f hf)
  have he := f.comap_pCore_of_ker_isPGroup hf hp
  rw [Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot] at he
  exact he

/-- The equivalence induced by a full max4 action on the binary three-space. -/
public noncomputable def max4QuotientEquivOfSurjective
    (f : max4 →* Matrix.PSL3Two.PSL) (hf : Function.Surjective f) :
    (max4 ⧸ pCore 2 max4) ≃* Matrix.PSL3Two.PSL :=
  (QuotientGroup.quotientMulEquivOfEq (max4_kernel_eq_pCore f hf).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The equivalence induced by a full max6 action on five letters. -/
public noncomputable def max6QuotientEquivOfSurjective
    (f : max6 →* Equiv.Perm (Fin 5)) (hf : Function.Surjective f) :
    (max6 ⧸ pCore 2 max6) ≃* Equiv.Perm (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq (max6_kernel_eq_pCore f hf).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- Compatibility with the literal intrinsic quotient projection for max4. -/
@[simp] public theorem max4QuotientEquivOfSurjective_mk
    (f : max4 →* Matrix.PSL3Two.PSL) (hf : Function.Surjective f) (g : max4) :
    max4QuotientEquivOfSurjective f hf (QuotientGroup.mk' (pCore 2 max4) g) = f g := by
  rfl

/-- Compatibility with the literal intrinsic quotient projection for max6. -/
@[simp] public theorem max6QuotientEquivOfSurjective_mk
    (f : max6 →* Equiv.Perm (Fin 5)) (hf : Function.Surjective f) (g : max6) :
    max6QuotientEquivOfSurjective f hf (QuotientGroup.mk' (pCore 2 max6) g) = f g := by
  rfl

end Rudvalis.CoreQuotients
