module

public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.Kernel
public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.WordCertificates.ElevenRelations
public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.WordCertificates.CentralRelations

/-!
# Perfectness and the central quartic word in the literal paired M22 model

The four verified ATLAS relations give perfectness through the published
abelianization reduction. The distinguished word has fourth power one and
nontrivial square in its degree-4928 action, while its degree-22 component is
trivial by the published kernel theorem. Thus its order in the paired subgroup
is exactly four. Its two checked generator commutations give membership in the
center of that subgroup by the published generation reduction.

These theorems discharge the three word-certificate premises of the existing
cyclic-four-cover assembly. Identifying the entire projection kernel still
uses the independent paired-group order bound.

Source application: Aschbacher–Smith I.1.1 and I.1.3(4), printed p.407;
ATLAS representation `4M22G1-p4928aB0`, attributed in `CyclicFour/source/`.
The certificate method and measurements are in `WordCertificates/README.md`.
-/

namespace Sporadic.Mathieu.M22CyclicFour
open WordCertificates

public theorem model_isPerfect : Group.IsPerfect Model :=
  perfect_of_generator_relations aPerm_sq bPerm_four ab_eleven ababb_eleven

private theorem centralWord_fst : centralWord.val.1 = centralPerm := rfl

private theorem projection_apply_val (x : Model) :
    (projection x : Equiv.Perm (Fin 22)) = x.val.2 := rfl

private theorem centralWord_snd : centralWord.val.2 = 1 := by
  have h : projection centralWord = 1 := centralWord_mem_kernel
  have he := congrArg (fun x : M22 => (x : Equiv.Perm (Fin 22))) h
  rw [projection_apply_val] at he
  exact he

public theorem centralWord_pow_four : centralWord ^ 4 = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · change centralWord.val.1 ^ 4 = 1
    rw [centralWord_fst]
    exact centralPerm_four
  · change centralWord.val.2 ^ 4 = 1
    rw [centralWord_snd, one_pow]

public theorem centralWord_sq_ne_one : centralWord ^ 2 ≠ 1 := by
  intro h
  apply centralPerm_sq_ne_one
  have he := congrArg (fun x : Model => x.val.1) h
  change centralWord.val.1 ^ 2 = 1 at he
  rwa [centralWord_fst] at he

public theorem centralWord_order : orderOf centralWord = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) centralWord_sq_ne_one centralWord_pow_four

public theorem centralWord_commute_generatorA : Commute centralWord generatorA := by
  apply Subtype.ext
  apply Prod.ext
  · change centralWord.val.1 * Data.aPerm = Data.aPerm * centralWord.val.1
    rw [centralWord_fst]
    exact centralPerm_commute_a
  · change centralWord.val.2 * m22GeneratorA = m22GeneratorA * centralWord.val.2
    rw [centralWord_snd, one_mul, mul_one]

public theorem centralWord_commute_generatorB : Commute centralWord generatorB := by
  apply Subtype.ext
  apply Prod.ext
  · change centralWord.val.1 * Data.bPerm = Data.bPerm * centralWord.val.1
    rw [centralWord_fst]
    exact centralPerm_commute_b
  · change centralWord.val.2 * m22GeneratorB = m22GeneratorB * centralWord.val.2
    rw [centralWord_snd, one_mul, mul_one]

public theorem centralWord_mem_center : centralWord ∈ Subgroup.center Model :=
  centralWord_mem_center_of_commutes centralWord_commute_generatorA centralWord_commute_generatorB

end Sporadic.Mathieu.M22CyclicFour
