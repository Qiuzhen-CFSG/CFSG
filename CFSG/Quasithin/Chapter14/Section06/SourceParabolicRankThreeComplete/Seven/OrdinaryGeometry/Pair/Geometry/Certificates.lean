module
public import Theory.Representation.BinaryPermutation.SevenParabolic.Ordinary

/-!
# Finite binary-plane certificates for the two seven-letter parabolics

An invariant plane on which nonzero words have equal weight has the standard
three-pair shape in the lambda case, and the complementary three-letter shape
in the theta case. The checks enumerate the 64 even binary words in each of
the two basis positions, using only three specified even permutations.
The source application and the point alignment are proved separately.
Source: Aschbacher--Smith, original14.6.10(5), printed p.1029.
-/

@[expose] public section
open Subgroup Equiv BinaryPermutation BinaryPermutation.SevenParabolic
open BinaryPermutation.SevenParabolic.Ordinary
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.FiniteGeometry
private local instance : DecidablePred (fun v : Full (Fin 7) => v ∈ core (Fin 7)) :=
  fun v => inferInstanceAs (Decidable ((augmentation (Fin 7)) v = 0))
private local instance : Fintype Space :=
  Fintype.ofFinset (Finset.univ.filter fun v => v ∈ core (Fin 7)) (by simp)
def inPlane (u v w : Space) : Prop := w = 0 ∨ w = u ∨ w = v ∨ w = u + v
private instance (u v w : Space) : Decidable (inPlane u v w) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
def pairRotate : Perm (Fin 7) := (swap 0 2 * swap 2 4) * (swap 1 3 * swap 3 5)
def pairExchange : Perm (Fin 7) := swap 0 2 * swap 1 3
def mixedSwap : Perm (Fin 7) := swap 0 1 * swap 4 5
def preservesPair (g : Perm (Fin 7)) (u v : Space) : Prop :=
  inPlane u v (action g u) ∧ inPlane u v (action g v)
private instance (g : Perm (Fin 7)) (u v : Space) : Decidable (preservesPair g u v) :=
  inferInstanceAs (Decidable (_ ∧ _))
set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 256 in
theorem lambda_cert : ∀ u v : Space,
    u ≠ 0 → v ≠ 0 → u ≠ v → weight v = weight u → weight (u + v) = weight u →
    preservesPair pairRotate u v → preservesPair doubleSwap u v →
    preservesPair pairExchange u v →
    inPlane firstFour secondFour u ∧ inPlane firstFour secondFour v := by
  decide +kernel
set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 256 in
theorem theta_cert : ∀ u v : Space,
    u ≠ 0 → v ≠ 0 → u ≠ v → weight v = weight u → weight (u + v) = weight u →
    preservesPair complementCycle u v → preservesPair mixedSwap u v →
    preservesPair pairExchange u v →
    inPlane pair56 pair57 u ∧ inPlane pair56 pair57 v := by
  decide +kernel
end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.FiniteGeometry
