module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootPoints
/-!
# Coordinate actions for the pinned D4 normalizers

Each elementary root matrix acts by two coordinate transvections. We first
record that scalar formula, then compute the three-factor source normalizer
word. In characteristic two, the first three simple normalizers swap adjacent
hyperbolic pairs; the fourth swaps the last two pairs across the two halves.
The calculation is separated from the Clifford carrier to avoid repeatedly
elaborating its dependent isometry structures.

Source: GLS3, Chapter 1, Theorem 1.12.1(h), with the normalizer convention
fixed in `PinningTorus.RootPoints`.
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Pinning.PointGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
set_option linter.unusedSimpArgs false
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
def rootAction (r : RootIndex) (a : k) (z : HyperbolicSpace k 4) : HyperbolicSpace k 4 :=
  let i := r.1.1.1
  let j := r.1.1.2
  if r.2.1.1 = 1 then
    if r.2.2.1 = 1 then
      (z.1 + (a * z.2 j) • Pi.single i 1 - (a * z.2 i) • Pi.single j 1, z.2)
    else
      (z.1 + (a * z.1 j) • Pi.single i 1, z.2 - (a * z.2 i) • Pi.single j 1)
  else
    if r.2.2.1 = 1 then
      (z.1 + (a * z.1 i) • Pi.single j 1, z.2 - (a * z.2 j) • Pi.single i 1)
    else
      (z.1, z.2 + (a * z.1 j) • Pi.single i 1 - (a * z.1 i) • Pi.single j 1)
omit [IsAlgClosed k] [CharP k 2] in
theorem rootAction_spec (r : RootIndex) (a : k) (z : HyperbolicSpace k 4) :
    (evenOrthogonalRootQuadraticPoint 4 r a).1 z = rootAction k r a z := by
  rcases r with ⟨⟨⟨i,j⟩,hij⟩,s,t⟩
  unfold evenOrthogonalRootQuadraticPoint evenOrthogonalRootIsometry rootAction
  dsimp only
  split_ifs <;> rfl

theorem normalizer_apply (r : RootIndex) (t : kˣ) (z : HyperbolicSpace k 4) :
    (naturalAction k (normalizerWord k r t)).1 z =
      rootAction k r t (rootAction k (negativeRoot r) (-((t : k)⁻¹)) (rootAction k r t z)) := by
  simp only [normalizerWord, map_mul, naturalAction_rootPoint,
    Subgroup.coe_mul, LinearEquiv.mul_apply, rootAction_spec]

def simpleAction (i : Fin 4) (z : HyperbolicSpace k 4) : HyperbolicSpace k 4 :=
  ![(![z.1 1, z.1 0, z.1 2, z.1 3], ![z.2 1, z.2 0, z.2 2, z.2 3]),
    (![z.1 0, z.1 2, z.1 1, z.1 3], ![z.2 0, z.2 2, z.2 1, z.2 3]),
    (![z.1 0, z.1 1, z.1 3, z.1 2], ![z.2 0, z.2 1, z.2 3, z.2 2]),
    (![z.1 0, z.1 1, z.2 3, z.2 2], ![z.2 0, z.2 1, z.1 3, z.1 2])] i

omit [IsAlgClosed k] in
theorem simpleAction_word (i : Fin 4) (z : HyperbolicSpace k 4) :
    rootAction k (simpleRoot i) 1
      (rootAction k (negativeSimpleRoot i) 1 (rootAction k (simpleRoot i) 1 z)) =
        simpleAction k i z := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have h3 : (3 : k) = 1 := by linear_combination h2
  fin_cases i <;>
    dsimp [simpleRoot, typeDSimpleRootIndex, negativeSimpleRoot, negativeRoot]
  all_goals apply Prod.ext <;> funext p <;> fin_cases p
  all_goals
    dsimp [rootAction, simpleAction]
    (norm_num [Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, mul_add, add_mul];
      ring_nf; simp [h2, h3])

/-- The source simple normalizer acts by the displayed coordinate permutation. -/
theorem simpleNormalizer_apply (i : Fin 4) (z : HyperbolicSpace k 4) :
    (naturalAction k (simpleNormalizer k i)).1 z = simpleAction k i z := by
  refine (normalizer_apply k (simpleRoot i) 1 z).trans ?_
  simpa only [Units.val_one, inv_one, CharTwo.neg_eq] using simpleAction_word k i z

end Triality.SimplyConnected.Pinning.PointGeneration
