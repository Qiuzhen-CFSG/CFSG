module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Carrier
public import Theory.AlgebraicGroup.RootSystems.TypeD4DiagramTriality

/-!
# Root points and source coroot words in the Clifford Spin carrier

The faithful natural action in characteristic two gives a unique Spin lift of
each standard orthogonal root matrix. Parameter recovery in that matrix proves
injectivity, and faithfulness transports its additive law. The positive simple
roots use the standard D4 numbering (central vertex 1, arms 0, 2, 3).

The words `n` and `h` have exactly the conventions of GLS3, Theorem 1.12.1:
`n(t) = x(t) x₋(-t⁻¹) x(t)` and `h(t) = n(1)⁻¹ n(t)`.
These are definitions of points; no regular inverse to the Spin cover is used
or asserted. Regular root curves and the coroot torus require separate proofs.

Source: `refs/KGroup/GLS3/Chapter1.tex`, §§1.12 and 1.14.
-/

@[expose] public section
noncomputable section

namespace Triality.SimplyConnected.Pinning
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped commutatorElement

universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The standard coordinate D4 roots. -/
abbrev RootIndex := TypeDRootIndex 4

/-- Negation of both signs in the standard coordinate root. -/
def negativeRoot (r : RootIndex) : RootIndex :=
  ⟨r.1, ⟨-r.2.1.1, by
    rcases (show r.2.1.1 = -1 ∨ r.2.1.1 = 1 from r.2.1.2) with h | h <;> simp [h]⟩,
    ⟨-r.2.2.1, by rcases (show r.2.2.1 = -1 ∨ r.2.2.1 = 1 from r.2.2.2) with h | h <;> simp [h]⟩⟩

@[simp] theorem negativeRoot_negativeRoot (r : RootIndex) :
    negativeRoot (negativeRoot r) = r := by
  rcases r with ⟨ij, s, t⟩
  simp [negativeRoot]

/-- This sign operation really negates the root vector. -/
theorem negativeRoot_vector (r : RootIndex) :
    typeDRootVector 4 (negativeRoot r) = -typeDRootVector 4 r := by
  rcases r with ⟨ij, s, t⟩
  simp [negativeRoot, typeDRootVector, add_comm]

omit [CharP k 2] in
/-- The root matrix lies in Omega because it is an actual commutator. -/
theorem rootMatrix_mem_omega (r : RootIndex) (a : k) :
    evenOrthogonalRootQuadraticPoint 4 r a ∈
      commutator (quadraticIsometrySubgroup (quadraticForm k)) := by
  obtain ⟨g, h, he⟩ := evenOrthogonalRootQuadraticPoint_is_commutator 4 r a
  rw [he, commutator_eq_closure]
  exact Subgroup.subset_closure (commutator_mem_commutatorSet g h)

/-- The unique Spin point acting as the prescribed elementary root matrix. -/
def rootPoint (r : RootIndex) (a : k) : Points k :=
  (omegaPointEquiv k).symm
    ⟨evenOrthogonalRootQuadraticPoint 4 r a, rootMatrix_mem_omega k r a⟩

@[simp] theorem naturalAction_rootPoint (r : RootIndex) (a : k) :
    naturalAction k (rootPoint k r a) = evenOrthogonalRootQuadraticPoint 4 r a := by
  exact congrArg Subtype.val ((omegaPointEquiv k).apply_symm_apply _)

/-- Matrix coefficients characterize the lift uniquely. -/
theorem eq_rootPoint_iff (r : RootIndex) (a : k) (x : Points k) :
    x = rootPoint k r a ↔
      naturalAction k x = evenOrthogonalRootQuadraticPoint 4 r a := by
  rw [← naturalAction_rootPoint k r a]
  exact (naturalAction_injective k).eq_iff.symm

@[simp] theorem rootPoint_zero (r : RootIndex) : rootPoint k r 0 = 1 := by
  apply naturalAction_injective k
  simp [evenOrthogonalRootQuadraticPoint_zero]

/-- The additive root-group law is inherited through a faithful action. -/
theorem rootPoint_add (r : RootIndex) (a b : k) :
    rootPoint k r (a + b) = rootPoint k r a * rootPoint k r b := by
  apply naturalAction_injective k
  simp [evenOrthogonalRootQuadraticPoint_add]

@[simp] theorem rootPoint_neg (r : RootIndex) (a : k) :
    rootPoint k r (-a) = (rootPoint k r a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← rootPoint_add, neg_add_cancel, rootPoint_zero]

/-- The parameter is recovered in one coefficient of the natural action. -/
theorem rootPoint_parameter (r : RootIndex) (a : k) :
    evenOrthogonalRootCoordinate 4 r
      ((naturalAction k (rootPoint k r a)).1 (evenOrthogonalRootSource 4 r)) = a := by
  rw [naturalAction_rootPoint, evenOrthogonalRoot_parameter_recovery]

theorem rootPoint_injective (r : RootIndex) : Function.Injective (rootPoint k r) := by
  intro a b hab
  rw [← rootPoint_parameter k r a, ← rootPoint_parameter k r b, hab]

/-- The additive root parameter, written multiplicatively for subgroup APIs. -/
def rootPointHom (r : RootIndex) : Multiplicative k →* Points k where
  toFun a := rootPoint k r a.toAdd
  map_one' := rootPoint_zero k r
  map_mul' a b := rootPoint_add k r a.toAdd b.toAdd

/-- The root subgroup of the point group. Closedness is a separate obligation. -/
def rootPointSubgroup (r : RootIndex) : Subgroup (Points k) :=
  (rootPointHom k r).range

/-- The source's numbered positive simple root. -/
abbrev simpleRoot (i : Fin 4) : RootIndex := typeDSimpleRootIndex 2 i

/-- The source's numbered negative simple root. -/
abbrev negativeSimpleRoot (i : Fin 4) : RootIndex := negativeRoot (simpleRoot i)

/-- Positive simple root points, with central vertex 1. -/
abbrev positiveSimplePoint (i : Fin 4) (a : k) : Points k :=
  rootPoint k (simpleRoot i) a

/-- Negative simple root points in the same matrix normalization. -/
abbrev negativeSimplePoint (i : Fin 4) (a : k) : Points k :=
  rootPoint k (negativeSimpleRoot i) a

/-- The normalizer word of GLS3 1.12.1. -/
def normalizerWord (r : RootIndex) (t : kˣ) : Points k :=
  rootPoint k r (t : k) * rootPoint k (negativeRoot r) (-((t : k)⁻¹)) *
    rootPoint k r (t : k)

/-- The coroot word of GLS3 1.12.1, with its specified order of multiplication. -/
def corootWord (r : RootIndex) (t : kˣ) : Points k :=
  (normalizerWord k r 1)⁻¹ * normalizerWord k r t

/-- The four normalizer representatives come from this same pinning. -/
abbrev simpleNormalizer (i : Fin 4) : Points k := normalizerWord k (simpleRoot i) 1

/-- The four simple coroot point maps. -/
abbrev simpleCoroot (i : Fin 4) (t : kˣ) : Points k := corootWord k (simpleRoot i) t

@[simp] theorem corootWord_one (r : RootIndex) : corootWord k r 1 = 1 := by
  simp [corootWord]

/-- In characteristic two each root point is its own inverse. -/
@[simp] theorem rootPoint_inv (r : RootIndex) (a : k) :
    (rootPoint k r a)⁻¹ = rootPoint k r a := by
  rw [← rootPoint_neg, CharTwo.neg_eq]

/-- The palindromic normalizer word is also its own inverse in characteristic two. -/
@[simp] theorem normalizerWord_inv (r : RootIndex) (t : kˣ) :
    (normalizerWord k r t)⁻¹ = normalizerWord k r t := by
  simp [normalizerWord, mul_assoc]

/-- The source relation `nα(1)² = hα(-1)` specializes to involutivity. -/
theorem normalizerWord_sq (r : RootIndex) (t : kˣ) :
    normalizerWord k r t ^ 2 = 1 := by
  calc
    normalizerWord k r t ^ 2 =
        (normalizerWord k r t)⁻¹ * normalizerWord k r t := by
      rw [normalizerWord_inv, pow_two]
    _ = 1 := inv_mul_cancel _

/-- Every verified natural-action conjugation formula lifts uniquely to Spin. -/
theorem rootPoint_conjugation_of_naturalAction
    (g : Points k) (r s : RootIndex) (a b : k)
    (h : (naturalAction k g)⁻¹ * evenOrthogonalRootQuadraticPoint 4 r a *
      naturalAction k g = evenOrthogonalRootQuadraticPoint 4 s b) :
    g⁻¹ * rootPoint k r a * g = rootPoint k s b := by
  apply naturalAction_injective k
  simpa only [map_mul, map_inv, naturalAction_rootPoint] using h

end Triality.SimplyConnected.Pinning
