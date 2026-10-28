module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Consequences of a pinned D4 endomorphism on the actual Spin points

The shared predicate `IsPinned` specifies transport of the positive and negative
simple roots by the arm cycle `0 → 2 → 3 → 0`, fixing vertex `1`. It does not
postulate such an endomorphism. Given one, concrete Spin generation proves its
cube is the identity. A coefficient in the faithful natural representation
separates `x₀(1)` from `x₂(1)`, proving exact order three. The same transport
identities determine the source normalizer and coroot words.

Existence of the point endomorphism and regularity on the whole Spin variety
are separate construction problems. No regularity is transferred through the
point equivalence with the orthogonal image.

Source: GLS3, Theorem 1.15.2(a,b), with the word conventions of 1.12.1
(`refs/KGroup/GLS3/Chapter1.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Diagram
open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Pinning
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The two signed simple-root transport laws; this does not assert existence of a map. -/
def IsPinned (f : Points k →* Points k) : Prop :=
  (∀ i t, f (positiveSimplePoint k i t) =
    positiveSimplePoint k (typeD4DiagramPermutation i) t) ∧
  (∀ i t, f (negativeSimplePoint k i t) =
    negativeSimplePoint k (typeD4DiagramPermutation i) t)

/-- The eight pinned simple root groups determine a homomorphism on all Spin points. -/
theorem hom_ext {H : Type*} [Group H] {f g : Points k →* H}
    (hp : ∀ i t, f (positiveSimplePoint k i t) = g (positiveSimplePoint k i t))
    (hn : ∀ i t, f (negativeSimplePoint k i t) = g (negativeSimplePoint k i t)) : f = g := by
  apply MonoidHom.eq_of_eqOn_dense (simplePointSubgroup_eq_top k)
  rintro _ (⟨⟨i,t⟩, rfl⟩ | ⟨⟨i,t⟩, rfl⟩)
  · exact hp i t
  · exact hn i t

/-- Generation promotes the cubic diagram identity to every Spin point. -/
theorem IsPinned.cube {f : Points k →* Points k} (hf : IsPinned k f) (x : Points k) :
    f (f (f x)) = x := by
  have h : f.comp (f.comp f) = MonoidHom.id _ := by
    apply hom_ext k
    · intro i t
      simp only [MonoidHom.comp_apply, hf.1, typeD4DiagramPermutation_three,
        MonoidHom.id_apply]
    · intro i t
      simp only [MonoidHom.comp_apply, hf.2, typeD4DiagramPermutation_three,
        MonoidHom.id_apply]
  exact DFunLike.congr_fun h x

/-- A pinned endomorphism is invertible, with its square as inverse. -/
def IsPinned.pointAut {f : Points k →* Points k} (hf : IsPinned k f) : MulAut (Points k) where
  toFun := f
  invFun x := f (f x)
  left_inv := hf.cube k
  right_inv := hf.cube k
  map_mul' := f.map_mul

/-- A natural matrix coefficient separates these two genuinely different pinned points. -/
theorem positiveSimplePoint_zero_ne_two :
    positiveSimplePoint k 0 1 ≠ positiveSimplePoint k 2 1 := by
  intro h
  have h' := congrArg (naturalAction k) h
  simp only [positiveSimplePoint, naturalAction_rootPoint] at h'
  have he := congrArg (fun g : quadraticIsometrySubgroup (quadraticForm k) =>
    (g.val ((Pi.single 1 1), 0)).1 0) h'
  norm_num [simpleRoot, typeDSimpleRootIndex, evenOrthogonalRootQuadraticPoint,
    evenOrthogonalRootIsometry, hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
    Pi.single_apply] at he

/-- The moved root element makes the period exactly three. -/
theorem IsPinned.orderOf_pointAut {f : Points k →* Points k} (hf : IsPinned k f) :
    orderOf (hf.pointAut k) = 3 := by
  apply orderOf_eq_prime
  · ext x
    exact hf.cube k x
  · intro h
    have he := DFunLike.congr_fun h (positiveSimplePoint k 0 1)
    change f (positiveSimplePoint k 0 1) = positiveSimplePoint k 0 1 at he
    rw [hf.1] at he
    exact positiveSimplePoint_zero_ne_two k he.symm

/-- Transport of the source normalizer word, with the original parameter. -/
theorem IsPinned.simpleNormalizer {f : Points k →* Points k} (hf : IsPinned k f)
    (i : Fin 4) (t : kˣ) :
    f (normalizerWord k (simpleRoot i) t) =
      normalizerWord k (simpleRoot (typeD4DiagramPermutation i)) t := by
  change f (positiveSimplePoint k i (t : k) *
    negativeSimplePoint k i (-((t : k)⁻¹)) * positiveSimplePoint k i (t : k)) = _
  simp only [map_mul, hf.1, hf.2]
  rfl

/-- Transport of the source coroot word `h(t) = n(1)⁻¹ n(t)`. -/
theorem IsPinned.simpleCoroot {f : Points k →* Points k} (hf : IsPinned k f)
    (i : Fin 4) (t : kˣ) :
    f (simpleCoroot k i t) = simpleCoroot k (typeD4DiagramPermutation i) t := by
  simp only [Pinning.simpleCoroot, corootWord, map_mul, map_inv, hf.simpleNormalizer k]

end Triality.SimplyConnected.Diagram
