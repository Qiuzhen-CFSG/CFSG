module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.Pinned
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.PointRealization.Roots

/-!
# Construction of the pinned D4 endomorphism on Spin points

The actual Clifford action preserves the embedded even half-spin space on
all eight signed simple root groups. Its action there agrees with the
natural action after the D4 arm cycle. Consider the Spin points whose
half-spin action agrees with the natural action of some other Spin point.
This set is a subgroup containing the signed simple generators, hence the
whole group. The other point is unique, because the half-spin embedding and
the natural Spin action in characteristic two are injective. Uniqueness
then proves multiplicativity and identifies the images of the generators.

Thus well-definedness comes from an actual Clifford representation, without
assuming a diagram map or a converse to Chevalley relator evaluation.
The construction is on the fixed carrier and requires no extra simplicity
or universality premise. Regularity is a separate construction; the point
isomorphism from Spin to its orthogonal image is never asserted regular.

Source: GLS3, Theorem 1.15.2(a), via the half-spin representation described
in §1.14.9(f) (`refs/KGroup/GLS3/Chapter1.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Diagram.HalfSpin
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Pinning
variable (k : Type*) [Field k] [CharP k 2] [IsAlgClosed k]

private def Intertwines (x y : Points k) : Prop :=
  ∀ v, pointAction k x (embedding k v) = embedding k ((naturalAction k y).val v)

private theorem intertwines_one : Intertwines k 1 1 := by
  intro v
  simp [map_one]

private theorem Intertwines.mul {x y x' y' : Points k}
    (h : Intertwines k x y) (h' : Intertwines k x' y') :
    Intertwines k (x * x') (y * y') := by
  intro v
  rw [map_mul, Module.End.mul_apply, h', h]
  simp [map_mul]

private theorem Intertwines.inv {x y : Points k} (h : Intertwines k x y) :
    Intertwines k x⁻¹ y⁻¹ := by
  intro v
  have h' := congrArg (pointAction k x⁻¹) (h ((naturalAction k y⁻¹).val v))
  have hx (w : Fock k) : pointAction k x⁻¹ (pointAction k x w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hy : (naturalAction k y).val ((naturalAction k y⁻¹).val v) = v := by
    simp [map_inv]
  rw [hx, hy] at h'
  exact h'.symm

private theorem Intertwines.unique {x y z : Points k}
    (h : Intertwines k x y) (h' : Intertwines k x z) : y = z := by
  apply naturalAction_injective k
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply embedding_injective k
  exact (h v).symm.trans (h' v)

/-- An actual Clifford representation, on an injectively embedded copy of the natural
space, makes the root assignment well-defined on the entire Spin point group. -/
private theorem exists_pinned_pointHom_of_intertwining
    (hp : ∀ i t, Intertwines k (positiveSimplePoint k i t)
      (positiveSimplePoint k (typeD4DiagramPermutation i) t))
    (hn : ∀ i t, Intertwines k (negativeSimplePoint k i t)
      (negativeSimplePoint k (typeD4DiagramPermutation i) t)) :
    ∃ f : Points k →* Points k, IsPinned k f := by
  let H : Subgroup (Points k) :=
    { carrier := {x | ∃ y, Intertwines k x y}
      one_mem' := ⟨1, intertwines_one k⟩
      mul_mem' := by
        rintro x x' ⟨y, hy⟩ ⟨y', hy'⟩
        exact ⟨y * y', hy.mul k hy'⟩
      inv_mem' := by
        rintro x ⟨y, hy⟩
        exact ⟨y⁻¹, hy.inv k⟩ }
  have hH : H = ⊤ := by
    apply top_unique
    rw [← simplePointSubgroup_eq_top k]
    apply (Subgroup.closure_le H).mpr
    rintro x (⟨⟨i,t⟩, rfl⟩ | ⟨⟨i,t⟩, rfl⟩)
    · exact ⟨_, hp i t⟩
    · exact ⟨_, hn i t⟩
  have hex (x : Points k) : ∃ y, Intertwines k x y := by
    change x ∈ H
    rw [hH]
    trivial
  choose f hf using hex
  let F : Points k →* Points k :=
    { toFun := f
      map_one' := (hf 1).unique k (intertwines_one k)
      map_mul' := fun x y => (hf (x * y)).unique k ((hf x).mul k (hf y)) }
  refine ⟨F, ?_, ?_⟩
  · intro i t
    exact (hf _).unique k (hp i t)
  · intro i t
    exact (hf _).unique k (hn i t)

end Triality.SimplyConnected.Diagram.HalfSpin

namespace Triality.SimplyConnected.Diagram
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Pinning
variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The pinned arm cycle exists on the actual Spin point group over every
algebraically closed field of characteristic two. -/
theorem exists_pinned_pointHom : ∃ f : Points k →* Points k, IsPinned k f := by
  apply HalfSpin.exists_pinned_pointHom_of_intertwining k
  · intro i t v
    rw [naturalAction_rootPoint]
    exact HalfSpin.positive_intertwines k i t v
  · intro i t v
    rw [naturalAction_rootPoint]
    exact HalfSpin.negative_intertwines k i t v

/-- A chosen realization of the pinned D4 arm cycle on the actual Spin points. -/
def pinnedPointHom : Points k →* Points k := (exists_pinned_pointHom k).choose

/-- Both signed simple root families are sent to the permuted family with the
same parameter. -/
theorem pinnedPointHom_isPinned : IsPinned k (pinnedPointHom k) :=
  (exists_pinned_pointHom k).choose_spec

end Triality.SimplyConnected.Diagram
