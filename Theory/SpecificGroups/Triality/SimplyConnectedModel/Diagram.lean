module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.Torus
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.PointRealization
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.Regularity

/-!
# The regular pinned order-three Spin diagram automorphism

Over every algebraically closed field of characteristic two, `pinnedIso`
realizes the D4 arm cycle `0 → 2 → 3 → 0`, fixing vertex `1`, on the actual
closed Clifford Spin variety. The half-spin representation constructs its
point homomorphism. Regularity follows by closed-graph coordinate descent,
using the proved spanning of the Spin tangent by torus and root tangents.

A regular endomorphism with the prescribed signed-simple-root action has cube
one by the concrete generation theorem. Its square is therefore a regular
inverse; the moved element `x₀(1)` gives exact order three. Its restriction to
the actual coroot torus is the regular coordinate permutation already built
in `Diagram.Torus`, fixing the character pullback orientation.

`exists_pinned_iso` discharges the point-map and regularity inputs of the
conditional assembly endpoints retained below. The exported `pinnedAut` is
its point-group automorphism. Neither simplicity nor universality is an
additional hypothesis for this concrete construction. No regular inverse to
the Spin-to-Omega point bijection or unresolved general Theorem 1.15.2 is used.

Source: GLS3, Theorem 1.15.2(a,b) (`refs/KGroup/GLS3/Chapter1.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Diagram
open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Pinning Pinning.CorootTorus
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- A regular pinned forward map has its square as regular inverse. -/
def isoOfPinnedMorphism (f : AlgebraicGroup.Morphism (groupVariety k) (groupVariety k))
    (hf : IsPinned k f.onPoints) : AlgebraicGroup.Iso (groupVariety k) (groupVariety k) where
  hom := f
  inv := f.comp f
  hom_inv_id := hf.cube k
  inv_hom_id := hf.cube k

/-- The resulting point-group automorphism has exact order three. -/
theorem isoOfPinnedMorphism_orderOf
    (f : AlgebraicGroup.Morphism (groupVariety k) (groupVariety k))
    (hf : IsPinned k f.onPoints) :
    orderOf (isoOfPinnedMorphism k f hf).toMulEquiv = 3 := hf.orderOf_pointAut k

/-- The cube is the identity as a regular algebraic-group morphism. -/
theorem isoOfPinnedMorphism_cube
    (f : AlgebraicGroup.Morphism (groupVariety k) (groupVariety k))
    (hf : IsPinned k f.onPoints) :
    f.comp (f.comp f) = AlgebraicGroup.Morphism.id (groupVariety k) := by
  apply AlgebraicGroup.Morphism.ext
  funext x
  exact hf.cube k x

/-- There is at most one regular morphism with this pinned action. -/
theorem pinnedMorphism_unique
    (f g : AlgebraicGroup.Morphism (groupVariety k) (groupVariety k))
    (hf : IsPinned k f.onPoints) (hg : IsPinned k g.onPoints) : f = g := by
  have h := hom_ext k (f := f.onPoints) (g := g.onPoints)
    (fun i t => (hf.1 i t).trans (hg.1 i t).symm)
    (fun i t => (hf.2 i t).trans (hg.2 i t).symm)
  apply AlgebraicGroup.Morphism.ext
  funext x
  exact DFunLike.congr_fun h x

/-- The diagram map restricts regularly to the constructed coroot torus isomorphism. -/
theorem isoOfPinnedMorphism_torus
    (f : AlgebraicGroup.Morphism (groupVariety k) (groupVariety k))
    (hf : IsPinned k f.onPoints) :
    f.comp (closedSubgroup k).inclusion =
      (closedSubgroup k).inclusion.comp (torusIso k).hom := by
  apply AlgebraicGroup.Morphism.ext
  funext t
  exact hf.torus_inclusion k t

/-- Coordinate reconstruction followed by the proved order and torus assembly.
The point homomorphism and its regular coordinate pullback are explicit inputs. -/
theorem exists_iso_of_pinned_coordinatePullback
    (f : Points k →* Points k) (hf : IsPinned k f)
    (pull : Variety.PolynomialFunction (groupVariety k) →ₐ[k]
      Variety.PolynomialFunction (groupVariety k))
    (hpull : ∀ a x, pull a x = a (f x)) :
    ∃ e : AlgebraicGroup.Iso (groupVariety k) (groupVariety k),
      e.hom.onPoints = f ∧ orderOf e.toMulEquiv = 3 ∧
      e.hom.comp (closedSubgroup k).inclusion =
        (closedSubgroup k).inclusion.comp (torusIso k).hom := by
  obtain ⟨φ, hφ⟩ := AlgebraicGroup.Morphism.exists_of_pointHom_of_polynomialFunctionAlgHom
    f pull hpull
  have hpin : IsPinned k φ.onPoints := hφ.symm ▸ hf
  exact ⟨isoOfPinnedMorphism k φ hpin, hφ, isoOfPinnedMorphism_orderOf k φ hpin,
    isoOfPinnedMorphism_torus k φ hpin⟩

/-- The regular realization of the constructed half-spin point homomorphism. -/
def pinnedMorphism : AlgebraicGroup.Morphism (groupVariety k) (groupVariety k) :=
  ((pinnedPointHom_isPinned k).exists_morphism k).choose

/-- Coordinate descent realizes exactly the constructed point map. -/
theorem pinnedMorphism_onPoints : (pinnedMorphism k).onPoints = pinnedPointHom k :=
  ((pinnedPointHom_isPinned k).exists_morphism k).choose_spec

/-- The descended morphism preserves both signed simple-root parameters. -/
theorem pinnedMorphism_isPinned : IsPinned k (pinnedMorphism k).onPoints := by
  rw [pinnedMorphism_onPoints]
  exact pinnedPointHom_isPinned k

/-- The pinned triality on the actual Clifford Spin variety, regular in both
directions. Its inverse is the square of the descended forward morphism. -/
def pinnedIso : AlgebraicGroup.Iso (groupVariety k) (groupVariety k) :=
  isoOfPinnedMorphism k (pinnedMorphism k) (pinnedMorphism_isPinned k)

/-- The point-group automorphism induced by the regular pinned triality. -/
def pinnedAut : MulAut (Points k) := (pinnedIso k).toMulEquiv

/-- Both signs of the pinning use exactly the cycle `0 → 2 → 3 → 0`. -/
theorem pinnedIso_isPinned : IsPinned k (pinnedIso k).hom.onPoints :=
  pinnedMorphism_isPinned k

/-- The exported point automorphism has the same signed pinned action. -/
theorem pinnedAut_isPinned : IsPinned k (pinnedAut k).toMonoidHom :=
  pinnedIso_isPinned k

/-- Triality sends a positive simple-root element to the permuted root with
unchanged parameter. -/
@[simp] theorem pinnedAut_positiveSimple (i : Fin 4) (t : k) :
    pinnedAut k (positiveSimplePoint k i t) =
      positiveSimplePoint k (typeD4DiagramPermutation i) t :=
  (pinnedAut_isPinned k).1 i t

/-- The negative simple roots have the identical parameter convention. -/
@[simp] theorem pinnedAut_negativeSimple (i : Fin 4) (t : k) :
    pinnedAut k (negativeSimplePoint k i t) =
      negativeSimplePoint k (typeD4DiagramPermutation i) t :=
  (pinnedAut_isPinned k).2 i t

/-- The inverse is explicitly a composite of regular morphisms. -/
theorem pinnedIso_inv : (pinnedIso k).inv = (pinnedIso k).hom.comp (pinnedIso k).hom := rfl

/-- The cube is the identity as a regular algebraic-group morphism. -/
theorem pinnedIso_cube :
    (pinnedIso k).hom.comp ((pinnedIso k).hom.comp (pinnedIso k).hom) =
      AlgebraicGroup.Morphism.id (groupVariety k) :=
  isoOfPinnedMorphism_cube k (pinnedMorphism k) (pinnedMorphism_isPinned k)

/-- Generation by the signed simple roots proves the pointwise cube identity. -/
theorem pinnedAut_cube (x : Points k) : pinnedAut k (pinnedAut k (pinnedAut k x)) = x :=
  (pinnedAut_isPinned k).cube k x

/-- The period-three identity in the automorphism group. -/
theorem pinnedAut_pow_three : pinnedAut k ^ 3 = 1 := by
  ext x
  exact pinnedAut_cube k x

/-- A concrete pinned root element is moved. -/
theorem pinnedAut_moves_positiveSimple_zero :
    pinnedAut k (positiveSimplePoint k 0 1) ≠ positiveSimplePoint k 0 1 := by
  rw [pinnedAut_positiveSimple]
  exact (positiveSimplePoint_zero_ne_two k).symm

/-- The moved root element makes the order exactly three. -/
theorem pinnedAut_orderOf : orderOf (pinnedAut k) = 3 :=
  isoOfPinnedMorphism_orderOf k (pinnedMorphism k) (pinnedMorphism_isPinned k)

/-- The pinned regular morphism is unique, as in GLS3 1.15.2(a). -/
theorem eq_pinnedMorphism (f : AlgebraicGroup.Morphism (groupVariety k) (groupVariety k))
    (hf : IsPinned k f.onPoints) : f = pinnedMorphism k :=
  pinnedMorphism_unique k f (pinnedMorphism k) hf (pinnedMorphism_isPinned k)

/-- Restriction to the constructed maximal torus is the regular coroot-coordinate
permutation; this identifies the ambient action with `Diagram.Torus`. -/
theorem pinnedIso_torus :
    (pinnedIso k).hom.comp (closedSubgroup k).inclusion =
      (closedSubgroup k).inclusion.comp (torusIso k).hom :=
  isoOfPinnedMorphism_torus k (pinnedMorphism k) (pinnedMorphism_isPinned k)

/-- The inverse restricts to the regular inverse of the same torus permutation. -/
theorem pinnedIso_inv_torus :
    (pinnedIso k).inv.comp (closedSubgroup k).inclusion =
      (closedSubgroup k).inclusion.comp (torusIso k).inv := by
  apply AlgebraicGroup.Morphism.ext
  funext t
  change (pinnedIso k).hom.onPoints
    ((pinnedIso k).hom.onPoints ((closedSubgroup k).includePoint t)) =
      (closedSubgroup k).includePoint ((torusMap k).onPoints ((torusMap k).onPoints t))
  rw [(pinnedIso_isPinned k).torus_inclusion k, (pinnedIso_isPinned k).torus_inclusion k]

/-- Preservation of the actual maximal torus in both directions. -/
theorem pinnedAut_torus_mem_iff (g : Points k) :
    pinnedAut k g ∈ (closedSubgroup k).toSubgroup ↔ g ∈ (closedSubgroup k).toSubgroup :=
  (pinnedAut_isPinned k).torus_mem_iff k g

/-- The ambient regular triality permutes the realized simple-coroot morphisms. -/
theorem pinnedIso_simpleCoroot (i : Fin 4) :
    (pinnedIso k).hom.comp ((closedSubgroup k).inclusion.comp
      ((pinnedRootData k).rootCocharacter (pinnedRootIndex k (simpleRoot i)))) =
    (closedSubgroup k).inclusion.comp ((pinnedRootData k).rootCocharacter
      (pinnedRootIndex k (simpleRoot (typeD4DiagramPermutation i)))) := by
  rw [AlgebraicGroup.Morphism.comp_assoc, pinnedIso_torus,
    ← AlgebraicGroup.Morphism.comp_assoc]
  change (closedSubgroup k).inclusion.comp ((torusMap k).comp _) = _
  rw [torusMap_simpleCoroot]

/-- Pullback of the actual fundamental characters uses the inverse index cycle. -/
theorem fundamentalCharacter_comp (i : Fin 4) :
    (fundamentalCharacter k i).comp (torusIso k).hom =
      fundamentalCharacter k (typeD4DiagramPermutation.symm i) := by
  apply TorusCharacter.pointCharacter_injective
  ext t
  exact fundamentalCharacter_pullback k i t

/-- The literal inverse graph action pulls back integral weights by the inverse
cycle. Together with `pinnedIso_inv_torus`, this fixes the ambient convention. -/
theorem weightEmbedding_inverse_comp (a : Fin 4 → ℤ) :
    (weightEmbedding k a).comp (torusIso k).inv =
      weightEmbedding k (a ∘ typeD4DiagramPermutation.symm) := by
  apply TorusCharacter.pointCharacter_injective
  ext t
  exact (weightEmbedding_inverse_pullback k a t).symm

/-- Existence on the fixed Spin carrier, with every point-realization and
regularity premise discharged. The other theorems above identify its cube,
coroot action, and forward and inverse torus restrictions. -/
theorem exists_pinned_iso :
    ∃ e : AlgebraicGroup.Iso (groupVariety k) (groupVariety k),
      IsPinned k e.hom.onPoints ∧ orderOf e.toMulEquiv = 3 ∧
      e.hom.comp (closedSubgroup k).inclusion =
        (closedSubgroup k).inclusion.comp (torusIso k).hom :=
  ⟨pinnedIso k, pinnedIso_isPinned k, pinnedAut_orderOf k, pinnedIso_torus k⟩

end Triality.SimplyConnected.Diagram
