module
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.AffineFormula
public import Mathlib.Topology.LocalAtTarget

/-!
# A non-affine fibre dimension formula for homogeneous varieties

For a surjection between geometric varieties homogeneous on closed points,
constant dimension `d` of all nonempty open pieces of rational scheme fibres
implies `dim V = dim W + d`. Choose an integral affine target chart and lift its
generic point to the source. Closed-point homogeneity supplies an integral
affine source neighbourhood inside the preimage of that chart; the restricted
morphism is dominant. Fibres of this restriction embed openly into the original
fibres, so `AffineFormula` applies. Homogeneity identifies both chart dimensions
with the dimensions of the whole varieties.

This argument includes disconnected sources and targets. It makes no
separability assumption and retains scheme fibres throughout. Source: Borel,
*Linear Algebraic Groups*, the orbit dimension argument in §11.1,
`refs/KGroup/Bor1/Chapter4.tex`.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Topology
universe u
namespace Theory.AlgebraicGroup.Variety.Geometric.MinimalOrbit

private theorem exists_openEmbedding_fiber
    {V W V' W' : Scheme.{u}} (f : V ⟶ W) (f' : V' ⟶ W')
    (i : V' ⟶ V) (j : W' ⟶ W)
    (hi : IsOpenEmbedding i) (hj : Function.Injective j)
    (hcomm : f' ≫ j = i ≫ f) (y : W') :
    ∃ g : f'.fiber y → f.fiber (j y), IsOpenEmbedding g := by
  let S : Set V := f ⁻¹' {j y}
  have heq : i ⁻¹' S = f' ⁻¹' {y} := by
    ext v
    change f (i v) = j y ↔ f' v = y
    rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]
    exact hj.eq_iff
  let e : f'.fiber y ≃ₜ i ⁻¹' S :=
    (f'.fiberHomeo y).trans (Homeomorph.setCongr heq.symm)
  let g := (f.fiberHomeo (j y)).symm ∘ (S.restrictPreimage i) ∘ e
  exact ⟨g, (f.fiberHomeo (j y)).symm.isOpenEmbedding.comp
    ((hi.restrictPreimage S).comp e.isOpenEmbedding)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The fibre dimension formula for surjections between closed-point-homogeneous varieties. -/
public theorem dimension_eq_add_of_homogeneous_fibers
    {k : Type u} [Field k] [IsAlgClosed k]
    {V W : Geometric k} [Nonempty V.toScheme]
    (f : Morphism V W) (hsurj : Function.Surjective f.hom)
    (hV : ∀ a ∈ closedPoints V.toScheme, ∀ b ∈ closedPoints V.toScheme,
      ∃ e : V.toScheme ≃ₜ V.toScheme, e a = b)
    (hW : ∀ a ∈ closedPoints W.toScheme, ∀ b ∈ closedPoints W.toScheme,
      ∃ e : W.toScheme ≃ₜ W.toScheme, e a = b)
    (d : ℕ)
    (hfiber : ∀ y : Point W,
      ∀ U : (f.hom.fiber (y.1 (IsLocalRing.closedPoint k))).Opens,
        (U : Set (f.hom.fiber (y.1 (IsLocalRing.closedPoint k)))).Nonempty →
          topologicalKrullDim U = (d : WithBot ℕ∞)) :
    dimension V = dimension W + (d : WithBot ℕ∞) := by
  classical
  let w := f.hom (Classical.choice (inferInstance : Nonempty V.toScheme))
  obtain ⟨O, hwO, hOi⟩ := W.exists_irreducible_open_nhds_of_closedPoint_transitive hW w
  obtain ⟨_, ⟨T, hT, rfl⟩, hwT, hTO⟩ :=
    W.toScheme.isBasis_affineOpens.exists_subset_of_mem_open hwO O.2
  have hTi : _root_.IsIrreducible (T : Set W.toScheme) :=
    ⟨⟨w, hwT⟩, hOi.2.open_subset T.2 hTO⟩
  let TW := openSubvariety W T
  let : IrreducibleSpace TW.toGeometric.toScheme := Subtype.irreducibleSpace hTi
  let : IsAffine TW.toGeometric.toScheme := hT
  let t := genericPoint TW.toGeometric.toScheme
  obtain ⟨v, hv⟩ := hsurj (TW.inclusion.hom t)
  have hvT : f.hom v ∈ T := by
    rw [hv]
    exact t.2
  obtain ⟨R, hvR, hRi⟩ := V.exists_irreducible_open_nhds_of_closedPoint_transitive hV v
  obtain ⟨_, ⟨U, hU, rfl⟩, hvU, hUS⟩ :=
    V.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
      (show v ∈ (R : Set V.toScheme) ∩ f.hom ⁻¹' T from ⟨hvR, hvT⟩)
      (R.2.inter (T.2.preimage f.hom.continuous))
  have hUi : _root_.IsIrreducible (U : Set V.toScheme) :=
    ⟨⟨v, hvU⟩, hRi.2.open_subset U.2 (fun a ha => (hUS ha).1)⟩
  have hUT : U ≤ f.hom ⁻¹ᵁ T := fun a ha => (hUS ha).2
  let UV := openSubvariety V U
  let : IrreducibleSpace UV.toGeometric.toScheme := Subtype.irreducibleSpace hUi
  let : IsAffine UV.toGeometric.toScheme := hU
  let fU : Morphism UV.toGeometric W := Morphism.comp UV.inclusion f
  have hfUT : Set.range fU.hom ⊆ T := by
    rintro z ⟨u, rfl⟩
    exact hUT u.2
  let fT : Morphism UV.toGeometric TW.toGeometric := restrictToOpenSubvariety T fU hfUT
  have hcomp : fT.hom ≫ TW.inclusion.hom = UV.inclusion.hom ≫ f.hom :=
    congrArg Morphism.hom (restrictToOpenSubvariety_inclusion T fU hfUT)
  have hgen : fT.hom ⟨v, hvU⟩ = t := by
    apply TW.inclusion.hom.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hcomp]
    exact hv
  let : IsDominant fT.hom := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← genericPoint_closure TW.toGeometric.toScheme]
    apply closure_mono
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact ⟨⟨v, hvU⟩, hgen⟩
  have hdim : dimension UV.toGeometric = dimension TW.toGeometric + (d : WithBot ℕ∞) := by
    apply affine_dimension_eq_add_of_constant_fiber_open_dimension fT d
    intro y S hSne
    obtain ⟨i, hi⟩ := exists_openEmbedding_fiber f.hom fT.hom UV.inclusion.hom TW.inclusion.hom
      UV.inclusion.hom.isOpenEmbedding TW.inclusion.hom.isOpenEmbedding.injective hcomp
      (y.1 (IsLocalRing.closedPoint k))
    let Sy : (f.hom.fiber ((TW.inclusion y).1 (IsLocalRing.closedPoint k))).Opens :=
      ⟨i '' (S : Set _), hi.isOpenMap _ S.2⟩
    have hSy : (Sy : Set (f.hom.fiber
      ((TW.inclusion y).1 (IsLocalRing.closedPoint k)))).Nonempty := hSne.image i
    have heq : topologicalKrullDim S = topologicalKrullDim Sy :=
      (hi.isEmbedding.homeomorphImage
        (S : Set (fT.hom.fiber (y.1 (IsLocalRing.closedPoint k))))).isHomeomorph.topologicalKrullDim_eq
    exact heq.trans (hfiber (TW.inclusion y) Sy hSy)
  have hdU : dimension V = dimension UV.toGeometric :=
    dimension_eq_nonemptyOpen_of_closedPoint_transitive V hV U ⟨v, hvU⟩
  have hdT : dimension W = dimension TW.toGeometric :=
    dimension_eq_nonemptyOpen_of_closedPoint_transitive W hW T ⟨w, hwT⟩
  rw [hdU, hdT]
  exact hdim

end Theory.AlgebraicGroup.Variety.Geometric.MinimalOrbit
