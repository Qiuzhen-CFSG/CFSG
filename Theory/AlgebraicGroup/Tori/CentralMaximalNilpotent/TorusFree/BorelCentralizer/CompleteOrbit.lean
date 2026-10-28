module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.OrbitMap
public import Theory.AlgebraicGroup.Bor1.CompleteNormalOrbitGeometry
public import Theory.AlgebraicGroup.Variety.SmoothIrreducibleNormal
public import Theory.AlgebraicGroup.Variety.BijectiveNormalization

/-!
# Affine orbits controlled by a complete homogeneous space

Suppose a connected affine group acts transitively on a complete variety `X`.
If the stabilizer of `x : X` fixes a point `y` of an affine variety, then the
whole group fixes `y`.

The diagonal orbit of `(x,y)` projects bijectively onto the orbit of `x`.
Both are genuine reduced orbit carriers, with regular inclusions and orbit
maps. The latter orbit is complete and smooth, hence normal. The bijective
normalization theorem transfers completeness to the irreducible diagonal
orbit. Its second projection has connected complete source and affine target,
so it is constant. This needs neither separability nor regular descent of a
set-theoretically invariant map through a quotient.

This supplies the geometric step of Borel, *Linear Algebraic Groups*, §11.4,
`refs/KGroup/Bor1/Chapter4.tex`, using §§10.1(2),(4) and the orbit geometry
from §1.8. The Borel centralizer theorem applies it to conjugation.
-/

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Theory.AlgebraicGroup

namespace Theory.AlgebraicGroup.Variety.Geometric.MorphicAction
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
variable {X Y : Geometric k}

private noncomputable def diagonal (A : MorphicAction G X) (C : MorphicAction G Y) :
    MorphicAction G (prod X Y) where
  smul g p := prodPoint (A.toMulAction.smul g (fst X Y p))
    (C.toMulAction.smul g (snd X Y p))
  one_smul p := by
    change prodPoint (A.toMulAction.smul 1 (fst X Y p))
      (C.toMulAction.smul 1 (snd X Y p)) = p
    exact (congrArg₂ prodPoint (A.toMulAction.one_smul _)
      (C.toMulAction.one_smul _)).trans ((prodPointEquiv X Y).symm_apply_apply p)
  mul_smul g h p := by
    change prodPoint (A.toMulAction.smul (g * h) (fst X Y p))
      (C.toMulAction.smul (g * h) (snd X Y p)) =
      prodPoint (A.toMulAction.smul g (fst X Y (prodPoint
        (A.toMulAction.smul h (fst X Y p)) (C.toMulAction.smul h (snd X Y p)))))
        (C.toMulAction.smul g (snd X Y (prodPoint
          (A.toMulAction.smul h (fst X Y p)) (C.toMulAction.smul h (snd X Y p)))))
    rw [fst_prodPoint, snd_prodPoint]
    exact congrArg₂ prodPoint (A.toMulAction.mul_smul _ _ _)
      (C.toMulAction.mul_smul _ _ _)
  actionMorphism := Morphism.pair
    ((Morphism.pair (fst (ofAffine G) (prod X Y))
      ((snd (ofAffine G) (prod X Y)).comp (fst X Y))).comp A.actionMorphism)
    ((Morphism.pair (fst (ofAffine G) (prod X Y))
      ((snd (ofAffine G) (prod X Y)).comp (snd X Y))).comp C.actionMorphism)
  actionMorphism_apply g p := by
    rw [Morphism.pair_apply]
    change prodPoint
      (A.actionMorphism ((Morphism.pair (fst (ofAffine G) (prod X Y))
        ((snd (ofAffine G) (prod X Y)).comp (fst X Y)))
        (prodPoint ((affinePointEquiv G).symm g) p)))
      (C.actionMorphism ((Morphism.pair (fst (ofAffine G) (prod X Y))
        ((snd (ofAffine G) (prod X Y)).comp (snd X Y)))
        (prodPoint ((affinePointEquiv G).symm g) p))) = _
    rw [Morphism.pair_apply, Morphism.pair_apply]
    rw [fst_prodPoint, Morphism.comp_apply_point, Morphism.comp_apply_point, snd_prodPoint]
    exact congrArg₂ prodPoint (A.actionMorphism_apply g _) (C.actionMorphism_apply g _)

private theorem diagonal_smul (A : MorphicAction G X) (C : MorphicAction G Y)
    (g : Theory.AlgebraicGroup.Variety.Point G) (x : Point X) (y : Point Y) :
    (A.diagonal C).toMulAction.smul g (prodPoint x y) =
      prodPoint (A.toMulAction.smul g x) (C.toMulAction.smul g y) := by
  change prodPoint _ _ = _
  rw [fst_prodPoint, snd_prodPoint]

private theorem inclusion_toOrbit (A : MorphicAction G X) (x : Point X)
    (g : Point (ofAffine G)) :
    (A.orbitSubvariety x).inclusion (A.toOrbitSubvariety x g) =
      A.toMulAction.smul (affinePointEquiv G g) x := by
  have h : (A.orbitSubvariety x).inclusion (A.toOrbitSubvariety x g) =
      A.orbitMorphismAt x g := by
    apply Subtype.ext
    exact (Category.assoc _ _ _).trans
      (congrArg (fun f => g.1 ≫ f) (A.toOrbitSubvariety_comp_inclusion x))
  rw [h]
  simpa using A.orbitMorphismAt_apply x (affinePointEquiv G g)

private theorem inclusion_injective (A : MorphicAction G X) (x : Point X) :
    Function.Injective (A.orbitSubvariety x).inclusion := by
  intro p q hpq
  apply Subtype.ext
  apply (cancel_mono (A.orbitSubvariety x).inclusion.hom).mp
  exact congrArg Subtype.val hpq

private theorem orbit_irreducible (A : MorphicAction G X) (hG : Variety.IsConnected G)
    (x : Point X) : IsIrreducible (A.orbitSubvariety x).toGeometric := by
  letI : IrreducibleSpace (ofAffine G).toScheme :=
    ofAffine_isIrreducible_of_isConnected G hG
  exact (A.toOrbitSubvariety_surjective x).irreducibleSpace
    (A.toOrbitSubvariety x).hom.continuous

private theorem orbit_range_univ (A : MorphicAction G X) (x : Point X)
    (htrans : ∀ y : Point X, ∃ g : Variety.Point G, A.toMulAction.smul g x = y) :
    Set.range (A.orbitSubvariety x).inclusion.hom = Set.univ := by
  apply Set.range_eq_univ.mpr
  apply ((A.orbitSubvariety x).inclusion.bijective_hom_of_bijective_points ?_).2
  refine ⟨A.inclusion_injective x, ?_⟩
  intro y
  obtain ⟨g, rfl⟩ := htrans y
  refine ⟨A.toOrbitSubvariety x ((affinePointEquiv G).symm g), ?_⟩
  rw [inclusion_toOrbit, Equiv.apply_symm_apply]

end Theory.AlgebraicGroup.Variety.Geometric.MorphicAction

namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

private noncomputable def liftClosed
    {V W Z : Geometric k} (i : Morphism Z V) [IsClosedImmersion i.hom]
    (f : Morphism W V) (hf : Set.range f.hom ⊆ Set.range i.hom) : Morphism W Z := by
  let S : Closeds V.toScheme := ⟨Set.range i.hom, i.hom.isClosedEmbedding.isClosed_range⟩
  have hi : i.hom.ker ≤ Scheme.IdealSheafData.vanishingIdeal S :=
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp i.hom.range_subset_ker_support
  have hker : i.hom.ker ≤ f.hom.ker :=
    hi.trans (vanishingIdeal_le_ker_of_isReduced S f.hom hf)
  exact { hom := IsClosedImmersion.lift i.hom f.hom hker
          commutes := by
            rw [← i.commutes, ← Category.assoc, IsClosedImmersion.lift_fac, f.commutes] }

omit [IsAlgClosed k] in
private theorem liftClosed_fac
    {V W Z : Geometric k} (i : Morphism Z V) [IsClosedImmersion i.hom]
    (f : Morphism W V) (hf : Set.range f.hom ⊆ Set.range i.hom) :
    (liftClosed i f hf).comp i = f := by
  apply Morphism.ext
  exact IsClosedImmersion.lift_fac _ _ _

omit [IsAlgClosed k] in
private theorem liftClosed_apply
    {V W Z : Geometric k} (i : Morphism Z V) [IsClosedImmersion i.hom]
    (f : Morphism W V) (hf : Set.range f.hom ⊆ Set.range i.hom) (z : Point W) :
    i (liftClosed i f hf z) = f z := by
  exact congrArg (fun t : Morphism W V => t z) (liftClosed_fac i f hf)

namespace MorphicAction
variable {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
variable {X Y : Geometric k}

private theorem orbit_eq_of_stabilizer_le (A : MorphicAction G X) (C : MorphicAction G Y)
    (x : Point X) (y : Point Y)
    (hfix : ∀ g, A.toMulAction.smul g x = x → C.toMulAction.smul g y = y)
    (g h : Variety.Point G) (heq : A.toMulAction.smul g x = A.toMulAction.smul h x) :
    C.toMulAction.smul g y = C.toMulAction.smul h y := by
  letI := A.toMulAction
  letI := C.toMulAction
  have ha : (g⁻¹ * h) • x = x := by
    change g • x = h • x at heq
    rw [mul_smul, ← heq, inv_smul_smul]
  have hc : (g⁻¹ * h) • y = y := hfix _ ha
  have hc' := congrArg (fun z : Point Y => g • z) hc
  change g • y = h • y
  simpa only [← mul_smul, mul_inv_cancel_left] using hc'.symm

/-- A point of an affine variety fixed by a stabilizer on a complete transitive
space is fixed by the entire connected group. The diagonal orbit supplies the
regular geometric replacement for descent through the homogeneous space. -/
public theorem fixed_on_affine_of_complete_transitive
    (A : MorphicAction G X) {V : Theory.AlgebraicGroup.Variety k}
    (C : MorphicAction G (ofAffine V)) (hG : Variety.IsConnected G)
    (hX : IsComplete X) (x : Point X)
    (htrans : ∀ z : Point X, ∃ g : Variety.Point G, A.toMulAction.smul g x = z)
    (y : Point (ofAffine V))
    (hfix : ∀ g, A.toMulAction.smul g x = x → C.toMulAction.smul g y = y) :
    ∀ g, C.toMulAction.smul g y = y := by
  let R := A.orbitSubvariety x
  have hrange : Set.range R.inclusion.hom = Set.univ := A.orbit_range_univ x htrans
  have hclosed : IsClosed (Set.range (A.orbitMorphismAt x).hom) := by
    rw [← A.orbitSubvariety_range x, hrange]
    exact isClosed_univ
  letI : IsClosedImmersion R.inclusion.hom := A.orbitSubvariety_isClosedImmersion x hclosed
  have hRcomplete : IsComplete R.toGeometric := A.orbitSubvariety_isComplete hX x hclosed
  have hRnormal : IsNormal R.toGeometric :=
    isNormal_of_isIrreducible_of_smooth _ (A.orbit_irreducible hG x)
      (A.orbitSubvariety_smooth x)
  let D := A.diagonal C
  let p := prodPoint x y
  let S := D.orbitSubvariety p
  let f₀ := S.inclusion.comp (fst X (ofAffine V))
  have hf₀ : Set.range f₀.hom ⊆ Set.range R.inclusion.hom := by
    rw [hrange]
    exact Set.subset_univ _
  let f := liftClosed R.inclusion f₀ hf₀
  have hfac (z : Point S.toGeometric) : R.inclusion (f z) = fst X (ofAffine V) (S.inclusion z) := by
    exact liftClosed_apply R.inclusion f₀ hf₀ z
  have hcoord (g : Point (ofAffine G)) :
      S.inclusion (D.toOrbitSubvariety p g) =
        prodPoint (A.toMulAction.smul (affinePointEquiv G g) x)
          (C.toMulAction.smul (affinePointEquiv G g) y) := by
    rw [D.inclusion_toOrbit, diagonal_smul]
  have hfcoord (g : Point (ofAffine G)) :
      R.inclusion (f (D.toOrbitSubvariety p g)) =
        A.toMulAction.smul (affinePointEquiv G g) x := by
    rw [hfac, hcoord, fst_prodPoint]
  have hbij : Function.Bijective f := by
    constructor
    · intro z w hzw
      obtain ⟨g, rfl⟩ := D.toOrbitSubvariety_surjective_points p z
      obtain ⟨h, rfl⟩ := D.toOrbitSubvariety_surjective_points p w
      have ha := congrArg (fun t => R.inclusion t) hzw
      rw [hfcoord, hfcoord] at ha
      apply D.inclusion_injective p
      rw [hcoord, hcoord, ha,
        A.orbit_eq_of_stabilizer_le C x y hfix _ _ ha]
    · intro z
      obtain ⟨g, rfl⟩ := A.toOrbitSubvariety_surjective_points x z
      refine ⟨D.toOrbitSubvariety p g, ?_⟩
      apply A.inclusion_injective x
      rw [hfcoord, inclusion_toOrbit]
  have hSirr : IsIrreducible S.toGeometric := D.orbit_irreducible hG p
  have hScomplete := isComplete_of_bijective_morphism_to_normal_complete
    f hSirr hRnormal (f.bijective_hom_of_bijective_points hbij) hRcomplete
  have hSconn : IsConnected S.toGeometric := by
    letI : IrreducibleSpace S.toGeometric.toScheme := hSirr
    change ConnectedSpace S.toGeometric.toScheme
    exact inferInstance
  have hconstant := morphism_to_affine_constant_of_isConnected_isComplete
    (S.inclusion.comp (snd X (ofAffine V))) hSconn hScomplete
  have hsecond (g : Variety.Point G) :
      (S.inclusion.comp (snd X (ofAffine V)))
        (D.toOrbitSubvariety p ((affinePointEquiv G).symm g)) = C.toMulAction.smul g y := by
    rw [Morphism.comp_apply_point, hcoord, snd_prodPoint, Equiv.apply_symm_apply]
  intro g
  apply (affinePointEquiv V).injective
  calc
    affinePointEquiv V (C.toMulAction.smul g y) =
        affinePointEquiv V ((S.inclusion.comp (snd X (ofAffine V)))
          (D.toOrbitSubvariety p ((affinePointEquiv G).symm g))) :=
      congrArg (affinePointEquiv V) (hsecond g).symm
    _ = affinePointEquiv V ((S.inclusion.comp (snd X (ofAffine V)))
          (D.toOrbitSubvariety p ((affinePointEquiv G).symm 1))) := hconstant _ _
    _ = affinePointEquiv V y :=
      congrArg (affinePointEquiv V) ((hsecond 1).trans (C.toMulAction.one_smul y))

end MorphicAction
end Theory.AlgebraicGroup.Variety.Geometric
