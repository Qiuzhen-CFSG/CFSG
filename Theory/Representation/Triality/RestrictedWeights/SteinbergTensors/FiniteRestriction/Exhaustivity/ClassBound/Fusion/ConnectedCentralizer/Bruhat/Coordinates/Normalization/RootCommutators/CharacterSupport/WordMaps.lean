module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.Closure

/-!
Affine parameter maps for finite products of root-pair commutators and their
inverses. Conjugation scales each coordinate by one of the two actual root
characters. Erasing all coordinates from either family gives the identity.
Subgroup closure induction gives such a map through every abstract commutator
subgroup element. Polynomial zero loci then pass detection from its Zariski
closure to one of these maps. No assertion that the commutator subgroup is
already closed, and no root-coordinate decomposition, is needed.

Source: the geometric support argument for GLS3, 1.12.1(b) and 1.12.7(b).
-/

open Theory.AlgebraicGroup
open scoped commutatorElement
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
namespace ConnectedCentralizer.Bruhat.Coordinates.Normalization
noncomputable section
universe u
variable {k : Type u} [Field k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

private def affineReindex {sigma tau : Type u} [Finite sigma] [Finite tau]
    (f : tau → sigma) :
    Variety.Morphism (affineSpaceVariety k sigma) (affineSpaceVariety k tau) where
  toFun z := affineSpacePoint (fun i => z.val (f i))
  regular := by
    intro i
    refine ⟨MvPolynomial.X (f i), ?_⟩
    intro z
    change z.val (f i) = evalPolynomial z.val (MvPolynomial.X (f i))
    rw [evalPolynomial_X]

private def affineCoordinate {sigma : Type u} [Finite sigma] (i : sigma) :
    Variety.Morphism (affineSpaceVariety k sigma) (KPlus k) where
  toFun z := kPlusPoint (z.val i)
  regular := by
    intro j
    refine ⟨MvPolynomial.X i, ?_⟩
    intro z
    rw [show j = PUnit.unit by rfl]
    change z.val i = evalPolynomial z.val (MvPolynomial.X i)
    rw [evalPolynomial_X]

private def parameterCurve (S : Geometry K) (a : S.roots.Root) :
    Variety.Morphism (KPlus k) K :=
  (S.roots.rootSubgroup a).inclusion.toVariety.comp (S.rootParameter a).hom.toVariety

private lemma parameterCurve_zero (S : Geometry K) (a : S.roots.Root) :
    (parameterCurve S a).toFun (kPlusPoint 0) = 1 := by
  have hzero : kPlusPoint (0 : k) = 1 := by
    rfl
  change (S.roots.rootSubgroup a).inclusion.onPoints
    ((S.rootParameter a).hom.onPoints (kPlusPoint 0)) = 1
  rw [hzero]
  simp

private lemma parameterCurve_scale (S : Geometry K) (a : S.roots.Root)
    (z : k) (s : Variety.Point S.torus.carrierVariety) :
    (parameterCurve S a).toFun
        (kPlusPoint ((S.roots.rootWeight a).pointCharacter s * z)) =
      (S.torus.includePoint s)⁻¹ * (parameterCurve S a).toFun (kPlusPoint z) *
        S.torus.includePoint s :=
  ((S.realized.2.2.1 a).2 (S.rootParameter a) z s).symm

private lemma exists_parameterCurve (S : Geometry K) (a : S.roots.Root)
    (g : Variety.Point K) (hg : g ∈ S.roots.rootSubgroup a) :
    ∃ z : k, (parameterCurve S a).toFun (kPlusPoint z) = g := by
  let X := S.roots.rootSubgroup a
  let x := S.rootParameter a
  let y : Variety.Point X.carrierVariety := X.pointEquiv.symm ⟨g, hg⟩
  let p : Variety.Point (KPlus k) := x.inv.onPoints y
  let z := Multiplicative.toAdd (additiveGroupPointEquiv k p)
  have hzp : kPlusPoint z = p := by
    apply (additiveGroupPointEquiv k).injective
    simp [kPlusPoint, z]
  refine ⟨z, ?_⟩
  change X.includePoint (x.hom.onPoints (kPlusPoint z)) = g
  rw [hzp, x.inv_hom_id]
  change (X.pointEquiv y).val = g
  simp [y]

private structure MixedWordMap (S : Geometry K) (a b : S.roots.Root) where
  Coord : Type u
  [finiteCoord : Finite Coord]
  side : Coord → Bool
  map : Variety.Morphism (affineSpaceVariety k Coord) K
  scale : ∀ (s : Variety.Point S.torus.carrierVariety) (z : Coord → k),
    map.toFun (affineSpacePoint (fun i =>
      (if side i then S.roots.rootWeight a else S.roots.rootWeight b).pointCharacter s * z i)) =
    (S.torus.includePoint s)⁻¹ * map.toFun (affineSpacePoint z) * S.torus.includePoint s
  erase : ∀ (e : Bool) (z : Coord → k),
    map.toFun (affineSpacePoint (fun i => if side i = e then 0 else z i)) = 1

attribute [instance] MixedWordMap.finiteCoord

private def oneWordMap (S : Geometry K) (a b : S.roots.Root) : MixedWordMap S a b where
  Coord := ULift.{u} PUnit
  side := fun _ => true
  map := Variety.Morphism.const _ K 1
  scale := by intros; simp [Variety.Morphism.const]
  erase := by intros; rfl

private def invWordMap {S : Geometry K} {a b : S.roots.Root}
    (f : MixedWordMap S a b) : MixedWordMap S a b where
  Coord := f.Coord
  side := f.side
  map := (Theory.AlgebraicGroup.invMorphism K).comp f.map
  scale := by
    intro s z
    change (f.map.toFun _)⁻¹ = _
    rw [f.scale]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
    rfl
  erase := by
    intro e z
    change (f.map.toFun _)⁻¹ = 1
    rw [f.erase, inv_one]

private def mulWordMap {S : Geometry K} {a b : S.roots.Root}
    (f g : MixedWordMap S a b) : MixedWordMap S a b where
  Coord := f.Coord ⊕ g.Coord
  side := Sum.elim f.side g.side
  map := (Theory.AlgebraicGroup.mulMorphism K).comp
    ((f.map.comp (affineReindex Sum.inl)).pair
      (g.map.comp (affineReindex Sum.inr)))
  scale := by
    intro s z
    change f.map.toFun (affineSpacePoint (fun i =>
        (if f.side i then S.roots.rootWeight a else S.roots.rootWeight b).pointCharacter s * z (.inl i))) *
      g.map.toFun (affineSpacePoint (fun i =>
        (if g.side i then S.roots.rootWeight a else S.roots.rootWeight b).pointCharacter s * z (.inr i))) = _
    rw [f.scale, g.scale]
    change ((S.torus.includePoint s)⁻¹ * f.map.toFun (affineSpacePoint (fun i => z (.inl i))) * S.torus.includePoint s) *
      ((S.torus.includePoint s)⁻¹ * g.map.toFun (affineSpacePoint (fun i => z (.inr i))) * S.torus.includePoint s) =
      (S.torus.includePoint s)⁻¹ *
        (f.map.toFun (affineSpacePoint (fun i => z (.inl i))) *
          g.map.toFun (affineSpacePoint (fun i => z (.inr i)))) * S.torus.includePoint s
    simp only [mul_assoc, mul_inv_cancel_left]
  erase := by
    intro e z
    change f.map.toFun (affineSpacePoint (fun i => if f.side i = e then 0 else z (.inl i))) *
      g.map.toFun (affineSpacePoint (fun i => if g.side i = e then 0 else z (.inr i))) = 1
    rw [f.erase, g.erase, one_mul]

private def generatorWordMap (S : Geometry K) (a b : S.roots.Root) : MixedWordMap S a b where
  Coord := ULift.{u} Bool
  side := ULift.down
  map := (Theory.AlgebraicGroup.commutatorMorphism K).comp
    (((parameterCurve S a).comp (affineCoordinate (ULift.up true))).pair
      ((parameterCurve S b).comp (affineCoordinate (ULift.up false))))
  scale := by
    intro s z
    change ⁅(parameterCurve S a).toFun
        (kPlusPoint ((S.roots.rootWeight a).pointCharacter s * z (ULift.up true))),
      (parameterCurve S b).toFun
        (kPlusPoint ((S.roots.rootWeight b).pointCharacter s * z (ULift.up false)))⁆ = _
    rw [parameterCurve_scale, parameterCurve_scale]
    change _ = (S.torus.includePoint s)⁻¹ *
      ⁅(parameterCurve S a).toFun (kPlusPoint (z (ULift.up true))),
        (parameterCurve S b).toFun (kPlusPoint (z (ULift.up false)))⁆ * S.torus.includePoint s
    simp only [commutatorElement_def]
    group
  erase := by
    intro e z
    change ⁅(parameterCurve S a).toFun (kPlusPoint (if true = e then 0 else z (ULift.up true))),
      (parameterCurve S b).toFun (kPlusPoint (if false = e then 0 else z (ULift.up false)))⁆ = 1
    cases e <;> simp [parameterCurve_zero]

private lemma exists_wordMap_of_mem (S : Geometry K) (a b : S.roots.Root)
    (g : Variety.Point K)
    (hg : g ∈ ⁅(S.roots.rootSubgroup a).toSubgroup, (S.roots.rootSubgroup b).toSubgroup⁆) :
    ∃ (f : MixedWordMap S a b) (z : f.Coord → k),
      f.map.toFun (affineSpacePoint z) = g := by
  rw [Subgroup.commutator_def] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      rcases hg with ⟨x, hx, y, hy, rfl⟩
      obtain ⟨v, hv⟩ := exists_parameterCurve S a x hx
      obtain ⟨w, hw⟩ := exists_parameterCurve S b y hy
      refine ⟨generatorWordMap S a b, (fun i => if i.down then v else w), ?_⟩
      change ⁅(parameterCurve S a).toFun (kPlusPoint v),
        (parameterCurve S b).toFun (kPlusPoint w)⁆ = ⁅x, y⁆
      rw [hv, hw]
  | one => exact ⟨oneWordMap S a b, fun _ => 0, rfl⟩
  | mul x y _ _ hx hy =>
      obtain ⟨f, z, hz⟩ := hx
      obtain ⟨g, w, hw⟩ := hy
      refine ⟨mulWordMap f g, Sum.elim z w, ?_⟩
      change f.map.toFun (affineSpacePoint z) * g.map.toFun (affineSpacePoint w) = x * y
      rw [hz, hw]
  | inv x _ hx =>
      obtain ⟨f, z, hz⟩ := hx
      refine ⟨invWordMap f, z, ?_⟩
      change (f.map.toFun (affineSpacePoint z))⁻¹ = x⁻¹
      rw [hz]

omit [CharP k 2] in
private lemma exists_nonzero_on_subgroup_of_nonzero_on_closure
    (H : Subgroup (Variety.Point K)) (F : Variety.PolynomialFunction K)
    (g : Variety.Point K) (hg : g ∈ closure (H : Set (Variety.Point K)))
    (hFg : F g ≠ 0) : ∃ h ∈ H, F h ≠ 0 := by
  by_contra h
  push Not at h
  have hclosed : IsClosed {x : Variety.Point K | F x = 0} := by
    apply Variety.isClosed_iff_isZariskiClosed.mpr
    obtain ⟨P, hP⟩ := F.representedBy
    refine ⟨{P}, ?_⟩
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq]
    rw [hP x]
  exact hFg (closure_minimal h hclosed hg)

/-- A nonzero inverse-conjugation eigenfunction on a root-pair commutator
closure pulls back to a nonzero polynomial of the same character. Erasing
either family of parameters makes that polynomial zero. -/
public theorem exists_mixedCommutatorPolynomial
    (S : Geometry K) (a b : S.roots.Root)
    (c : TorusCharacter S.torus.carrierVariety)
    (F : Variety.PolynomialFunction K) (hFone : F 1 = 0)
    (hFscale : ∀ (s : Variety.Point S.torus.carrierVariety) (g : Variety.Point K),
      F ((S.torus.includePoint s)⁻¹ * g * S.torus.includePoint s) =
        c.pointCharacter s * F g)
    (g : Variety.Point K) (hg : g ∈ closedPairCommutator S a b) (hFg : F g ≠ 0) :
    ∃ (sigma : Type u) (_ : Finite sigma) (side : sigma → Bool) (P : MvPolynomial sigma k),
      (∃ z : sigma → k, MvPolynomial.eval z P ≠ 0) ∧
      (∀ (s : Variety.Point S.torus.carrierVariety) (z : sigma → k),
        MvPolynomial.eval
          (fun i => (if side i then S.roots.rootWeight a else S.roots.rootWeight b).pointCharacter s * z i) P =
            c.pointCharacter s * MvPolynomial.eval z P) ∧
      (∀ (e : Bool) (z : sigma → k),
        MvPolynomial.eval (fun i => if side i = e then 0 else z i) P = 0) := by
  obtain ⟨h, hh, hFh⟩ := exists_nonzero_on_subgroup_of_nonzero_on_closure
    _ F g hg hFg
  obtain ⟨f, z, hz⟩ := exists_wordMap_of_mem S a b h hh
  let q := Variety.PolynomialFunction.pullback f.map F
  obtain ⟨P, hP⟩ := q.representedBy
  have heval (w : f.Coord → k) :
      MvPolynomial.eval w P = F (f.map.toFun (affineSpacePoint w)) :=
    (hP (affineSpacePoint w)).symm
  refine ⟨f.Coord, inferInstance, f.side, P, ⟨z, ?_⟩, ?_, ?_⟩
  · rwa [heval, hz]
  · intro s w
    rw [heval, f.scale, hFscale, heval]
  · intro e w
    rw [heval, f.erase, hFone]

end
end ConnectedCentralizer.Bruhat.Coordinates.Normalization
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
