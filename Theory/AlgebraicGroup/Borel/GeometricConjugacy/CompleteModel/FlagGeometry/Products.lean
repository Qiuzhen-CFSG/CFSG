module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagData
public import Theory.AlgebraicGroup.Variety.AffineGeometricMorphism

/-!
# Complete finite products and their regular actions

Finite products of reduced separated finite-type varieties over an algebraically
closed field are formed recursively from scheme fiber products. Universal
closedness is preserved by base change and composition. Rational points are
identified with tuples, and coordinatewise group actions are induced by actual
product morphisms. The empty product is the complete point scheme `Spec k`.

These are the ambient constructions for the flag variety used in Borel,
*Linear Algebraic Groups*, §11.1.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

@[expose] public noncomputable section

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry

open Variety.Geometric

universe u
variable {k : Type u} [Field k]

/-- The complete point scheme, also used for an empty product. -/
def point : Variety.Geometric k where
  toScheme := Spec (.of k)
  structureMap := 𝟙 _
  finiteType := by infer_instance
  quasiCompact := by infer_instance
  separated := by infer_instance
  reduced := by infer_instance

instance pointUnique : Unique (Point (point (k := k))) where
  default := ⟨𝟙 _, by simp [point]⟩
  uniq x := Subtype.ext (by simpa [point] using x.property)

theorem point_isComplete : IsComplete (point (k := k)) := by
  change UniversallyClosed (𝟙 (Spec (.of k)))
  infer_instance

variable [IsAlgClosed k]

theorem prod_isComplete {X Y : Variety.Geometric k}
    (hX : IsComplete X) (hY : IsComplete Y) : IsComplete (prod X Y) := by
  let : UniversallyClosed X.structureMap := hX
  let : UniversallyClosed Y.structureMap := hY
  change UniversallyClosed (pullback.fst X.structureMap Y.structureMap ≫ X.structureMap)
  infer_instance

/-- Finite products, including the empty product as `Spec k`. -/
def finProduct : (n : ℕ) → (Fin n → Variety.Geometric k) → Variety.Geometric k
  | 0, _ => point
  | n + 1, X => prod (X 0) (finProduct n (fun i => X i.succ))

/-- The rational points of a finite product are tuples of rational points. -/
def finProductPointEquiv : (n : ℕ) → (X : Fin n → Variety.Geometric k) →
    Point (finProduct n X) ≃ ((i : Fin n) → Point (X i))
  | 0, _ => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => (default : Point (point (k := k)))
      left_inv := fun x => @Subsingleton.elim (Point (point (k := k))) inferInstance _ x
      right_inv := fun _ => funext (fun i => Fin.elim0 i) }
  | n + 1, X =>
    (prodPointEquiv (X 0) (finProduct n (fun i => X i.succ))).trans
      (((Equiv.refl (Point (X 0))).prodCongr
        (finProductPointEquiv n (fun i => X i.succ))).trans
          (Fin.consEquiv (fun i => Point (X i))))

theorem finProduct_isComplete (n : ℕ) (X : Fin n → Variety.Geometric k)
    (hX : ∀ i, IsComplete (X i)) : IsComplete (finProduct n X) := by
  induction n with
  | zero => exact point_isComplete
  | succ n ih => exact prod_isComplete (hX 0) (ih _ (fun i => hX i.succ))

variable {G : Variety k} [AlgebraicGroup G]

/-- Every group acts regularly on the point scheme. -/
def pointAction : MorphicAction G (point (k := k)) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  actionMorphism := snd _ _
  actionMorphism_apply _ _ := snd_prodPoint _ _

/-- The product of regular actions, induced by a genuine product morphism. -/
def prodAction {X Y : Variety.Geometric k}
    (A : MorphicAction G X) (B : MorphicAction G Y) : MorphicAction G (prod X Y) where
  smul g x := prodPoint (A.toMulAction.smul g (fst X Y x))
    (B.toMulAction.smul g (snd X Y x))
  one_smul x := by
    change prodPoint (A.toMulAction.smul 1 (fst X Y x))
      (B.toMulAction.smul 1 (snd X Y x)) = x
    exact (congrArg₂ prodPoint (@one_smul _ _ _ A.toMulAction (fst X Y x))
      (@one_smul _ _ _ B.toMulAction (snd X Y x))).trans
        ((prodPointEquiv X Y).symm_apply_apply x)
  mul_smul g h x := by
    change prodPoint (A.toMulAction.smul (g * h) (fst X Y x))
      (B.toMulAction.smul (g * h) (snd X Y x)) =
      prodPoint (A.toMulAction.smul g (fst X Y (prodPoint _ _)))
        (B.toMulAction.smul g (snd X Y (prodPoint _ _)))
    rw [fst_prodPoint, snd_prodPoint]
    exact congrArg₂ prodPoint
      (@mul_smul _ _ _ A.toMulAction.toSemigroupAction g h (fst X Y x))
      (@mul_smul _ _ _ B.toMulAction.toSemigroupAction g h (snd X Y x))
  actionMorphism := Variety.Geometric.Morphism.pair
    (Variety.Geometric.Morphism.comp
      (Variety.Geometric.Morphism.pair (fst (ofAffine G) (prod X Y))
        (Variety.Geometric.Morphism.comp (snd (ofAffine G) (prod X Y)) (fst X Y)))
      A.actionMorphism)
    (Variety.Geometric.Morphism.comp
      (Variety.Geometric.Morphism.pair (fst (ofAffine G) (prod X Y))
        (Variety.Geometric.Morphism.comp (snd (ofAffine G) (prod X Y)) (snd X Y)))
      B.actionMorphism)
  actionMorphism_apply g x := by
    erw [Variety.Geometric.Morphism.pair_apply]
    apply congrArg₂ prodPoint
    · erw [Variety.Geometric.Morphism.comp_apply_point,
        Variety.Geometric.Morphism.pair_apply, fst_prodPoint,
        Variety.Geometric.Morphism.comp_apply_point, snd_prodPoint]
      exact A.actionMorphism_apply g (fst X Y x)
    · erw [Variety.Geometric.Morphism.comp_apply_point,
        Variety.Geometric.Morphism.pair_apply, fst_prodPoint,
        Variety.Geometric.Morphism.comp_apply_point, snd_prodPoint]
      exact B.actionMorphism_apply g (snd X Y x)

/-- Coordinatewise regular action on any finite product. -/
def finProductAction : (n : ℕ) → (X : Fin n → Variety.Geometric k) →
    ((i : Fin n) → MorphicAction G (X i)) → MorphicAction G (finProduct n X)
  | 0, _, _ => pointAction
  | n + 1, X, A => prodAction (A 0)
      (finProductAction n (fun i => X i.succ) (fun i => A i.succ))

theorem finProductAction_equivariant (n : ℕ) (X : Fin n → Variety.Geometric k)
    (A : (i : Fin n) → MorphicAction G (X i))
    (g : Variety.Point G) (x : Point (finProduct n X)) (i : Fin n) :
    finProductPointEquiv n X ((finProductAction n X A).toMulAction.smul g x) i =
      (A i).toMulAction.smul g (finProductPointEquiv n X x i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change fst _ _ (prodPoint _ _) = _
      exact fst_prodPoint _ _
    · change finProductPointEquiv n (fun i => X i.succ)
          (snd _ _ (prodPoint _ _)) j = _
      rw [snd_prodPoint]
      exact ih _ _ _ j

end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry
