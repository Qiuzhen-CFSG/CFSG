module

public import Theory.AlgebraicGroup.Irreducible.Product

/-!
# Regular lifts through finite-kernel morphisms

A normalized regular lift of a homomorphism from a connected algebraic group
is itself a homomorphism. Its multiplicative defect has connected image in
the finite kernel, hence is identically one. This is the same connectedness
argument used for central kernels in GLS3, Proposition 1.10.3(a), and needs
neither separability nor a regular inverse to the finite-kernel morphism.
-/

public section
universe u
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k]

/-- Multiplicativity descends to a normalized regular lift through a morphism
with finite point kernel. -/
theorem Morphism.regularLift_map_mul
    {X H G : Variety k} [AlgebraicGroup X] [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hfinite : Finite φ.kernel)
    (hX : Variety.IsConnected X) (f : Variety.Morphism X H)
    (hf : f.toFun 1 = 1) (g : Morphism X G)
    (hcomp : ∀ x, φ.onPoints (f.toFun x) = g.onPoints x) :
    ∀ x y, f.toFun (x * y) = f.toFun x * f.toFun y := by
  let fx := f.comp (Variety.Morphism.fst X X)
  let fy := f.comp (Variety.Morphism.snd X X)
  let fxy := f.comp (mulMorphism X)
  let defect : Variety.Morphism (Variety.prod X X) H :=
    (mulMorphism H).comp
      (((mulMorphism H).comp (fxy.pair ((invMorphism H).comp fy))).pair
        ((invMorphism H).comp fx))
  have hdefect (x y : Variety.Point X) :
      defect.toFun ((Variety.prodPointEquiv X X).symm (x, y)) =
        f.toFun (x * y) * (f.toFun y)⁻¹ * (f.toFun x)⁻¹ := rfl
  have hrange : Set.range defect.toFun ⊆ (φ.kernel : Set (Variety.Point H)) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨⟨x, y⟩, rfl⟩ := (Variety.prodPointEquiv X X).symm.surjective z
    change φ.onPoints (defect.toFun _) = 1
    rw [hdefect, MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv,
      MonoidHom.map_inv, hcomp, hcomp, hcomp, MonoidHom.map_mul]
    simp [mul_assoc]
  let : Finite φ.kernel := hfinite
  have hprod : Variety.IsConnected (Variety.prod X X) := by
    have hi := prodSet_irreducible_of_irreducible
      (connectedAlgebraicGroup_irreducible X hX)
      (connectedAlgebraicGroup_irreducible X hX)
    have heq : Variety.prodSet (Set.univ : Set (Variety.Point X)) Set.univ =
        (Set.univ : Set (Variety.Point (Variety.prod X X))) := by
      ext z
      simp [Variety.prodSet]
    rw [heq] at hi
    exact hi.isConnected
  have hs := connected_finite_morphism_range_subsingleton defect hprod
    ((Set.toFinite (φ.kernel : Set (Variety.Point H))).subset hrange)
  intro x y
  have heq := hs
    (Set.mem_range_self ((Variety.prodPointEquiv X X).symm (x, y)))
    (Set.mem_range_self ((Variety.prodPointEquiv X X).symm (1, 1)))
  rw [hdefect, hdefect, one_mul, hf, inv_one, mul_one] at heq
  have heq' : f.toFun (x * y) * (f.toFun x * f.toFun y)⁻¹ = 1 := by
    simpa only [mul_inv_rev, ← mul_assoc, mul_one] using heq
  exact mul_inv_eq_one.mp heq'

/-- A normalized regular lift is an algebraic-group morphism with the same
point map. -/
def Morphism.regularLift
    {X H G : Variety k} [AlgebraicGroup X] [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hfinite : Finite φ.kernel)
    (hX : Variety.IsConnected X) (f : Variety.Morphism X H)
    (hf : f.toFun 1 = 1) (g : Morphism X G)
    (hcomp : ∀ x, φ.onPoints (f.toFun x) = g.onPoints x) : Morphism X H where
  toVariety := f
  map_one := hf
  map_mul := φ.regularLift_map_mul hfinite hX f hf g hcomp

@[simp] theorem Morphism.regularLift_apply
    {X H G : Variety k} [AlgebraicGroup X] [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hfinite : Finite φ.kernel)
    (hX : Variety.IsConnected X) (f : Variety.Morphism X H)
    (hf : f.toFun 1 = 1) (g : Morphism X G)
    (hcomp : ∀ x, φ.onPoints (f.toFun x) = g.onPoints x)
    (x : Variety.Point X) :
    (φ.regularLift hfinite hX f hf g hcomp).onPoints x = f.toFun x := by
  unfold Morphism.regularLift
  rfl

end Theory.AlgebraicGroup
