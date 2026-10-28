module

public import Theory.AlgebraicGroup.Tori.Characters.ProperImage
public import Theory.AlgebraicGroup.Tori.Character.Laurent
public import Theory.AlgebraicGroup.Tori.Power

/-!
# Torus point kernels and products of cocharacters

A product of cocharacters covering the image of a finite-kernel map covers
its source torus. A character annihilating a proper product image would have
finite image, contradicting connectedness. Consequently a bijective composite
of such a product with the finite-kernel map forces that map to be injective.
Coordinate-dependent powers of the characteristic are bijective on torus
points, without asserting regularity of their inverses.

This is the torus calculation in the fundamental-coroot criterion of GLS3,
Theorem 1.12.5(b), `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A torus morphism whose image covers the image of a finite-kernel map is surjective. -/
theorem torus_surjective_of_finiteKernel_image_cover
    {D S G : Variety k} [AlgebraicGroup D] [AlgebraicGroup S] [AlgebraicGroup G]
    (hD : IsTorus D) (hS : IsTorus S)
    (p : Morphism D S) (q : Morphism S G) (hfinite : Finite q.kernel)
    (hcover : ∀ s, ∃ d, q.onPoints (p.onPoints d) = q.onPoints s) :
    Function.Surjective p.onPoints := by
  by_contra hn
  obtain ⟨χ, hχ, y, hy⟩ :=
    IsTorus.exists_character_ne_one_of_not_surjective hD hS p hn
  let : Finite q.kernel := hfinite
  have hχrange : Set.range χ.onPoints ⊆
      χ.onPoints '' (q.kernel : Set (Variety.Point S)) := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨d, hd⟩ := hcover s
    refine ⟨(p.onPoints d)⁻¹ * s, ?_, ?_⟩
    · change q.onPoints ((p.onPoints d)⁻¹ * s) = 1
      rw [map_mul, map_inv, hd, inv_mul_cancel]
    · rw [map_mul, map_inv, hχ d, inv_one, one_mul]
  have hfiniteRange : (Set.range χ.toVariety.toFun).Finite :=
    ((Set.toFinite (q.kernel : Set (Variety.Point S))).image χ.onPoints).subset hχrange
  have hsub := connected_finite_morphism_range_subsingleton
    χ.toVariety hS.isConnected hfiniteRange
  exact hy ((hsub (Set.mem_range_self y) (Set.mem_range_self 1)).trans χ.map_one)

private def tupleOne {D S : Variety k} [AlgebraicGroup D] [AlgebraicGroup S] :
    Morphism D S where
  toVariety := Variety.Morphism.const D S 1
  map_one := rfl
  map_mul := by intro _ _; exact (one_mul 1).symm

private def tupleMul {D S : Variety k} [AlgebraicGroup D] [AlgebraicGroup S]
    (hS : IsMulCommutative (Variety.Point S)) (f g : Morphism D S) : Morphism D S where
  toVariety := (Theory.AlgebraicGroup.mulMorphism S).comp (f.toVariety.pair g.toVariety)
  map_one := by change f.onPoints 1 * g.onPoints 1 = 1; simp
  map_mul := by
    intro x y
    change f.onPoints (x * y) * g.onPoints (x * y) =
      (f.onPoints x * g.onPoints x) * (f.onPoints y * g.onPoints y)
    rw [map_mul, map_mul]
    have hc : f.onPoints y * g.onPoints x = g.onPoints x * f.onPoints y :=
      (isMulCommutative_iff.mp hS) _ _
    simp only [mul_assoc, ← mul_assoc (f.onPoints y), hc]

private def tupleListProduct {D S : Variety k} [AlgebraicGroup D] [AlgebraicGroup S]
    (hS : IsMulCommutative (Variety.Point S)) : List (Morphism D S) → Morphism D S
  | [] => tupleOne
  | f :: fs => tupleMul hS f (tupleListProduct hS fs)

omit [IsAlgClosed k] in
private lemma tupleListProduct_apply {D S : Variety k}
    [AlgebraicGroup D] [AlgebraicGroup S]
    (hS : IsMulCommutative (Variety.Point S)) (fs : List (Morphism D S))
    (x : Variety.Point D) :
    (tupleListProduct hS fs).onPoints x = (fs.map fun f => f.onPoints x).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change f.onPoints x * (tupleListProduct hS fs).onPoints x = _
    rw [ih]
    rfl

/-- The product of a finite tuple of cocharacters is a regular morphism. -/
noncomputable def cocharacterTupleProduct {S : Variety k} [AlgebraicGroup S]
    (hS : IsTorus S) {n : ℕ} (μ : Fin n → Morphism (KMult k) S) :
    Morphism (dVariety k n) S :=
  tupleListProduct hS.isMulCommutative
    (List.ofFn fun i => (μ i).comp (dCoordinateCharacter n i))

omit [IsAlgClosed k] in
theorem cocharacterTupleProduct_apply {S : Variety k} [AlgebraicGroup S]
    (hS : IsTorus S) {n : ℕ} (μ : Fin n → Morphism (KMult k) S)
    (x : Variety.Point (dVariety k n)) :
    (cocharacterTupleProduct hS μ).onPoints x =
      (List.ofFn fun i => (μ i).onPoints ((dCoordinateCharacter n i).onPoints x)).prod := by
  rw [cocharacterTupleProduct, tupleListProduct_apply, List.map_ofFn]
  rfl

/-- Coordinate-dependent powers of the characteristic are bijective on torus points. -/
theorem diagonal_primePower_bijective (p : ℕ) [CharP k p] [Fact p.Prime]
    {n : ℕ} (a : Fin n → ℕ) :
    Function.Bijective (fun x : Variety.Point (dVariety k n) =>
      (dPointEquiv n).symm (fun i => dPointEquiv n x i ^ (p ^ a i))) := by
  have hunits (m : ℕ) : Function.Bijective (fun t : kˣ => t ^ (p ^ m)) := by
    constructor
    · intro x y hxy
      apply Units.ext
      apply (frobenius_inj k p).iterate m
      have hval := congrArg (Units.coeHom k) hxy
      rw [map_pow, map_pow] at hval
      change (x : k) ^ p ^ m = (y : k) ^ p ^ m at hval
      simpa only [iterate_frobenius] using hval
    · intro y
      obtain ⟨x, hx⟩ := units_zpow_surjective_of_isAlgClosed (k := k)
        (p ^ m : ℕ) (by exact_mod_cast (pow_ne_zero m (Fact.out : p.Prime).ne_zero)) y
      exact ⟨x, (zpow_natCast x (p ^ m)).symm.trans hx⟩
  constructor
  · intro x y hxy
    apply (dPointEquiv n).injective
    have h := (dPointEquiv n).symm.injective hxy
    funext i
    exact (hunits (a i)).1 (congrFun h i)
  · intro y
    choose x hx using fun i => (hunits (a i)).2 (dPointEquiv n y i)
    refine ⟨(dPointEquiv n).symm x, ?_⟩
    apply (dPointEquiv n).injective
    simp only [Equiv.apply_symm_apply]
    exact funext hx

/-- A bijective composite from a torus detects injectivity of a finite-kernel map. -/
theorem torus_injective_of_bijective_composite
    {D S G : Variety k} [AlgebraicGroup D] [AlgebraicGroup S] [AlgebraicGroup G]
    (hD : IsTorus D) (hS : IsTorus S)
    (p : Morphism D S) (q : Morphism S G) (hfinite : Finite q.kernel)
    (hcomp : Function.Bijective (q.comp p).onPoints) :
    Function.Injective q.onPoints := by
  have hp : Function.Surjective p.onPoints :=
    torus_surjective_of_finiteKernel_image_cover hD hS p q hfinite
      (fun s => hcomp.2 (q.onPoints s))
  intro x y hxy
  obtain ⟨a, rfl⟩ := hp x
  obtain ⟨b, rfl⟩ := hp y
  exact congrArg p.onPoints (hcomp.1 hxy)

end Theory.AlgebraicGroup
