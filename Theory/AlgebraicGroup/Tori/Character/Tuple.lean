module

public import Theory.AlgebraicGroup.Tori.Character.Laurent

universe u

/-! Algebraic-group morphisms assembled from finite tuples of characters. -/

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A finite tuple of characters of `T`, regarded as a morphism `T → D_n`. -/
@[expose]
public def torusCharacterTupleMorphism
    (T : Variety k) [AlgebraicGroup T]
    (n : ℕ) (χ : Fin n → TorusCharacter T) :
    AlgebraicGroup.Morphism T (dVariety k n) := by
  let F : Variety.Morphism T (dVariety k n) :=
    { toFun := fun x => (dPointEquiv n).symm fun j =>
          dPointEquiv 1 ((χ j).toVariety.toFun x) 0
      regular := by
        intro c
        cases c with
        | inl j =>
            rcases (χ j.down).toVariety.regular
                (Sum.inl (ULift.up (0 : Fin 1))) with ⟨p, hp⟩
            refine ⟨p, fun x => ?_⟩
            change ((χ j.down).toVariety.toFun x).val
              (Sum.inl (ULift.up (0 : Fin 1))) = evalPolynomial x.val p
            exact hp x
        | inr j =>
            rcases (χ j.down).toVariety.regular
                (Sum.inr (ULift.up (0 : Fin 1))) with ⟨p, hp⟩
            refine ⟨p, fun x => ?_⟩
            change ((χ j.down).toVariety.toFun x).val
              (Sum.inr (ULift.up (0 : Fin 1))) = evalPolynomial x.val p
            exact hp x }
  refine
    { toVariety := F
      map_one := ?_
      map_mul := ?_ }
  · apply (dPointEquiv n).injective
    rw [dPointEquiv_one]
    funext j
    change dPointEquiv 1 ((χ j).toVariety.toFun 1) 0 = 1
    rw [(χ j).map_one, dPointEquiv_one]
    rfl
  · intro x y
    apply (dPointEquiv n).injective
    rw [dPointEquiv_mul]
    funext j
    change dPointEquiv 1 ((χ j).toVariety.toFun (x * y)) 0 =
      dPointEquiv 1 ((χ j).toVariety.toFun x) 0 *
        dPointEquiv 1 ((χ j).toVariety.toFun y) 0
    rw [(χ j).map_mul]
    exact congrFun (dPointEquiv_mul 1 _ _) 0

/-- Pointwise evaluation of a tuple-of-characters morphism. -/
public lemma torusCharacterTupleMorphism_apply
    (T : Variety k) [AlgebraicGroup T]
    (n : ℕ) (χ : Fin n → TorusCharacter T)
    (x : Variety.Point T) (j : Fin n) :
    dPointEquiv n ((torusCharacterTupleMorphism T n χ).onPoints x) j =
      dPointEquiv 1 ((χ j).onPoints x) 0 := by
  rfl

/-- A finite tuple of Laurent characters, regarded as an algebraic-group
morphism between standard diagonal tori. -/
@[expose]
public noncomputable def dCharacterTupleMorphism
    (m n : ℕ) (z : Fin m → Fin n → ℤ) :
    AlgebraicGroup.Morphism (dVariety k n) (dVariety k m) :=
  torusCharacterTupleMorphism (dVariety k n) m
    (fun j => dLaurentCharacter n (z j))

/-- Pointwise evaluation of a tuple of Laurent characters. -/
public lemma dCharacterTupleMorphism_apply
    (m n : ℕ) (z : Fin m → Fin n → ℤ)
    (x : Variety.Point (dVariety k n)) (j : Fin m) :
    dPointEquiv m ((dCharacterTupleMorphism (k := k) m n z).onPoints x) j =
      ∏ i, (dPointEquiv n x i) ^ z j i := by
  change dPointEquiv 1
      ((dLaurentCharacter (k := k) n (z j)).onPoints x) 0 = _
  exact dLaurentCharacter_apply n (z j) x

/-- A product of integral powers of Laurent monomials is the Laurent monomial
whose exponent vector is the corresponding linear combination. -/
public lemma prod_laurentMonomial_zpow
    {G : Type*} [CommGroup G] {I J : Type*} [Fintype I] [Fintype J]
    (x : I → G) (z : J → I → ℤ) (w : J → ℤ) :
    (∏ j, (∏ i, x i ^ z j i) ^ w j) =
      ∏ i, x i ^ (∑ j, w j * z j i) := by
  classical
  calc
    (∏ j, (∏ i, x i ^ z j i) ^ w j) =
        ∏ j, ∏ i, (x i ^ z j i) ^ w j := by
      apply Finset.prod_congr rfl
      intro j hj
      exact (Finset.prod_zpow (fun i => x i ^ z j i) Finset.univ (w j)).symm
    _ = ∏ j, ∏ i, x i ^ (w j * z j i) := by
      apply Finset.prod_congr rfl
      intro j hj
      apply Finset.prod_congr rfl
      intro i hi
      rw [mul_comm, zpow_mul]
    _ = ∏ i, ∏ j, x i ^ (w j * z j i) := Finset.prod_comm
    _ = ∏ i, x i ^ (∑ j, w j * z j i) := by
      apply Finset.prod_congr rfl
      intro i hi
      symm
      induction (Finset.univ : Finset J) using Finset.induction_on with
      | empty => simp
      | @insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

/-- Composition of character tuples corresponds to multiplication of their
integer exponent matrices. -/
public lemma dCharacterTupleMorphism_comp
    (l m n : ℕ) (w : Fin l → Fin m → ℤ) (z : Fin m → Fin n → ℤ) :
    (dCharacterTupleMorphism (k := k) l m w).comp
        (dCharacterTupleMorphism (k := k) m n z) =
      dCharacterTupleMorphism (k := k) l n
        (fun q i => ∑ j, w q j * z j i) := by
  apply Theory.AlgebraicGroup.Morphism.ext
  funext x
  apply (dPointEquiv l).injective
  funext q
  change dPointEquiv l
      ((dCharacterTupleMorphism (k := k) l m w).onPoints
        ((dCharacterTupleMorphism (k := k) m n z).onPoints x)) q =
    dPointEquiv l
      ((dCharacterTupleMorphism (k := k) l n
        (fun q i => ∑ j, w q j * z j i)).onPoints x) q
  rw [dCharacterTupleMorphism_apply, dCharacterTupleMorphism_apply]
  simp_rw [dCharacterTupleMorphism_apply]
  exact prod_laurentMonomial_zpow (dPointEquiv n x) z (w q)

/-- The tuple of standard coordinate characters is the identity morphism. -/
public lemma dCharacterTupleMorphism_basis (n : ℕ) :
    dCharacterTupleMorphism (k := k) n n (fun j => Pi.single j 1) =
      Theory.AlgebraicGroup.Morphism.id (dVariety k n) := by
  apply Theory.AlgebraicGroup.Morphism.ext
  funext x
  apply (dPointEquiv n).injective
  funext j
  change dPointEquiv n
      ((dCharacterTupleMorphism (k := k) n n
        (fun j => Pi.single j 1)).onPoints x) j = dPointEquiv n x j
  rw [dCharacterTupleMorphism_apply]
  simp [Pi.single_apply]

end Theory.AlgebraicGroup
