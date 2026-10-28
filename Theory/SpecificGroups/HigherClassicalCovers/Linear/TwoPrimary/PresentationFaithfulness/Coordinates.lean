module

public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.FiniteTorus
public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.Bruhat.Tori

/-!
# Coordinate transport for the elementary presentation

An injection of coordinate sets gives an actual homomorphism between the
presented Steinberg groups. Its action on Weyl and torus words transports the
proved degree-three finite-field torus identities to every degree at least
three. In particular, this supplies multiplicativity, root reversal and
three-coordinate torus factorization in degree four without assuming matrix
faithfulness.

Source: Steinberg, *Lectures on Chevalley Groups*, §6, Lemmas 38–40 and
Theorem 9, printed pp.71–74 (`refs/KGroup/GLS3/Chapter2St1.tex`).
The degree-three producers are `Faithfulness.FiniteTorus` and `Bruhat.Tori`.
-/

@[expose] public section

namespace Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimaryFaithfulness

open Theory.SpecificGroups.LinearHigher SteinbergWords
variable {m n : ℕ} {F : Type*} [Field F]

/-- Relabel a root along an injection of coordinates. -/
def coordinateRoot (e : Fin m ↪ Fin n) (r : Root m) : Root n :=
  root (e r.val.1) (e r.val.2) (fun h => r.property (e.injective h))

/-- Coordinate inclusions preserve the literal elementary presentation. -/
def coordinateMap (e : Fin m ↪ Fin n) : SteinbergGroup m F →* SteinbergGroup n F :=
  lift {
    add := fun r a b => generator_relations.add (coordinateRoot e r) a b
    distant := fun r s a b hrs hsr => generator_relations.distant (coordinateRoot e r) (coordinateRoot e s) a b
      (fun h => hrs (e.injective h)) (fun h => hsr (e.injective h))
    chain := fun i j k hij hjk hik a b => generator_relations.chain
      (e i) (e j) (e k) (fun h => hij (e.injective h))
      (fun h => hjk (e.injective h)) (fun h => hik (e.injective h)) a b }

@[simp] theorem coordinateMap_generator (e : Fin m ↪ Fin n) (r : Root m) (a : F) :
    coordinateMap e (generator r a) = generator (coordinateRoot e r) a :=
  lift_generator _ _ _

@[simp] theorem coordinateMap_weylWord (e : Fin m ↪ Fin n)
    (i j : Fin m) (hij : i ≠ j) (t : Fˣ) :
    coordinateMap e (weylWord generator i j hij t) =
      weylWord generator (e i) (e j) (fun h => hij (e.injective h)) t := by
  simp [weylWord, coordinateRoot, root]

@[simp] theorem coordinateMap_torusWord (e : Fin m ↪ Fin n)
    (i j : Fin m) (hij : i ≠ j) (t : Fˣ) :
    coordinateMap e (torusWord generator i j hij t) =
      torusWord generator (e i) (e j) (fun h => hij (e.injective h)) t := by
  simp only [torusWord, map_mul, coordinateMap_weylWord]

/-- The ordered three-coordinate subsystem used for rank-two identities. -/
def threeCoordinates (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Fin 3 ↪ Fin n where
  toFun := ![i, j, k]
  inj' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all

/-- Finite-field torus multiplicativity transports through an actual presentation map. -/
theorem torusWord_mul [Finite F] (hn : 2 < n) (i j : Fin n) (hij : i ≠ j)
    (s t : Fˣ) :
    torusWord generator i j hij s * torusWord generator i j hij t =
      torusWord generator i j hij (s * t) := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
  let e := threeCoordinates i j k hij hki.symm hkj.symm
  have h := congrArg (coordinateMap (F := F) e)
    (Matrix.PSL3.UniversalProjection.Faithfulness.torusMultiplicative
      (F := F) 0 1 (by decide) s t)
  simpa only [Matrix.PSL3.UniversalProjection.Faithfulness.torus,
    map_mul, coordinateMap_torusWord, e, threeCoordinates, Function.Embedding.coeFn_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- Reversing a root inverts its torus parameter. -/
theorem torusWord_reverse [Finite F] (hn : 2 < n) (i j : Fin n) (hij : i ≠ j)
    (t : Fˣ) : torusWord generator j i hij.symm t = torusWord generator i j hij t⁻¹ := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
  let e := threeCoordinates i j k hij hki.symm hkj.symm
  have h := congrArg (coordinateMap (F := F) e)
    (Matrix.PSL3.UniversalProjection.Faithfulness.torus_reverse
      Matrix.PSL3.UniversalProjection.Faithfulness.torusMultiplicative
      0 1 (by decide) t)
  simpa only [Matrix.PSL3.UniversalProjection.Faithfulness.torus,
    coordinateMap_torusWord, e, threeCoordinates, Function.Embedding.coeFn_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- The torus of a sum of two adjacent roots is their product. -/
theorem torusWord_chain [Finite F] (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (t : Fˣ) :
    torusWord generator i k hik t =
      torusWord generator i j hij t * torusWord generator j k hjk t := by
  let e := threeCoordinates i j k hij hik hjk
  have h := congrArg (coordinateMap (F := F) e)
    (Matrix.PSL3.UniversalProjection.Faithfulness.torus_zero_two
      Matrix.PSL3.UniversalProjection.Faithfulness.torusMultiplicative t)
  simpa [Matrix.PSL3.UniversalProjection.Faithfulness.torus,
    e, threeCoordinates] using h

end Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimaryFaithfulness
