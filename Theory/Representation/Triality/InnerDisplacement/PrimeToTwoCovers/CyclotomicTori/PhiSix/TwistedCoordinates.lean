module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix.Descent
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix.Order
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix.TwistedCoordinates.Coroots
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The marked sixth-cyclotomic plane in the actual split triality torus

Let q = 2ⁿ and let d be the full p-primary part of q² − q + 1, where p > 3.
Since d divides q⁶ − 1, the units of the actual larger coefficient field
contain a cyclic subgroup of order d. Its faithful coroot coordinates with
columns (1,q+1,1,1) and (1,0,−q,q−1) give the required plane. The minor
−(q+1) is a unit modulo d, without requiring ZMod d to be a field.

The simple-Weyl formulas prove fixedness under c times the forward
q-Frobenius diagram action, with the arm cycle 0 → 2 → 3 → 0. They also
prove that direct conjugation by c⁴ acts by q² on the first marked generator
and fixes the second. Here c is the literal word n₀ n₂ n₃ n₁. Thus every
field, embedding and conjugation premise of `TwistedPlane` is discharged.
The separate Lang construction can consume this plane through `PhiSix.Descent`.

Source: GLS3 §§2.1–2.4, particularly the torus and Weyl relations in 2.4.7–8,
and the nondefining-characteristic applications of §6.1
(`refs/KGroup/GLS3/chapter2.tex`, `refs/KGroup/GLS3/chapter6.tex`).
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix.TwistedCoordinates
open Standard Standard.EvenField Standard.ConcreteBruhat
open Standard.Parabolics TorusCoordinates RootConjugation
noncomputable section
variable {d : ℕ}

lemma larger_prime (n : ℕ) (hn : 0 < n) : (largerParameters n hn).prime = 2 := rfl

lemma rotation_exponentProduct (n : ℕ) (hn : 0 < n)
    (u : Multiplicative (ZMod d) →* (ExtensionField (largerParameters n hn))ˣ)
    (a : Fin 4 → ZMod d) :
    (MulAut.conj (rotation n hn))
      (exponentProduct (largerParameters n hn) (larger_prime n hn) u (Multiplicative.ofAdd a)) =
    exponentProduct (largerParameters n hn) (larger_prime n hn) u (Multiplicative.ofAdd (coxeter a)) := by
  exact (congrArg (fun g : SplitGroup (largerParameters n hn) => (MulAut.conj g)
    (exponentProduct (largerParameters n hn) (larger_prime n hn) u
      (Multiplicative.ofAdd a))) (rotation_eq_word n hn)).trans
    (word_exponentProduct (largerParameters n hn) (larger_prime n hn) u a)

lemma halfTwist_torusWord (n : ℕ) (hn : 0 < n) (i : Fin 4)
    (t : (ExtensionField (largerParameters n hn))ˣ) :
    halfTwist n hn (torusWord (largerParameters n hn) i t) =
      torusWord (largerParameters n hn) (typeD4DiagramPermutation i) (t ^ (2^n)) := by
  change diagramAutomorphism _
    (OuterOdd.coefficientSplit _ (coefficientFrobenius (2*n) (by omega) n)
      (torusWord _ i t)) = _
  simp only [torusWord, weylWord, positiveRoot, negativeRoot, map_mul,
    OuterOdd.coefficientSplit_positive, OuterOdd.coefficientSplit_negative,
    diagramAutomorphism_positive, diagramAutomorphism_negative,
    typeD4DiagramBasePermutation_numbered, map_neg, map_inv₀, map_one,
    coefficientFrobenius_apply, Units.val_pow_eq_pow_val]

def frobeniusDiagram (q : ZMod d) (a : Fin 4 → ZMod d) : Fin 4 → ZMod d :=
  ![q * a 3, q * a 1, q * a 0, q * a 2]

lemma halfTwist_exponentProduct (n : ℕ) (hn : 0 < n)
    (u : Multiplicative (ZMod d) →* (ExtensionField (largerParameters n hn))ˣ)
    (a : Fin 4 → ZMod d) :
    halfTwist n hn
      (exponentProduct (largerParameters n hn) (larger_prime n hn) u (Multiplicative.ofAdd a)) =
    exponentProduct (largerParameters n hn) (larger_prime n hn) u
      (Multiplicative.ofAdd (frobeniusDiagram (2^n) a)) := by
  have hs (i : Fin 4) (t : ZMod d) :
      halfTwist n hn (exponentProduct (largerParameters n hn) (larger_prime n hn) u
        (Multiplicative.ofAdd (Function.update (0 : Fin 4 → ZMod d) i t))) =
      exponentProduct (largerParameters n hn) (larger_prime n hn) u
        (Multiplicative.ofAdd (Function.update (0 : Fin 4 → ZMod d) (typeD4DiagramPermutation i) ((2^n : ℕ)*t))) := by
    rw [exponentProduct_single, exponentProduct_single, halfTwist_torusWord, unit_nat_coeff]
  have decomp : a = Function.update (0 : Fin 4 → ZMod d) 0 (a 0) + Function.update (0 : Fin 4 → ZMod d) 2 (a 2) +
      Function.update (0 : Fin 4 → ZMod d) 3 (a 3) + Function.update (0 : Fin 4 → ZMod d) 1 (a 1) := by
    funext j; fin_cases j <;> simp
  conv_lhs => rw [decomp]
  simp only [exponentProduct_add, map_mul, hs]
  simp only [← exponentProduct_add]
  congr 2
  funext j
  fin_cases j <;> simp [frobeniusDiagram, typeD4DiagramPermutation]

/-- Columns (1,q+1,1,1) and (1,0,-q,q-1). -/
def planeCoordinates (q : ZMod d) (z : ZMod d × ZMod d) : Fin 4 → ZMod d :=
  ![z.1 + z.2, (q+1)*z.1, z.1-q*z.2, z.1+(q-1)*z.2]

lemma planeCoordinates_injective (q : ZMod d) (hq : IsUnit (q+1)) :
    Function.Injective (planeCoordinates q) := by
  intro z w h
  have h1 : z.1 = w.1 := hq.mul_left_cancel (congrFun h 1)
  have h0 : z.1+z.2 = w.1+w.2 := congrFun h 0
  rw [h1] at h0
  exact Prod.ext h1 (add_left_cancel h0)

def planeExponents (q : ZMod d) : Plane d →* Multiplicative (Fin 4 → ZMod d) where
  toFun z := Multiplicative.ofAdd (planeCoordinates q z.toAdd)
  map_one' := by
    change Multiplicative.ofAdd (planeCoordinates q 0) = Multiplicative.ofAdd 0
    congr 1
    funext i
    fin_cases i <;> simp [planeCoordinates]
  map_mul' z w := by
    change Multiplicative.ofAdd (planeCoordinates q (z.toAdd+w.toAdd)) =
      Multiplicative.ofAdd (planeCoordinates q z.toAdd + planeCoordinates q w.toAdd)
    congr 1
    funext i
    fin_cases i <;> simp [planeCoordinates] <;> ring

lemma plane_twisted (q : ZMod d) (hq : q^2-q+1=0) (z : ZMod d × ZMod d) :
    coxeter (frobeniusDiagram q (planeCoordinates q z)) = planeCoordinates q z := by
  funext i
  fin_cases i <;> simp [coxeter, frobeniusDiagram, planeCoordinates]
  · linear_combination -(z.1+z.2)*hq
  · linear_combination -z.1*hq
  · linear_combination -z.1*hq
  · linear_combination (z.2-z.1)*hq

lemma plane_first_action (q : ZMod d) (hq : q^2-q+1=0) :
    coxeter (coxeter (coxeter (coxeter (planeCoordinates q (1,0))))) =
      planeCoordinates q (q^2,0) := by
  funext i
  fin_cases i <;> simp [coxeter, planeCoordinates]
  · linear_combination -hq
  · linear_combination -(q+2)*hq
  · linear_combination -hq
  · linear_combination -hq

lemma plane_second_action (q : ZMod d) :
    coxeter (coxeter (coxeter (coxeter (planeCoordinates q (0,1))))) =
      planeCoordinates q (0,1) := by
  funext i
  fin_cases i <;> simp [coxeter, planeCoordinates] <;> ring

lemma conj_four {G : Type*} [Group G] (g x : G) :
    (MulAut.conj (g^4)) x =
      (MulAut.conj g) ((MulAut.conj g) ((MulAut.conj g) ((MulAut.conj g) x))) := by
  simpa only [pow_succ, pow_zero, one_mul] using conj_product_four g g g g x

lemma rotation_four_exponentProduct (n : ℕ) (hn : 0 < n)
    (u : Multiplicative (ZMod d) →* (ExtensionField (largerParameters n hn))ˣ)
    (a : Fin 4 → ZMod d) :
    (MulAut.conj (rotation n hn ^ 4))
      (exponentProduct (largerParameters n hn) (larger_prime n hn) u (Multiplicative.ofAdd a)) =
    exponentProduct (largerParameters n hn) (larger_prime n hn) u
      (Multiplicative.ofAdd (coxeter (coxeter (coxeter (coxeter a))))) := by
  simp only [conj_four, rotation_exponentProduct]

/-- The homomorphism into the literal split Geck group. -/
def embedding (n : ℕ) (hn : 0 < n)
    (u : Multiplicative (ZMod d) →* (ExtensionField (largerParameters n hn))ˣ) :
    Plane d →* SplitGroup (largerParameters n hn) :=
  (exponentProduct (largerParameters n hn) (larger_prime n hn) u).comp (planeExponents (2^n))

lemma embedding_injective (n : ℕ) (hn : 0 < n)
    (u : Multiplicative (ZMod d) →* (ExtensionField (largerParameters n hn))ˣ)
    (hu : Function.Injective u) (hq : IsUnit ((2^n : ZMod d)+1)) :
    Function.Injective (embedding n hn u) := by
  intro z w h
  apply planeCoordinates_injective (2^n) hq
  have hc := product_injective (largerParameters n hn) (larger_prime n hn) h
  funext i
  exact hu (congrFun hc i)

lemma embedding_twisted (n : ℕ) (hn : 0 < n)
    (u : Multiplicative (ZMod d) →* (ExtensionField (largerParameters n hn))ˣ)
    (hq : (2^n : ZMod d)^2-2^n+1=0) (z : Plane d) :
    rotation n hn * halfTwist n hn (embedding n hn u z) =
      embedding n hn u z * rotation n hn := by
  have h : (MulAut.conj (rotation n hn)) (halfTwist n hn (embedding n hn u z)) =
      embedding n hn u z := by
    change (MulAut.conj (rotation n hn)) (halfTwist n hn
      (exponentProduct (largerParameters n hn) (larger_prime n hn) u (Multiplicative.ofAdd (planeCoordinates (2^n) z.toAdd)))) = _
    simp only [halfTwist_exponentProduct, rotation_exponentProduct, plane_twisted _ hq]
    rfl
  change rotation n hn * halfTwist n hn (embedding n hn u z) * (rotation n hn)⁻¹ = _ at h
  exact (mul_inv_eq_iff_eq_mul).mp h

lemma embedding_first (n : ℕ) (hn : 0 < n)
    (u : Multiplicative (ZMod d) →* (ExtensionField (largerParameters n hn))ˣ)
    (hq : (2^n : ZMod d)^2-2^n+1=0) :
    rotation n hn ^ 4 * embedding n hn u (first d) * (rotation n hn ^ 4)⁻¹ =
      embedding n hn u (first d) ^ ((2^n)^2) := by
  change (MulAut.conj (rotation n hn ^ 4))
    (exponentProduct (largerParameters n hn) (larger_prime n hn) u (Multiplicative.ofAdd (planeCoordinates (2^n) (1,0)))) = _
  simp only [rotation_four_exponentProduct, plane_first_action _ hq]
  rw [← map_pow]
  change exponentProduct (largerParameters n hn) (larger_prime n hn) u
      (Multiplicative.ofAdd (planeCoordinates (2^n) ((2^n)^2,0))) =
    exponentProduct (largerParameters n hn) (larger_prime n hn) u
      (Multiplicative.ofAdd (planeCoordinates (2^n) (first d ^ ((2^n)^2)).toAdd))
  congr 3
  simp [first, ← ofAdd_nsmul, nsmul_eq_mul]

lemma embedding_second (n : ℕ) (hn : 0 < n)
    (u : Multiplicative (ZMod d) →* (ExtensionField (largerParameters n hn))ˣ) :
    rotation n hn ^ 4 * embedding n hn u (second d) * (rotation n hn ^ 4)⁻¹ =
      embedding n hn u (second d) := by
  change (MulAut.conj (rotation n hn ^ 4))
    (exponentProduct (largerParameters n hn) (larger_prime n hn) u (Multiplicative.ofAdd (planeCoordinates (2^n) (0,1)))) = _
  simp only [rotation_four_exponentProduct, plane_second_action]
  rfl

end
end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix.TwistedCoordinates


namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix.TwistedCoordinates
open Standard
noncomputable section

lemma modulus_dvd_six {q : ℕ} (hq : 1 ≤ q) : modulus q ∣ q^6-1 := by
  have hq2 : q ≤ q^2 := by nlinarith
  have hq3 : 1 ≤ q^3 := one_le_pow₀ hq
  have hq6 : 1 ≤ q^6 := one_le_pow₀ hq
  refine ⟨(q+1)*(q^3-1), ?_⟩
  dsimp only [modulus]
  zify [hq2, hq3, hq6]
  ring

lemma primary_dvd_six {q p : ℕ} (hq : 1 ≤ q) :
    p ^ (modulus q).factorization p ∣ q^6-1 :=
  (Nat.ordProj_dvd (modulus q) p).trans (modulus_dvd_six hq)

lemma primary_relation {q p : ℕ} (hq : 1 ≤ q) :
    (q : ZMod (p ^ (modulus q).factorization p))^2 - q + 1 = 0 := by
  have hq2 : q ≤ q^2 := by nlinarith
  have h := (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.ordProj_dvd (modulus q) p)
  simpa only [modulus, Nat.cast_add, Nat.cast_sub hq2, Nat.cast_pow, Nat.cast_one] using h

lemma primary_unit {q p : ℕ} [Fact p.Prime] (hq : 1 ≤ q)
    (hp : 3 < p) (hd : p ∣ modulus q) :
    IsUnit ((q : ZMod (p ^ (modulus q).factorization p)) + 1) := by
  have hdiv : q+1 ∣ q^2-1 := by
    refine ⟨q-1, ?_⟩
    have hq2 : 1 ≤ q^2 := one_le_pow₀ hq
    zify [hq, hq2]
    ring
  have hc := Nat.Coprime.of_dvd_right hdiv (primary_coprime hq hp hd ((modulus q).factorization p))
  rw [← Nat.cast_one, ← Nat.cast_add]
  exact (ZMod.isUnit_iff_coprime _ _).mpr hc.symm

lemma larger_units_card (n : ℕ) (hn : 0 < n) :
    Nat.card (ExtensionField (largerParameters n hn))ˣ = (2^n)^6-1 := by
  rw [Nat.card_units, card_extensionField]
  change (2^(2*n))^3-1 = (2^n)^6-1
  simp only [← pow_mul]
  congr 2
  omega

lemma cyclic_units {n d : ℕ} (hn : 0 < n) (hd : d ∣ (2^n)^6-1) :
    ∃ u : Multiplicative (ZMod d) →* (ExtensionField (largerParameters n hn))ˣ,
      Function.Injective u := by
  let U := (ExtensionField (largerParameters n hn))ˣ
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
  have hd' : d ∣ orderOf g := by rwa [hg, larger_units_card]
  have ht : orderOf (g ^ (orderOf g / d)) = d :=
    orderOf_pow_orderOf_div (by rw [hg]; exact Nat.card_pos.ne') hd'
  let H := Subgroup.zpowers (g ^ (orderOf g / d))
  have hcard : Nat.card H = d := (Nat.card_zpowers _).trans ht
  let e : Multiplicative (ZMod d) ≃* H := by
    rw [← hcard]
    exact zmodCyclicMulEquiv inferInstance
  exact ⟨H.subtype.comp e.toMonoidHom, Subtype.val_injective.comp e.injective⟩

end
end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix.TwistedCoordinates
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix
open Standard Standard.ConcreteBruhat TwistedCoordinates
noncomputable section

/-- The full sixth-cyclotomic primary plane in the actual split torus over GF(q⁶).
The equations use the forward diagram–q-Frobenius and the literal folded word. -/
theorem twistedPlane_nonempty (n : ℕ) (hn : 0 < n) (_hn' : 1 < n)
    (p : ℕ) [Fact p.Prime] (hp : 3 < p) (hd : p ∣ modulus (2^n)) :
    Nonempty (TwistedPlane n hn (p ^ (modulus (2^n)).factorization p)) := by
  have hq : 1 ≤ 2^n := one_le_pow₀ (by decide)
  obtain ⟨u, hu⟩ := cyclic_units hn (primary_dvd_six (p := p) hq)
  have hrel : (2^n : ZMod (p ^ (modulus (2^n)).factorization p))^2-2^n+1=0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using primary_relation (p := p) hq
  have hunit : IsUnit ((2^n : ZMod (p ^ (modulus (2^n)).factorization p))+1) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using primary_unit hq hp hd
  exact ⟨{
    embedding := embedding n hn u
    injective := embedding_injective n hn u hu hunit
    mem_torus := fun z => TorusCoordinates.product_mem _ _
    twisted := embedding_twisted n hn u hrel
    conjugate_first := embedding_first n hn u hrel
    conjugate_second := embedding_second n hn u
  }⟩

end
end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix
