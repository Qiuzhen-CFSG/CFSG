module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.Diagonal
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.RootConjugation.Torus

/-!
# Exponent coordinates and the folded Weyl action on the split D₄ torus

A cyclic unit homomorphism turns additive coroot exponents into the original
Geck torus words. The simple-coroot conjugation formula gives the Cartan
reflection on these exponents, and composing four reflections gives the direct
action of the word n₀ n₂ n₃ n₁. All formulas hold over ZMod d, including
composite d, and use the faithful split-torus coordinates.

Source: GLS3 §§2.3–2.4, especially the coroot and Weyl relations in 2.4.7–8
(`refs/KGroup/GLS3/chapter2.tex`). The sixth-cyclotomic construction in the
parent module applies this action to its two marked columns.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix.TwistedCoordinates
open Standard Standard.ConcreteBruhat
open Standard.Parabolics TorusCoordinates RootConjugation
noncomputable section

variable {d : ℕ} (P : Parameters) (hp : P.prime = 2)
  (u : Multiplicative (ZMod d) →* (ExtensionField P)ˣ)

def exponentCoordinates : Multiplicative (Fin 4 → ZMod d) →* Coordinates P where
  toFun a i := u (Multiplicative.ofAdd (a.toAdd i))
  map_one' := by funext i; exact map_one u
  map_mul' a b := by funext i; exact map_mul u _ _

def exponentProduct : Multiplicative (Fin 4 → ZMod d) →* SplitGroup P :=
  (productHom P hp).comp (exponentCoordinates P u)

lemma exponentProduct_add (a b : Fin 4 → ZMod d) :
    exponentProduct P hp u (Multiplicative.ofAdd (a+b)) =
      exponentProduct P hp u (Multiplicative.ofAdd a) *
      exponentProduct P hp u (Multiplicative.ofAdd b) :=
  map_mul (exponentProduct P hp u) _ _

lemma unit_coeff (t : ZMod d) (k : ℤ) :
    u (Multiplicative.ofAdd (t * (k : ZMod d))) = u (Multiplicative.ofAdd t) ^ k := by
  simpa only [← ofAdd_zsmul, zsmul_eq_mul, mul_comm] using
    map_zpow u (Multiplicative.ofAdd t) k

lemma unit_nat_coeff (t : ZMod d) (k : ℕ) :
    u (Multiplicative.ofAdd ((k : ZMod d) * t)) = u (Multiplicative.ofAdd t) ^ k := by
  simpa only [← ofAdd_nsmul, nsmul_eq_mul] using
    map_pow u (Multiplicative.ofAdd t) k

lemma exponentProduct_single (i : Fin 4) (t : ZMod d) :
    exponentProduct P hp u (Multiplicative.ofAdd (Function.update (0 : Fin 4 → ZMod d) i t)) =
      torusWord P i (u (Multiplicative.ofAdd t)) := by
  change product P _ = _
  rw [← product_single P hp]
  congr 1
  funext j
  by_cases h : j = i
  · subst j; simp [exponentCoordinates]
  · simp [exponentCoordinates, Function.update_of_ne h]

lemma weyl_single (i j : Fin 4) (t : ZMod d) :
    (MulAut.conj (weylWord P i 1))
      (exponentProduct P hp u (Multiplicative.ofAdd (Function.update (0 : Fin 4 → ZMod d) j t))) =
    exponentProduct P hp u (Multiplicative.ofAdd
      (Function.update (0 : Fin 4 → ZMod d) j t + Function.update (0 : Fin 4 → ZMod d) i (t * (-typeDCartanMatrix 2 j i : ℤ)))) := by
  simp only [exponentProduct_add, exponentProduct_single, MulAut.conj_apply,
    weylWord_torusWord_conjugation P hp, unit_coeff]

/-- Cartan reflection on coroot exponents, in the numbered basis. -/
def reflection (i : Fin 4) (a : Fin 4 → ZMod d) : Fin 4 → ZMod d :=
  a + Function.update (0 : Fin 4 → ZMod d) i
    (a 0 * (-typeDCartanMatrix 2 0 i : ℤ) +
     a 2 * (-typeDCartanMatrix 2 2 i : ℤ) +
     a 3 * (-typeDCartanMatrix 2 3 i : ℤ) +
     a 1 * (-typeDCartanMatrix 2 1 i : ℤ))

lemma weyl_exponentProduct (i : Fin 4) (a : Fin 4 → ZMod d) :
    (MulAut.conj (weylWord P i 1)) (exponentProduct P hp u (Multiplicative.ofAdd a)) =
      exponentProduct P hp u (Multiplicative.ofAdd (reflection i a)) := by
  have decomp : a = Function.update (0 : Fin 4 → ZMod d) 0 (a 0) + Function.update (0 : Fin 4 → ZMod d) 2 (a 2) +
      Function.update (0 : Fin 4 → ZMod d) 3 (a 3) + Function.update (0 : Fin 4 → ZMod d) 1 (a 1) := by
    funext j; fin_cases j <;> simp
  conv_lhs => rw [decomp]
  simp only [exponentProduct_add, map_mul, weyl_single]
  simp only [← exponentProduct_add]
  congr 2
  funext j
  fin_cases j <;> fin_cases i <;> simp [reflection] <;> ring

/-- The direct action of c = n₀ n₂ n₃ n₁. -/
def coxeter (a : Fin 4 → ZMod d) : Fin 4 → ZMod d :=
  ![a 2 + a 3 - a 1, a 0 + a 2 + a 3 - a 1,
    a 0 + a 3 - a 1, a 0 + a 2 - a 1]

lemma coxeter_eq_reflections (a : Fin 4 → ZMod d) :
    reflection 0 (reflection 2 (reflection 3 (reflection 1 a))) = coxeter a := by
  funext i
  fin_cases i <;> simp [reflection, coxeter, typeDCartanMatrix] <;> ring

lemma conj_product_four {G : Type*} [Group G] (a b c d x : G) :
    (MulAut.conj (a*b*c*d)) x =
      (MulAut.conj a) ((MulAut.conj b) ((MulAut.conj c) ((MulAut.conj d) x))) := by
  simp only [MulAut.conj_apply]
  group

lemma word_exponentProduct (a : Fin 4 → ZMod d) :
    (MulAut.conj (weylWord P 0 1 * weylWord P 2 1 * weylWord P 3 1 * weylWord P 1 1))
      (exponentProduct P hp u (Multiplicative.ofAdd a)) =
      exponentProduct P hp u (Multiplicative.ofAdd (coxeter a)) := by
  calc
    _ = (MulAut.conj (weylWord P 0 1))
      ((MulAut.conj (weylWord P 2 1))
        ((MulAut.conj (weylWord P 3 1))
          ((MulAut.conj (weylWord P 1 1))
            (exponentProduct P hp u (Multiplicative.ofAdd a))))) :=
      conj_product_four _ _ _ _ _
    _ = _ := by
      simp only [weyl_exponentProduct P hp u, coxeter_eq_reflections]

end
end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix.TwistedCoordinates
