module

public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PresentationFaithfulness.Tori
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PresentationFaithfulness.Separation
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PresentationFaithfulness.PositiveCollection
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PresentationFaithfulness.WeylKernel
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.CoprimeRootLifts
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Degree-four Steinberg presentation faithfulness over finite fields

The finite-field torus calculation and upper/monomial matrix separation
are proved in the descendants imported here. The independently proved Bruhat
coverage, faithfulness on the positive subgroup and collection of the Weyl
kernel into the torus discharge every premise of the kernel reduction below.
Thus the literal map from the elementary Steinberg presentation to SL₄ is
injective over every finite field, preserving the scalar center. Together
with its existing surjectivity this proves the degree-four instance of the
source presentation theorem, including the required Fermat-prime fields.

The final theorem applies this faithfulness result to the existing coprime-kernel
root lifts. Actual prime field cardinality supplies the characteristic,
and the resulting surjective map SL₄ → E commutes with the literal
projection to PSL₄. No two-primary bound or universality premise is used.

Source: Steinberg, *Lectures on Chevalley Groups*, §6, Theorems 8–9 and
the explicit SL example, printed pp.71–74; §7, Theorem 11, printed
pp.86–88 (`refs/KGroup/GLS3/Chapter2St1.tex`).
-/

@[expose] public section

namespace Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimaryFaithfulness

open Theory.SpecificGroups.LinearHigher
open scoped MatrixGroups
universe u v
variable {F : Type u} [Field F] [Finite F]

/-- Bruhat coverage and the two restricted collection statements imply
faithfulness into the literal SL₄, retaining its scalar center. -/
theorem matrixMap_injective_of_bruhat
    (hcover : BruhatCover F) (hU : UpperFaithful F) (hW : WeylKernelInTorus F) :
    Function.Injective (matrixMap (n := 4) (F := F)) := by
  have hker (g : SteinbergGroup 4 F) (hg : matrixMap g = 1) : g = 1 := by
    obtain ⟨u, w, v, he⟩ := hcover g
    have hw : matrixMap w.val = matrixMap (u.val⁻¹ * v.val⁻¹) := by
      calc
        _ = (matrixMap u.val)⁻¹ * matrixMap g * (matrixMap v.val)⁻¹ := by
          rw [he, map_mul, map_mul]
          group
        _ = _ := by rw [hg]; simp only [map_mul, map_inv, mul_one]
    have hw1 : matrixMap w.val = 1 := upperWeylSeparation _ _
      ((upperSubgroup F).mul_mem ((upperSubgroup F).inv_mem u.property)
        ((upperSubgroup F).inv_mem v.property)) w.property hw.symm
    have hew : w.val = 1 := torusSubgroup_eq_one_of_matrixMap (hW _ w.property hw1) hw1
    have heuv : (u * v : upperSubgroup F) = 1 := by
      apply hU
      change matrixMap (u.val * v.val) = matrixMap 1
      rw [he, hew, mul_one] at hg
      simpa only [map_one] using hg
    rw [he, hew, mul_one]
    exact congrArg Subtype.val heuv
  intro g h he
  apply mul_inv_eq_one.mp
  apply hker
  rw [map_mul, map_inv, he, mul_inv_cancel]

/-- The elementary Steinberg presentation maps faithfully to the literal SL₄
over every finite field. In particular no Fermat-prime restriction is needed. -/
theorem matrixMap_injective :
    Function.Injective (matrixMap (n := 4) (F := F)) :=
  matrixMap_injective_of_bruhat bruhatCover upperFaithful weylKernelInTorus

/-- Actual prime cardinality supplies the characteristic needed by root lifting. -/
theorem charP_of_prime_card (p : ℕ) (hp : p.Prime) (hF : Nat.card F = p) : CharP F p := by
  let : Fintype F := Fintype.ofFinite F
  let : Fact p.Prime := ⟨hp⟩
  exact charP_of_card_eq_prime (by rwa [← Nat.card_eq_fintype_card])

/-- The literal covering-map application, conditional only on the remaining
Bruhat collection inputs. These premises must be discharged before claiming
the source presentation theorem or the two-primary bound. -/
theorem exists_covering_of_bruhat
    (hcover : BruhatCover F) (hU : UpperFaithful F) (hW : WeylKernelInTorus F)
    (p : ℕ) (hp : p.Prime) (hF : Nat.card F = p)
    {E : Type v} [Group E] [Group.IsPerfect E]
    (f : E →* PSL(4, F)) (hf : Function.Surjective f)
    (hcenter : f.ker ≤ Subgroup.center E) (hcop : (Nat.card f.ker).Coprime p) :
    ∃ s : SL(4, F) →* E, Function.Surjective s ∧
      f.comp s = QuotientGroup.mk' (Subgroup.center SL(4, F)) ∧
      s.ker ≤ Subgroup.center SL(4, F) := by
  let : CharP F p := charP_of_prime_card p hp hF
  exact CoprimeRootLifts.exists_covering_of_matrixMap_injective
    f hf hcenter hcop (by decide) (matrixMap_injective_of_bruhat hcover hU hW)

/-- A perfect central extension of PSL₄ with kernel order prime to the field
cardinality is covered by the literal SL₄. Prime cardinality supplies `CharP`;
the finite-field presentation theorem discharges the root-lifting premise. -/
theorem exists_covering
    (p : ℕ) (hp : p.Prime) (hF : Nat.card F = p)
    {E : Type v} [Group E] [Group.IsPerfect E]
    (f : E →* PSL(4, F)) (hf : Function.Surjective f)
    (hcenter : f.ker ≤ Subgroup.center E) (hcop : (Nat.card f.ker).Coprime p) :
    ∃ s : SL(4, F) →* E, Function.Surjective s ∧
      f.comp s = QuotientGroup.mk' (Subgroup.center SL(4, F)) ∧
      s.ker ≤ Subgroup.center SL(4, F) := by
  let : CharP F p := charP_of_prime_card p hp hF
  exact CoprimeRootLifts.exists_covering_of_matrixMap_injective
    f hf hcenter hcop (by decide) matrixMap_injective

end Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimaryFaithfulness
