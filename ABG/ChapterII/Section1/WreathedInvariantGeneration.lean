module
public import ABG.ChapterII.Section1.WreathedCentralizers
public import ABG.ChapterII.Section1.WreathedBaseProduct
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.IndexNormal

/-!
# Generation from a normalized outer subgroup

This is the cardinality step in ABG Chapter II §1 Lemma 2(xiii), article p.10.
Let `A` be a subgroup of the abelian base of order `2^n`, disjoint from the
center and normalizing a subgroup `X` disjoint from `A`. If `X` contains an
element outside the base, then `X` and `A` generate the whole wreathed group.
The preceding reductions in the invariant-subgroup argument supply these
hypotheses from the cyclic subgroup in the source statement.

For an outer element `g` of `X`, the function `a ↦ [a,g]` on `A` takes values
in `X` and in the base. Equality of two values says that the ratio of their
inputs centralizes `g`; a base element with this property is central.
Disjointness of `A` from the center therefore makes this function injective.
Its image and its translate by `g` give two disjoint cosets in `X`.
Multiplication by `A` remains injective because `A` and `X` are disjoint.
The domain has the prescribed cardinality of the whole group, so the resulting
function is surjective and all elements lie in `X ⊔ A`.
-/

private theorem two_coset_injective {S A : Type*} [Group S]
    (U : Subgroup S) (f : A → S) (hf : Function.Injective f)
    (hfU : ∀ a, f a ∈ U) (g : S) (hg : g ∉ U) :
    Function.Injective (fun p : A × Fin 2 => f p.1 * g ^ p.2.val) := by
  rintro ⟨a,i⟩ ⟨b,j⟩ he
  fin_cases i <;> fin_cases j
  · simp only [pow_zero, mul_one] at he
    exact Prod.ext (hf he) rfl
  · simp only [pow_zero, pow_one, mul_one] at he
    have hmem := U.mul_mem (U.inv_mem (hfU b)) (hfU a)
    rw [he] at hmem
    exact (hg (by simpa using hmem)).elim
  · simp only [pow_zero, pow_one, mul_one] at he
    have hmem := U.mul_mem (U.inv_mem (hfU a)) (hfU b)
    rw [← he] at hmem
    exact (hg (by simpa using hmem)).elim
  · simp only [pow_one, mul_left_inj] at he
    exact Prod.ext (hf he) rfl

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)
open scoped commutatorElement

public theorem sup_eq_top_of_outer_normalized (A X : Subgroup S)
    (hAU : A ≤ P.U) (hdAC : Disjoint A (Subgroup.center S))
    (hn : A ≤ Subgroup.normalizer (X : Set S)) (hdAX : Disjoint A X)
    (hcard : Nat.card A = 2 ^ n) (g : S) (hgX : g ∈ X) (hgU : g ∉ P.U) :
    X ⊔ A = ⊤ := by
  let hUN : P.U.Normal := P.U.normal_of_index_eq_two P.index_U
  let f : A → S := fun a => ⁅(a : S), g⁆
  have hfX (a : A) : f a ∈ X := by
    exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hn a.property) g).mp hgX)
      (X.inv_mem hgX)
  have hfU (a : A) : f a ∈ P.U := by
    have h := P.U.mul_mem (hAU a.property)
      (hUN.conj_mem _ (P.U.inv_mem (hAU a.property)) g)
    simpa only [f, commutatorElement_def, mul_assoc] using h
  have hf : Function.Injective f := by
    intro a b he
    have hc : Commute ((b : S)⁻¹ * (a : S)) g := by
      change (b : S)⁻¹ * (a : S) * g = g * ((b : S)⁻¹ * (a : S))
      calc
        _ = (b : S)⁻¹ * f a * g * (a : S) := by dsimp [f]; rw [commutatorElement_def]; group
        _ = (b : S)⁻¹ * f b * g * (a : S) := by rw [he]
        _ = _ := by dsimp [f]; rw [commutatorElement_def]; group
    have hba : (b : S)⁻¹ * (a : S) ∈ A := A.mul_mem (A.inv_mem b.property) a.property
    have hcZ := P.base_commute_outer_mem_center (hAU hba) hgU hc
    have he1 := Subgroup.disjoint_def.mp hdAC hba hcZ
    exact Subtype.ext (inv_mul_eq_one.mp he1).symm
  let f₂ : A × Fin 2 → X := fun p =>
    ⟨f p.1 * g ^ p.2.val, X.mul_mem (hfX p.1) (X.pow_mem hgX _)⟩
  have hf₂ : Function.Injective f₂ := by
    intro p q he
    exact two_coset_injective P.U f hf hfU g hgU (congrArg (fun x : X => (x : S)) he)
  let F : (A × Fin 2) × A → S := fun p => (f₂ p.1 : S) * (p.2 : S)
  have hF : Function.Injective F := by
    intro p q he
    have hpair : (f₂ p.1, p.2) = (f₂ q.1, q.2) :=
      Subgroup.mul_injective_of_disjoint hdAX.symm he
    have hp₁ : p.1 = q.1 := hf₂ (congrArg Prod.fst hpair)
    have hp₂ : p.2 = q.2 := congrArg (fun z : X × A => z.2) hpair
    exact Prod.ext hp₁ hp₂
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  have hbij : Function.Bijective F := by
    apply (Nat.bijective_iff_injective_and_card F).mpr
    refine ⟨hF, ?_⟩
    simp only [Nat.card_prod, Nat.card_fin, hcard, P.card]
    rw [pow_add, Nat.mul_comm 2 n, pow_mul]
    ring
  apply top_unique
  intro s _
  obtain ⟨⟨p,a⟩,rfl⟩ := hbij.surjective s
  exact (X ⊔ A).mul_mem ((show X ≤ X ⊔ A from le_sup_left) (f₂ p).property)
    ((show A ≤ X ⊔ A from le_sup_right) a.property)

end ABG.Wreathed.Presentation
