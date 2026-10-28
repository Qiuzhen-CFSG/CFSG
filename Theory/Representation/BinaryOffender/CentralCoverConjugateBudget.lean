module

public import Theory.Representation.BinaryOffender.ElementaryConjugateBudget
public import Theory.Representation.BinaryOffender.CubicConjugateBound
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PerfectNormalizerLift
public import Theory.Representation.Quotient

/-!
# Elementary conjugate generation through a central cover

A generating family of conjugates in a quotient lifts to its perfect central
cover. An odd kernel preserves the ranks of elementary two-subgroups. The
intersection of the corresponding fixed spaces then bounds the binary module
degree by the cubic-ratio bound times the conjugate-generation budget.

This keeps the quotient map, central kernel and actual conjugating elements;
no faithful action of the quotient on the original module is asserted.

Source: the fixed-space inequalities (2.5)--(2.6) in Guralnick--Malle,
*Classification of 2F-modules I*, applied to Aschbacher--Smith K.1,
printed p.452. Concrete generation budgets are separate group-theoretic facts.
-/

@[expose] public section
open Subgroup
namespace Representation.BinaryOffender

/-- A bound on the number of generating conjugates times the elementary rank. -/
def ElementaryConjugateBudget (S : Type*) [Group S] (b : ℕ) : Prop :=
  ∀ A : Subgroup S, IsElementaryTwo A →
    ∃ (n : ℕ) (c : Fin n → S), n * rank A ≤ b ∧
      (⨆ i, A.map (MulAut.conj (c i)).toMonoidHom) = ⊤

variable {G S V : Type*} [Group G] [Finite G] [Group S]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Lift generating conjugates through the actual odd central kernel and bound degree. -/
theorem finrank_le_of_cubicRatio_of_central_cover [Group.IsPerfect G] [Nontrivial G]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ) (q : G →* S) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ center G) (hodd : Nat.Coprime 2 (Nat.card q.ker))
    {a b : ℕ} (hbudget : ElementaryConjugateBudget S b)
    (hsmall : cubicRatio ρ ≤ a) : Module.finrank (ZMod 2) V ≤ a * b := by
  classical
  obtain ⟨A, hA, _, hcodim⟩ := (cubicRatio_le_nat_iff ρ a).mp hsmall
  let : IsElementaryAbelian 2 A := hA.2
  have hqA := injective_comp_subtype_of_coprime_ker q hodd A
    (IsElementaryAbelian.isPGroup 2 A)
  let e : A ≃* A.map q := MulEquiv.ofBijective (q.subgroupMap A)
    ⟨fun x y h => hqA (congrArg Subtype.val h), q.subgroupMap_surjective A⟩
  have hB : IsElementaryTwo (A.map q) := by
    refine ⟨?_, IsElementaryAbelian.map q⟩
    intro hz
    have hc := Nat.card_congr e.toEquiv
    rw [hz, Subgroup.card_bot] at hc
    exact hA.1 (eq_bot_of_card_eq A hc)
  have hr : rank (A.map q) = rank A := by
    unfold rank
    rw [Nat.card_congr e.toEquiv]
  obtain ⟨n, c, hn, hc⟩ := hbudget (A.map q) hB
  choose d hd using fun i => hq (c i)
  let J := ⨆ i, A.map (MulAut.conj (d i)).toMonoidHom
  have hJ : J = ⊤ := by
    apply top_unique
    apply le_of_map_le_of_perfect q hcentral
    have he : J.map q = ⨆ i, (A.map q).map (MulAut.conj (c i)).toMonoidHom := by
      rw [Subgroup.map_iSup]
      apply iSup_congr
      intro i
      rw [map_map, map_map]
      congr 1
      ext x
      change q (d i * x * (d i)⁻¹) = c i * q x * (c i)⁻¹
      rw [map_mul, map_mul, map_inv, hd]
    rw [he, hc]
    exact le_top
  have hfix : fixedSpace ρ ⊤ = ⊥ := by
    let := hi
    exact fixedSpace_eq_bot_of_faithful_irreducible_on ρ ⊤ hf
      ((irreducible_comp_surjective_iff (⊤ : Subgroup G).subtype
        (fun g => ⟨⟨g, mem_top _⟩, rfl⟩) ρ).mpr hi)
  have hdim := finrank_le_mul_fixedCodim_of_subgroup_conjugates ρ ⊤ A hfix d hJ.ge
  rw [hr] at hn
  calc
    Module.finrank (ZMod 2) V ≤ n * fixedCodim ρ A := hdim
    _ ≤ n * (a * rank A) := Nat.mul_le_mul_left n hcodim
    _ = a * (n * rank A) := by ac_rfl
    _ ≤ a * b := Nat.mul_le_mul_left a hn

end Representation.BinaryOffender
