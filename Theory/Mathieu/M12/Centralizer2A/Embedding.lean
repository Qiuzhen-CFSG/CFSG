module

public import Theory.Mathieu.M12.Centralizer2A.Coordinates
public import Theory.Mathieu.M12.Centralizer2A.Representative
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Finite.Perm

/-!
# A concrete C₂ × S₅ in the M₁₂ 2A centralizer

Words in the standard M₁₂ generators certify membership of the transposition
lifts. The central generator is exactly `m12Involution2A`. Consequently the
faithful product action embeds in its literal centralizer and proves the lower
bound 240. The final equivalence here still explicitly requires the matching
upper bound; exhaustion of the centralizer is a separate geometric obligation.

Source: Aschbacher–Smith 16.1.5(4), printed p.1171, with the ATLAS representative
specified in `Properties.InvolutionClasses`. No order or simplicity assertion
about a merely labelled group is used.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12Centralizer2A
set_option maxRecDepth 10000

def swapPoint : Fin 5 → Fin 5 → Fin 12 → Fin 12 := ![![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], ![8, 3, 5, 1, 10, 2, 9, 11, 0, 6, 4, 7], ![1, 0, 4, 6, 2, 11, 3, 10, 9, 8, 7, 5], ![6, 8, 7, 9, 5, 4, 0, 2, 1, 3, 11, 10], ![9, 6, 11, 8, 7, 10, 1, 4, 3, 0, 5, 2]], ![![8, 3, 5, 1, 10, 2, 9, 11, 0, 6, 4, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], ![6, 9, 7, 8, 11, 10, 0, 2, 3, 1, 5, 4], ![3, 6, 10, 0, 7, 11, 1, 4, 9, 8, 2, 5], ![1, 0, 4, 9, 2, 7, 8, 5, 6, 3, 11, 10]], ![![1, 0, 4, 6, 2, 11, 3, 10, 9, 8, 7, 5], ![6, 9, 7, 8, 11, 10, 0, 2, 3, 1, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], ![9, 3, 11, 1, 10, 7, 8, 5, 6, 0, 4, 2], ![3, 8, 10, 0, 5, 4, 9, 11, 1, 6, 2, 7]], ![![6, 8, 7, 9, 5, 4, 0, 2, 1, 3, 11, 10], ![3, 6, 10, 0, 7, 11, 1, 4, 9, 8, 2, 5], ![9, 3, 11, 1, 10, 7, 8, 5, 6, 0, 4, 2], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], ![8, 9, 5, 6, 11, 2, 3, 10, 0, 1, 7, 4]], ![![9, 6, 11, 8, 7, 10, 1, 4, 3, 0, 5, 2], ![1, 0, 4, 9, 2, 7, 8, 5, 6, 3, 11, 10], ![3, 8, 10, 0, 5, 4, 9, 11, 1, 6, 2, 7], ![8, 9, 5, 6, 11, 2, 3, 10, 0, 1, 7, 4], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]]

def swapWord : Fin 5 → Fin 5 → List Bool := ![![[], [true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false], [false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false], [true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true], [true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true]], ![[true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false], [], [false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false], [false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true], [true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false]], ![[false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false], [false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false], [], [true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true], [false, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true]], ![[true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true], [false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true], [true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true], [], [false, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false]], ![[true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true], [true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false], [false, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true], [false, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false], []]]

def swapPerm (a b : Fin 5) : Equiv.Perm (Fin 12) where
  toFun := swapPoint a b
  invFun := swapPoint a b
  left_inv := (by decide +kernel : ∀ a b x, swapPoint a b (swapPoint a b x) = x) a b
  right_inv := (by decide +kernel : ∀ a b x, swapPoint a b (swapPoint a b x) = x) a b

theorem representation_swap (a b : Fin 5) :
    representation (1, Equiv.swap a b) = swapPerm a b := by
  apply Equiv.ext
  intro x
  obtain ⟨p,rfl⟩ := pointEquiv.surjective x
  rw [representation_apply, one_mul, sixAction_swap]
  exact (by decide +kernel : ∀ a b p,
    pointEquiv (p.1, swapIndex a b p.2) = swapPerm a b (pointEquiv p)) a b p

def wordPerm : List Bool → Equiv.Perm (Fin 12)
  | [] => 1
  | b :: bs => (if b then m12GeneratorB else m12GeneratorA) * wordPerm bs

theorem wordPerm_mem (bs : List Bool) : wordPerm bs ∈ M12 := by
  induction bs with
  | nil => exact M12.one_mem
  | cons b bs ih =>
    cases b with
    | false => exact M12.mul_mem m12GeneratorA_mem ih
    | true => exact M12.mul_mem m12GeneratorB_mem ih

theorem swapPerm_mem (a b : Fin 5) : swapPerm a b ∈ M12 := by
  have h : ∀ a b, swapPerm a b = wordPerm (swapWord a b) := by decide +kernel
  rw [h]
  exact wordPerm_mem _

def twoAction : C2 →* Equiv.Perm (Fin 12) :=
  pointEquiv.permCongrHom.toMonoidHom.comp
    (pairAction.comp ((MonoidHom.id C2).prod (1 : C2 →* Equiv.Perm (Fin 6))))

theorem representation_two (c : C2) : representation (c,1) = twoAction c := by
  change pointEquiv.permCongrHom (pairAction (c,sixAction 1)) =
    pointEquiv.permCongrHom (pairAction (c,1))
  rw [map_one]

theorem twoAction_eq (c : C2) : twoAction c =
    if c = 1 then 1 else (m12Involution2A : Equiv.Perm (Fin 12)) := by
  revert c
  rw [representative_coe]
  decide +kernel

theorem representation_mem (p : C2 × Equiv.Perm (Fin 5)) : representation p ∈ M12 := by
  have hS (s : Equiv.Perm (Fin 5)) : representation (1,s) ∈ M12 := by
    induction s using Equiv.Perm.swap_induction_on with
    | one =>
      change representation 1 ∈ M12
      rw [map_one]
      exact M12.one_mem
    | swap_mul s a b _ ih =>
      have hm := M12.mul_mem (swapPerm_mem a b) ih
      rw [← representation_swap a b, ← map_mul] at hm
      simpa only [Prod.mk_mul_mk, one_mul] using hm
  have hC (c : C2) : representation (c,1) ∈ M12 := by
    rw [representation_two, twoAction_eq]
    split
    · exact M12.one_mem
    · exact m12Involution2A.property
  obtain ⟨c,s⟩ := p
  have hp : (c,s) = (c,1)*(1,s) := by simp
  rw [hp, map_mul]
  exact M12.mul_mem (hC c) (hS s)

noncomputable def intoM12 : C2 × Equiv.Perm (Fin 5) →* M12 :=
  representation.codRestrict M12 representation_mem

theorem intoM12_injective : Function.Injective intoM12 := by
  intro p q hpq
  exact representation_injective (congrArg Subtype.val hpq)

theorem intoM12_two : intoM12 (Multiplicative.ofAdd 1,1) = m12Involution2A := by
  apply Subtype.ext
  change representation (Multiplicative.ofAdd 1,1) = _
  rw [representation_two, twoAction_eq, if_neg (by decide +kernel)]

noncomputable abbrev centralizer := Subgroup.centralizer ({m12Involution2A} : Set M12)

theorem intoM12_mem_centralizer (p : C2 × Equiv.Perm (Fin 5)) : intoM12 p ∈ centralizer := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  rw [← intoM12_two, ← map_mul, ← map_mul]
  congr 1
  exact Prod.ext (mul_comm _ _) (by simp)

noncomputable def embedding : C2 × Equiv.Perm (Fin 5) →* centralizer :=
  intoM12.codRestrict centralizer intoM12_mem_centralizer

theorem embedding_injective : Function.Injective embedding := by
  intro p q hpq
  exact intoM12_injective (congrArg Subtype.val hpq)

theorem card_product : Nat.card (C2 × Equiv.Perm (Fin 5)) = 240 := by
  rw [Nat.card_prod, Nat.card_perm, Nat.card_fin]
  have h : Nat.card C2 = 2 := by exact Nat.card_zmod 2
  rw [h]
  decide +kernel

theorem card_centralizer_ge : 240 ≤ Nat.card centralizer := by
  rw [← card_product]
  exact Nat.card_le_card_of_injective embedding embedding_injective

noncomputable def centralizerEquivOfCardLe (h : Nat.card centralizer ≤ 240) :
    centralizer ≃* C2 × Equiv.Perm (Fin 5) :=
  (MulEquiv.ofBijective embedding
    (embedding_injective.bijective_of_nat_card_le (by simpa only [card_product] using h))).symm

end Sporadic.Mathieu.M12Centralizer2A
