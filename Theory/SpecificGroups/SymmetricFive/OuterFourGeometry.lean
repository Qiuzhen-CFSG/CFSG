module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum

/-!
# A dihedral local for an outer four-group in S₅

Mark a Sylow two-subgroup by the permutations (01), (23), and (02)(13).
Its only elementary four-group containing odd permutations is
B = ⟨(01), (23)⟩, and C(S₅,B) = B. The subgroup
H = ⟨(01)(14)(23), (01)⟩ is an actual copy of DihedralGroup 6.
Its intersection with the marked Sylow is B, hence is Sylow in H.
The join of H and the Sylow contains all adjacent transpositions.

The finite checks concern eight Sylow words, twelve dihedral words and
individual five-point permutations, never the subgroup lattice. Sylow
conjugacy transports the marking to an arbitrary positioned outer actor.
This is the permutation geometry used for Aschbacher–Smith E.1.2(E1),
E.1.5 and E.1.14(7), pp.210–214, citing Aschbacher (1982), Lemma 4.11.
-/

public section

open Subgroup
namespace Theory.SpecificGroups.SymmetricFive.OuterFourGeometry
abbrev D := Equiv.Perm (Fin 5)
private def a : D := Equiv.swap 0 1
private def b : D := Equiv.swap 2 3
private def c : D := Equiv.swap 0 2 * Equiv.swap 1 3
private def word : Fin 8 → D := ![1, a, b, a*b, c, a*c, b*c, a*b*c]
def eight : Subgroup D where
  carrier := Set.range word
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    have hc : ∀ i j, ∃ k, word i * word j = word k := by decide +kernel
    rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hc i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    have hc : ∀ i, ∃ j, (word i)⁻¹ = word j := by decide +kernel
    rintro x ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hc i
    exact ⟨j, hj.symm⟩
private def rotation : D := a * Equiv.swap 1 4 * b
private def localPerm : DihedralGroup 6 → D
  | .r i => rotation ^ i.val
  | .sr i => a * rotation ^ i.val
private def localHom : DihedralGroup 6 →* D where
  toFun := localPerm
  map_one' := by decide +kernel
  map_mul' := by decide +kernel
private theorem localHom_injective : Function.Injective localHom := by decide +kernel

private def fourWord : Fin 4 → D := ![1, a, b, a*b]
def four : Subgroup D where
  carrier := Set.range fourWord
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    have hc : ∀ i j, ∃ k, fourWord i * fourWord j = fourWord k := by decide +kernel
    rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hc i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    have hc : ∀ i, (fourWord i)⁻¹ = fourWord i := by decide +kernel
    rintro x ⟨i, rfl⟩
    exact ⟨i, (hc i).symm⟩
theorem four_card : Nat.card four = 4 := by
  have hi : Function.Injective fourWord := by decide +kernel
  change Nat.card (Set.range fourWord) = 4
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  simp
theorem eight_card : Nat.card eight = 8 := by
  have hi : Function.Injective word := by decide +kernel
  change Nat.card (Set.range word) = 8
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  simp
@[expose] noncomputable def standardSylow : Sylow 2 D := Sylow.ofCard eight (by
  rw [eight_card, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num [Nat.factorial]
  decide +kernel)
theorem four_le_eight : four ≤ eight := by
  have hc : ∀ i, ∃ j, fourWord i = word j := by decide +kernel
  rintro x ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := hc i
  exact ⟨j, hj.symm⟩
instance four_elementary : IsElementaryAbelian 2 four where
  is_comm.comm x y := by
    have hc : ∀ i j, fourWord i * fourWord j = fourWord j * fourWord i := by decide +kernel
    apply Subtype.ext
    obtain ⟨i, hi⟩ := x.property
    obtain ⟨j, hj⟩ := y.property
    change (x : D) * (y : D) = (y : D) * (x : D)
    simpa only [hi, hj] using hc i j
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    have hc : ∀ i, (fourWord i)^2 = 1 := by decide +kernel
    intro x
    apply Subtype.ext
    obtain ⟨i, hi⟩ := x.property
    change (x : D)^2 = 1
    simpa only [hi] using hc i

theorem positioned_four_eq (B : Subgroup D) [IsElementaryAbelian 2 B]
    (hcard : Nat.card B = 4) (hB : B ≤ eight)
    (hout : ¬ B ≤ alternatingGroup (Fin 5)) : B = four := by
  classical
  have hc : ∀ i j, (word i)^2 = 1 → (word i).sign ≠ 1 →
      word j * word i = word i * word j → ∃ k, fourWord k = word j := by decide +kernel
  obtain ⟨x, hx, hxout⟩ := Set.not_subset.mp hout
  obtain ⟨i, hi⟩ := hB hx
  have hp : (word i)^2 = 1 := hi ▸ elemPow_eq_one_of_isElementaryAbelian x hx
  have hs : (word i).sign ≠ 1 := by
    intro h
    exact hxout (Equiv.Perm.mem_alternatingGroup.mpr (hi ▸ h))
  apply eq_of_le_of_card_ge
  · intro y hy
    obtain ⟨j, hj⟩ := hB hy
    have hcomm : y * x = x * y := congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : B) ⟨x, hx⟩)
    obtain ⟨k, hk⟩ := hc i j hp hs (by simpa only [hi, hj] using hcomm)
    exact ⟨k, hk.trans hj⟩
  · rw [hcard, four_card]

theorem four_centralizer : centralizer (four : Set D) = four := by
  have hc : ∀ x : D, a * x = x * a → b * x = x * b →
      ∃ k, fourWord k = x := by decide +kernel
  apply le_antisymm
  · intro x hx
    exact hc x ((mem_centralizer_iff.mp hx) a ⟨1, rfl⟩)
      ((mem_centralizer_iff.mp hx) b ⟨2, rfl⟩)
  · intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : four) ⟨x, hx⟩)

def localGroup : Subgroup D := localHom.range
noncomputable def localEquiv : localGroup ≃* DihedralGroup 6 :=
  (MonoidHom.ofInjective localHom_injective).symm
theorem local_card : Nat.card localGroup = 12 := by
  rw [Nat.card_congr localEquiv.toEquiv]
  exact DihedralGroup.nat_card

theorem four_le_local : four ≤ localGroup := by
  have hc : ∀ i, ∃ d : DihedralGroup 6, localHom d = fourWord i := by decide +kernel
  rintro x ⟨i, rfl⟩
  exact hc i

theorem eight_inf_local : eight ⊓ localGroup = four := by
  have hc : ∀ i (d : DihedralGroup 6), word i = localHom d →
      ∃ k, fourWord k = word i := by decide +kernel
  apply le_antisymm
  · rintro x ⟨⟨i, rfl⟩, d, hd⟩
    exact hc i d hd.symm
  · exact le_inf four_le_eight four_le_local

theorem local_sylow : ∃ S : Sylow 2 localGroup,
    (S : Subgroup localGroup) = eight.subgroupOf localGroup := by
  have he : eight.subgroupOf localGroup = four.subgroupOf localGroup := by
    apply (map_injective localGroup.subtype_injective)
    simp only [subgroupOf_map_subtype, eight_inf_local, inf_eq_left.mpr four_le_local]
  have hc : Nat.card (eight.subgroupOf localGroup) = 4 := by
    rw [he, Nat.card_congr (subgroupOfEquivOfLe four_le_local).toEquiv, four_card]
  exact ⟨Sylow.ofCard (eight.subgroupOf localGroup) (by rw [hc, local_card]; decide +kernel), rfl⟩

theorem local_sup_eight : localGroup ⊔ eight = ⊤ := by
  let M := localGroup ⊔ eight
  have ha : a ∈ M := (le_sup_right : eight ≤ M) ⟨1, rfl⟩
  have hb : b ∈ M := (le_sup_right : eight ≤ M) ⟨2, rfl⟩
  have hc : c ∈ M := (le_sup_right : eight ≤ M) ⟨4, rfl⟩
  have ht : Equiv.swap 1 4 ∈ M := by
    have hr : rotation ∈ M := (le_sup_left : localGroup ≤ M) ⟨.r 1, by decide +kernel⟩
    have he : a * rotation * b = Equiv.swap 1 4 := by decide +kernel
    rw [← he]
    exact M.mul_mem (M.mul_mem ha hr) hb
  have hu : Equiv.swap 3 4 ∈ M := by
    have he : c * Equiv.swap 1 4 * c⁻¹ = Equiv.swap 3 4 := by decide +kernel
    rw [← he]
    exact M.mul_mem (M.mul_mem hc ht) (M.inv_mem hc)
  have hv : Equiv.swap 1 2 ∈ M := by
    have he : Equiv.swap 1 4 * (b * Equiv.swap 3 4 * b) * Equiv.swap 1 4 =
        Equiv.swap 1 2 := by decide +kernel
    rw [← he]
    exact M.mul_mem (M.mul_mem ht (M.mul_mem (M.mul_mem hb hu) hb)) ht
  have hgen := Equiv.Perm.mclosure_swap_castSucc_succ 4
  apply Subgroup.toSubmonoid_injective
  apply top_unique
  rw [← hgen, Submonoid.closure_le]
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact ha
  · exact hv
  · exact hb
  · exact hu

/-- Simultaneously mark the Sylow subgroup and its outer four-group. -/
theorem exists_marking (S : Sylow 2 D) (B : Subgroup D)
    [IsElementaryAbelian 2 B] (hcard : Nat.card B = 4)
    (hBS : B ≤ (S : Subgroup D)) (hout : ¬ B ≤ alternatingGroup (Fin 5)) :
    ∃ e : D ≃* D, (S : Subgroup D).map e.toMonoidHom = eight ∧
      B.map e.toMonoidHom = four := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D S standardSylow
  let e := MulAut.conj g
  have hS : (S : Subgroup D).map e.toMonoidHom = eight := by
    have h := congrArg (fun Q : Sylow 2 D => (Q : Subgroup D)) hg
    exact h
  let : IsElementaryAbelian 2 (B.map e.toMonoidHom) := IsElementaryAbelian.map e.toMonoidHom
  have hB : B.map e.toMonoidHom ≤ eight := hS ▸ map_mono hBS
  have hn : ¬ B.map e.toMonoidHom ≤ alternatingGroup (Fin 5) := by
    intro h
    apply hout
    intro x hx
    have hs := Equiv.Perm.mem_alternatingGroup.mp (h (mem_map_of_mem e.toMonoidHom hx))
    apply Equiv.Perm.mem_alternatingGroup.mpr
    change (g * x * g⁻¹).sign = 1 at hs
    simpa only [map_mul, map_inv,
      mul_comm (Equiv.Perm.sign g) (Equiv.Perm.sign x), mul_inv_cancel_right] using hs
  refine ⟨e, hS, positioned_four_eq _ ?_ hB hn⟩
  rw [card_map_of_injective e.injective, hcard]

end Theory.SpecificGroups.SymmetricFive.OuterFourGeometry
