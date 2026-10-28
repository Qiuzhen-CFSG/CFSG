module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.Coordinates
public import Theory.GroupAction.IndexTwoFixedCard

/-!
# Faithfulness forced by a two-element Sylow fixed space

Every nontrivial normal subgroup of S₄ contains its normal four-group. For
this small symmetric group, explicit products of conjugates prove that fact.
The four-group has index two inside any Sylow two-subgroup. Consequently a
nonfaithful binary action restricts to a Sylow action trivial on an index-two
subgroup; the elementary fixed/displacement bound then gives at least four
fixed vectors on the group of order sixteen.

This proves faithfulness from the supplied Sylow fixed order two, without any
complement or extension hypothesis. It is a preliminary reduction for the
finite action classification used in Huppert–Blackburn, *Finite Groups III*,
XII.1.18(b), p.314, not the classification itself.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
open LocalModelDichotomy
open Equiv

private abbrev doubleSwap : SymmetricFour := doubleTransposition
private def kleinSet (g : SymmetricFour) : Prop :=
  g = 1 ∨ g = doubleSwap ∨
    g = Equiv.swap 0 2 * Equiv.swap 1 3 ∨ g = Equiv.swap 0 3 * Equiv.swap 1 2
private instance (g : SymmetricFour) : Decidable (kleinSet g) := inferInstanceAs (Decidable (_ ∨ _))
private def klein : Subgroup SymmetricFour where
  carrier := {g | kleinSet g}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have h : ∀ x y, kleinSet x → kleinSet y → kleinSet (x * y) := by decide +kernel
    exact h
  inv_mem' := by
    have h : ∀ x, kleinSet x → kleinSet x⁻¹ := by decide +kernel
    exact h
private instance : klein.Normal where
  conj_mem := by
    have h : ∀ n, kleinSet n → ∀ g, kleinSet (g * n * g⁻¹) := by decide +kernel
    exact h
private theorem klein_card : Nat.card klein = 4 := by
  change Nat.card {g : SymmetricFour // kleinSet g} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 10000 in
private theorem doubleSwap_in_normal (N : Subgroup SymmetricFour) [N.Normal]
    {g : SymmetricFour} (hg : g ≠ 1) (hgn : g ∈ N) : doubleSwap ∈ N := by
  have h : ∀ g : SymmetricFour, g ≠ 1 → ∃ a b : SymmetricFour,
      doubleSwap = a * g * a⁻¹ ∨
      doubleSwap = (a * g * a⁻¹) * (b * g * b⁻¹) := by decide +kernel
  obtain ⟨a, b, ha | hab⟩ := h g hg
  · rw [ha]
    exact (inferInstance : N.Normal).conj_mem g hgn a
  · rw [hab]
    exact N.mul_mem ((inferInstance : N.Normal).conj_mem g hgn a) ((inferInstance : N.Normal).conj_mem g hgn b)

private theorem klein_le_normal (N : Subgroup SymmetricFour) [N.Normal]
    {g : SymmetricFour} (hg : g ≠ 1) (hgn : g ∈ N) : klein ≤ N := by
  have hd := doubleSwap_in_normal N hg hgn
  have h : ∀ v : SymmetricFour, kleinSet v →
      v = 1 ∨ ∃ a : SymmetricFour, v = a * doubleSwap * a⁻¹ := by decide +kernel
  intro v hv
  rcases h v hv with rfl | ⟨a, rfl⟩
  · exact N.one_mem
  · exact (inferInstance : N.Normal).conj_mem _ hd a

private theorem sylow_card (P : Sylow 2 SymmetricFour) : Nat.card P = 8 := by
  rw [P.card_eq_multiplicity]
  have h : Nat.card SymmetricFour = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  rw [h]
  have hf : Nat.factorization 24 2 = 3 := by decide +kernel
  rw [hf]
  rfl

private theorem klein_index (P : Sylow 2 SymmetricFour) :
    (klein.subgroupOf P).index = 2 := by
  have hle : klein ≤ P := (IsPGroup.of_card (p := 2) (n := 2) klein_card).le_sylow_of_normal P
  have hcard : Nat.card (klein.subgroupOf P) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans klein_card
  have h := (klein.subgroupOf P).card_mul_index
  rw [hcard, sylow_card] at h
  omega

/-- The Sylow fixed order two excludes every nontrivial kernel. -/
public theorem action_injective_of_sylow_fixed_card
    (α : SymmetricFour →* MulAut BinaryFour) (P : Sylow 2 SymmetricFour)
    (hP : Nat.card {v : BinaryFour // ∀ s : P, α (s : SymmetricFour) v = v} = 2) :
    Function.Injective α := by
  apply α.ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro g hg
  change g = 1
  by_contra hne
  have hklein : klein ≤ α.ker := klein_le_normal α.ker hne hg
  let : MulDistribMulAction P BinaryFour :=
    MulDistribMulAction.compHom BinaryFour (α.comp (P : Subgroup SymmetricFour).subtype)
  let : IsElementaryAbelian 2 BinaryFour := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      change ∀ v : BinaryFour, v ^ 2 = 1
      decide +kernel) }
  have hbound := card_le_fixed_card_sq_of_index_two_kernel
    (V := BinaryFour) (klein.subgroupOf P) (klein_index P) (by
      intro n hn v
      change α (n : SymmetricFour) v = v
      have h : α (n : SymmetricFour) = 1 := hklein hn
      rw [h]
      rfl)
  have hcard : Nat.card BinaryFour = 16 := by
    rw [Nat.card_eq_fintype_card]
    decide
  change Nat.card BinaryFour ≤
    Nat.card {v : BinaryFour // ∀ s : P, α (s : SymmetricFour) v = v} ^ 2 at hbound
  rw [hcard, hP] at hbound
  norm_num at hbound

/-- The full fixed order two supplies a nonidentity fixed vector. -/
public theorem exists_nonidentity_fixed
    (α : SymmetricFour →* MulAut BinaryFour)
    (hfixed : Nat.card {v : BinaryFour // ∀ s : SymmetricFour, α s v = v} = 2) :
    ∃ v : BinaryFour, v ≠ 1 ∧ ∀ s : SymmetricFour, α s v = v := by
  let oneFixed : {v : BinaryFour // ∀ s : SymmetricFour, α s v = v} :=
    ⟨1, fun s => (α s).map_one⟩
  obtain ⟨v, hv, _⟩ := (Nat.card_eq_two_iff' oneFixed).mp hfixed
  exact ⟨v, fun h => hv (Subtype.ext h), v.property⟩

/-- The three-cycle acts nontrivially under the Sylow fixed order hypothesis. -/
public theorem threeCycle_action_ne_one
    (α : SymmetricFour →* MulAut BinaryFour) (P : Sylow 2 SymmetricFour)
    (hP : Nat.card {v : BinaryFour // ∀ s : P, α (s : SymmetricFour) v = v} = 2) :
    α threeCycle ≠ 1 := by
  intro h
  apply threeCycle_ne_one
  exact action_injective_of_sylow_fixed_card α P hP (h.trans α.map_one.symm)

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
