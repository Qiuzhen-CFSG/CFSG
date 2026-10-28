module

public import Theory.GroupTheory.PairedProduct
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Group

/-!
# The lattice above a product of pair diagonals

For a nonabelian simple group `S`, the product of the diagonals in `I → S × S`
is self-normalizing. Any strictly larger subgroup contains a full pair factor.
Consequently, an action transitive on the actual pair factors makes an invariant
paired diagonal maximal among proper invariant subgroups, when `I` is finite
and nonempty.

To localize an element with unequal entries, first multiply by a diagonal to
make all second entries trivial, then commute with a diagonal supported at the
chosen coordinate. The subgroup of first entries supported there is normal in
`S`. Simplicity and centerlessness force it to be all of `S`, and the diagonal
supplies the second entries. This avoids a general subdirect-product theorem.

Source: the paired case of GLS2, Chapter B, Lemma 3.25, as used in Chapter G,
Theorem 25.14, Step 2. Simplicity and perfectness express nonabelian simplicity;
finiteness of `S` is not needed for this argument.
-/

public section

open scoped commutatorElement

namespace Subgroup.PairedProduct
variable {I S : Type*} [Group S]

private lemma simple_center [IsSimpleGroup S] [Group.IsPerfect S] : center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) inferInstance with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp h)).elim

private lemma eq_of_conjugation_eq (hz : center S = ⊥) {a b : S}
    (h : ∀ s : S, a * s * a⁻¹ = b * s * b⁻¹) : a = b := by
  have hc : b⁻¹ * a ∈ center S := mem_center_iff.mpr fun s => by
    calc
      s * (b⁻¹ * a) = b⁻¹ * (b * s * b⁻¹) * a := by group
      _ = b⁻¹ * (a * s * a⁻¹) * a := by rw [h s]
      _ = b⁻¹ * a * s := by group
  rw [hz, mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

/-- The product of pair diagonals is self-normalizing. -/
theorem normalizer_diagonal [IsSimpleGroup S] [Group.IsPerfect S] :
    normalizer (diagonal I S : Set (I → S × S)) = diagonal I S := by
  apply le_antisymm ?_ (diagonal I S).le_normalizer
  intro x hx i
  apply eq_of_conjugation_eq simple_center
  intro s
  exact (mem_normalizer_iff.mp hx (fun _ => (s, s))).mp (fun _ => rfl) i

private lemma single_diagonal [DecidableEq I] (i : I) (s : S) :
    Pi.mulSingle i (s, s) ∈ diagonal I S := by
  intro j
  by_cases hj : j = i
  · subst j; simp
  · simp [Pi.mulSingle_eq_of_ne hj]

/-- An unequal coordinate in an overgroup of the diagonal forces the whole
pair at that coordinate into the overgroup. -/
theorem factor_le_of_unequal [IsSimpleGroup S] [Group.IsPerfect S]
    {M : Subgroup (I → S × S)} (hD : diagonal I S ≤ M)
    {x : I → S × S} (hx : x ∈ M) {i : I} (hi : (x i).1 ≠ (x i).2) :
    factor I S i ≤ M := by
  classical
  let N : Subgroup S := M.comap
    ((MonoidHom.mulSingle (fun _ : I => S × S) i).comp (MonoidHom.inl S S))
  have hNmem (s : S) : s ∈ N ↔ Pi.mulSingle i (s, 1) ∈ M := Iff.rfl
  have hNnormal : N.Normal := by
    constructor
    intro s hs g
    rw [hNmem] at hs ⊢
    have hd := hD (single_diagonal i g)
    convert M.mul_mem (M.mul_mem hd hs) (M.inv_mem hd) using 1
    ext j <;> by_cases hj : j = i <;> simp [hj, Pi.mulSingle_eq_of_ne]
  have hNtop : N = ⊤ := by
    rcases hNnormal.eq_bot_or_eq_top with hN | hN
    · let y : I → S × S := fun j => ((x j).1 * (x j).2⁻¹, 1)
      have hy : y ∈ M := by
        have hd : (fun j => ((x j).2, (x j).2)) ∈ M := hD (fun _ => rfl)
        convert M.mul_mem hx (M.inv_mem hd) using 1
        ext j <;> simp [y]
      have hc : (x i).1 * (x i).2⁻¹ ∈ center S := by
        apply mem_center_iff.mpr
        intro s
        have hd := hD (single_diagonal i s)
        have hm : ⁅(x i).1 * (x i).2⁻¹, s⁆ ∈ N := by
          rw [hNmem]
          convert M.mul_mem (M.mul_mem (M.mul_mem hy hd) (M.inv_mem hy))
            (M.inv_mem hd) using 1
          ext j <;> by_cases hj : j = i <;>
              simp [hj, Pi.mulSingle_eq_of_ne, y, commutatorElement_def]
        rw [hN, mem_bot] at hm
        exact (commutatorElement_eq_one_iff_mul_comm.mp hm).symm
      rw [simple_center, mem_bot] at hc
      exact (hi (mul_inv_eq_one.mp hc)).elim
    · exact hN
  intro z hz
  have hleft : Pi.mulSingle i ((z i).1 * (z i).2⁻¹, 1) ∈ M :=
    (hNmem _).mp (hNtop ▸ mem_top _)
  have hdiag := hD (single_diagonal i (z i).2)
  convert M.mul_mem hleft hdiag using 1
  ext j <;>
    by_cases hj : j = i
  · subst j; simp [mul_assoc]
  · have hzj := hz j hj
    simp [Pi.mulSingle_eq_of_ne hj, hzj]
  · subst j; simp
  · have hzj := hz j hj
    simp [Pi.mulSingle_eq_of_ne hj, hzj]

/-- Every strict overgroup of the paired diagonal contains a full pair factor. -/
theorem exists_factor_le [IsSimpleGroup S] [Group.IsPerfect S]
    {M : Subgroup (I → S × S)} (hD : diagonal I S ≤ M)
    (hne : M ≠ diagonal I S) : ∃ i, factor I S i ≤ M := by
  classical
  have hnot : ¬ M ≤ diagonal I S := fun h => hne (le_antisymm h hD)
  obtain ⟨x, hx, hxd⟩ := SetLike.not_le_iff_exists.mp hnot
  change ¬ ∀ i, (x i).1 = (x i).2 at hxd
  push Not at hxd
  obtain ⟨i, hi⟩ := hxd
  exact ⟨i, factor_le_of_unequal hD hx hi⟩

/-- Transitivity on pair factors leaves no proper invariant intermediate
subgroup strictly above the diagonal. -/
theorem eq_diagonal_or_eq_top [Finite I] [IsSimpleGroup S] [Group.IsPerfect S]
    {A : Type*} [Group A] {α : A →* MulAut (I → S × S)}
    (htrans : IsPairTransitive I S α) {M : Subgroup (I → S × S)}
    (hD : diagonal I S ≤ M)
    (hM : ∀ b, M.map (α b).toMonoidHom = M) : M = diagonal I S ∨ M = ⊤ := by
  classical
  by_cases he : M = diagonal I S
  · exact Or.inl he
  right
  obtain ⟨i, hi⟩ := exists_factor_le hD he
  have hfactor (j : I) : factor I S j ≤ M := by
    obtain ⟨b, hb⟩ := htrans i j
    rw [← hb, ← hM b]
    exact map_mono hi
  apply top_unique
  intro x _
  apply pi_mem_of_mulSingle_mem
  intro j
  apply hfactor j
  intro k hk
  exact Pi.mulSingle_eq_of_ne hk _

/-- With at least one pair and a nontrivial factor, the paired diagonal is proper. -/
theorem diagonal_ne_top [Nonempty I] [Nontrivial S] : diagonal I S ≠ ⊤ := by
  intro he
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  have hm : (fun _ : I => (s, 1)) ∈ diagonal I S := he ▸ mem_top _
  exact hs (hm (Classical.choice ‹Nonempty I›))

/-- An invariant paired diagonal is maximal among proper invariant subgroups
under any action transitive on the full pair factors. -/
theorem diagonal_maximal_invariant [Finite I] [Nonempty I]
    [IsSimpleGroup S] [Group.IsPerfect S]
    {A : Type*} [Group A] {α : A →* MulAut (I → S × S)}
    (htrans : IsPairTransitive I S α)
    (hdiag : ∀ b, (diagonal I S).map (α b).toMonoidHom = diagonal I S) :
    Maximal (fun M : Subgroup (I → S × S) =>
      M ≠ ⊤ ∧ ∀ b, M.map (α b).toMonoidHom = M) (diagonal I S) := by
  refine ⟨⟨diagonal_ne_top, hdiag⟩, ?_⟩
  intro M hM hD
  rcases eq_diagonal_or_eq_top htrans hD hM.2 with he | he
  · exact he.le
  · exact (hM.1 he).elim

end Subgroup.PairedProduct

end
