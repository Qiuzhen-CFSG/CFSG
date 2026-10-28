module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.Contracts

/-!
# Recovering the cyclic order from consecutive composition factors

Suppose every incident label starts an ordering of all labels, with a unique
successor whenever two adjacent pairs have the same first label. The first
successor in each ordering defines a surjection, hence a permutation. Every
ordering is its successive orbit, so the permutation is a single cycle.

This is the finite step of Feit VII.2.23, after the serial modules and the
no-branching conclusion of VII.8.2 have been proved. It uses no real-valency
bound or self-duality assumption. The final adapter retains the still-required
module construction, consecutive uniqueness and dual closure as explicit inputs.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules
open _root_.Equiv

private theorem cycle_of_words {A : Type*} [Finite A] {n : ℕ}
    (word : A → Fin (n + 1) ≃ A) (start : ∀ a, word a 0 = a)
    (coherent : ∀ a b (i j : Fin n), word a i.castSucc = word b j.castSucc →
      word a i.succ = word b j.succ) :
    ∃ σ : Perm A, σ.IsCycleOn Set.univ ∧
      ∀ a (i : Fin (n + 1)), (σ ^ i.val) a = word a i := by
  classical
  cases n with
  | zero =>
    have hsub : Subsingleton A := ⟨fun a b => by
      obtain ⟨i, rfl⟩ := (word a).surjective b
      have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
      simpa [hi] using (start a).symm⟩
    let := hsub
    refine ⟨1, Equiv.Perm.isCycleOn_of_subsingleton _ _, ?_⟩
    intro a i
    exact Subsingleton.elim _ _
  | succ n =>
    let next : A → A := fun a => word a 1
    have step (a : A) (i : Fin (n + 1)) : next (word a i.castSucc) = word a i.succ := by
      exact (coherent a (word a i.castSucc) i 0 (by simp [start])).symm
    have hsurj : Function.Surjective next := by
      intro a
      let b := word a 1
      have hba : b ≠ a := by
        intro h
        have h' : word a 1 = word a 0 := h.trans (start a).symm
        have hval := congrArg Fin.val ((word a).injective h')
        simp at hval
      let i := (word b).symm a
      have hi : i ≠ 0 := by
        intro h
        have : b = a := by simpa [i, h, start] using (word b).apply_symm_apply a
        exact hba this
      have hpos : 0 < i.val := by
        by_contra h
        exact hi (Fin.ext (by change i.val = 0; omega))
      let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      refine ⟨word b j.castSucc, ?_⟩
      rw [step, hj]
      exact (word b).apply_symm_apply a
    let σ : Perm A := Equiv.ofBijective next
      ⟨(Finite.injective_iff_surjective).mpr hsurj, hsurj⟩
    have hp (a : A) (i : Fin (n + 1 + 1)) : (σ ^ i.val) a = word a i := by
      induction i using Fin.induction with
      | zero => simpa using (start a).symm
      | succ i ih =>
        change (σ ^ (i.val + 1)) a = _
        simp only [Fin.val_castSucc] at ih
        rw [pow_succ', Perm.mul_apply, ih]
        exact step a i
    refine ⟨σ, ⟨σ.bijective.bijOn_univ, ?_⟩, hp⟩
    intro a _ b _
    obtain ⟨i, rfl⟩ := (word a).surjective b
    exact ⟨(i.val : ℤ), by rw [zpow_natCast, hp]⟩

/-- Consistent adjacent factors in a full family of linear orderings determine
one common cyclic successor. This includes empty and singleton label sets. -/
theorem exists_cycle_of_consecutive_unique {A : Type*} [Finite A] {s : ℕ}
    (word : A → Fin s ≃ A)
    (start : ∀ a (h : 0 < s), word a ⟨0, h⟩ = a)
    (coherent : ∀ a b (i j : Fin s) (hi : i.val + 1 < s) (hj : j.val + 1 < s),
      word a i = word b j → word a ⟨i.val + 1, hi⟩ = word b ⟨j.val + 1, hj⟩) :
    ∃ σ : Perm A, σ.IsCycleOn Set.univ ∧ ∀ a (i : Fin s), (σ ^ i.val) a = word a i := by
  cases s with
  | zero =>
    let : IsEmpty A := ⟨fun a => Fin.elim0 ((word a).symm a)⟩
    exact ⟨1, Equiv.Perm.isCycleOn_of_subsingleton _ _, fun _ i => Fin.elim0 i⟩
  | succ n =>
    exact cycle_of_words word (fun a => start a (Nat.succ_pos n))
      (fun a b i j h => coherent a b i.castSucc j.castSucc
        (Nat.succ_lt_succ i.isLt) (Nat.succ_lt_succ j.isLt) h)

open ModularBlock.PrimeBlockConstruction
variable {p : ℕ} {G : Type*} [Group G] [Finite G]
    {d : PrimeCongruenceBlockData p G} {K : Type*} [Field K] {m n : ℕ}
    {L : CyclicRootLift K m} {t : Tree d.chi d.block p n L}
    {r : CompatibleRoots d K m} {v : {i // i ∈ d.block}}

/-- Assemble the common cycle after the source module and dual-closure
obligations have been discharged. This is a conditional construction. -/
def cyclicVertexFamilyOfSeries (a : VertexSeries t r v) (hc : a.ConsecutiveUnique)
    (hd : ∀ e, ∃ f, Nonempty (((a.lattice e).reduction r).dual.Equiv
      ((a.lattice f).reduction r))) : CyclicVertexFamily t r v := by
  let h := exists_cycle_of_consecutive_unique a.ordering a.first hc
  exact {
    toVertexSeries := a
    successor := h.choose
    cyclic := h.choose_spec.1
    powers := h.choose_spec.2
    dual_closed := hd }

/-- The successive quotients use the powers of the common successor, on the
literal incident-edge subtype. -/
theorem CyclicVertexFamily.factor_equiv_pow (a : CyclicVertexFamily t r v)
    (e : ↥(t.incident v)) (i : Fin (t.incident v).card) :
    Nonempty (((a.series e).factor i).Equiv (t.rep ((a.successor ^ i.val) e).val)) := by
  rw [a.powers]
  exact a.factor_equiv e i

end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules
