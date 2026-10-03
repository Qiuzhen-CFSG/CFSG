module
public import Theory.GroupAction.Quadratic
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Data.Set.Card

/-!
# Quadratic actors preserve a complementary pair individually

A faithful elementary abelian two-group with more than two elements acts
quadratically on an abelian group. If its action permutes two complementary
subgroups, every actor preserves each subgroup individually. Neither the
summand orders nor an irreducibility hypothesis are needed.

If an actor swaps the two summands, any actor preserving them has its
first-summand displacements fixed by the swap, by quadraticity. These
therefore lie in the intersection of the summands and vanish. The same
holds for the second summand, so faithfulness makes that actor trivial.
Any other swapping actor differs from the first by such a trivial actor.
There would be at most two actors, contradicting the cardinality hypothesis.

This elementary observation supplies stability of the intrinsic support
lines of the chief module in Stellmacher (9.1), printed p48 of
`refs/files/stellmacher-n-group.pdf`, before selection of the order-three
subgroup D*. It uses the supplied action throughout.
-/

open scoped IsMulCommutative

public theorem quadratic_actor_preserves_complementary_pair
    {A V : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group V] [IsMulCommutative V] [MulDistribMulAction A V]
    (hfaith : fixingSubgroup A (Set.univ : Set V) = ⊥)
    (hcard : 2 < Nat.card A) (hquad : commutatorAction₂ A V = ⊥)
    (P Q : Subgroup V) (hcompl : IsCompl P Q)
    (hperm : ∀ a : A,
      ((∀ v ∈ P, a • v ∈ P) ∧ (∀ v ∈ Q, a • v ∈ Q)) ∨
      ((∀ v ∈ P, a • v ∈ Q) ∧ (∀ v ∈ Q, a • v ∈ P))) :
    ∀ a : A, (∀ v ∈ P, a • v ∈ P) ∧ (∀ v ∈ Q, a • v ∈ Q) := by
  intro a
  rcases hperm a with hstable | hswap
  · exact hstable
  exfalso
  have hfixed := commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hquad
  have stable_trivial (b : A)
      (hbP : ∀ v ∈ P, b • v ∈ P) (hbQ : ∀ v ∈ Q, b • v ∈ Q) : b = 1 := by
    have hPfix (v : V) (hv : v ∈ P) : b • v = v := by
      let delta := v⁻¹ * (b • v)
      have hdeltaP : delta ∈ P := P.mul_mem (P.inv_mem hv) (hbP v hv)
      have hdeltaComm : delta ∈ commutatorAction A V := by
        exact Subgroup.subset_closure ⟨b, v, Subgroup.mem_top v, rfl⟩
      have hdeltaFix : a • delta = delta := hfixed hdeltaComm a
      have hdeltaQ : delta ∈ Q := hdeltaFix ▸ hswap.1 delta hdeltaP
      have hone : delta = 1 := hcompl.disjoint.le_bot ⟨hdeltaP, hdeltaQ⟩
      exact (inv_mul_eq_one.mp hone).symm
    have hQfix (v : V) (hv : v ∈ Q) : b • v = v := by
      let delta := v⁻¹ * (b • v)
      have hdeltaQ : delta ∈ Q := Q.mul_mem (Q.inv_mem hv) (hbQ v hv)
      have hdeltaComm : delta ∈ commutatorAction A V := by
        exact Subgroup.subset_closure ⟨b, v, Subgroup.mem_top v, rfl⟩
      have hdeltaFix : a • delta = delta := hfixed hdeltaComm a
      have hdeltaP : delta ∈ P := hdeltaFix ▸ hswap.2 delta hdeltaQ
      have hone : delta = 1 := hcompl.disjoint.le_bot ⟨hdeltaP, hdeltaQ⟩
      exact (inv_mul_eq_one.mp hone).symm
    apply Subgroup.mem_bot.mp
    rw [← hfaith, mem_fixingSubgroup_iff]
    intro v _
    have hv : v ∈ P ⊔ Q := hcompl.sup_eq_top.ge (Subgroup.mem_top v)
    obtain ⟨p, hp, q, hq, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [smul_mul', hPfix p hp, hQfix q hq]
  have hcover : ∀ b : A, b = 1 ∨ b = a := by
    intro b
    rcases hperm b with hpreserves | hswaps
    · exact Or.inl (stable_trivial b hpreserves.1 hpreserves.2)
    · right
      have hba : b * a = 1 := stable_trivial (b * a)
        (fun v hv => by rw [mul_smul]; exact hswaps.2 _ (hswap.1 v hv))
        (fun v hv => by rw [mul_smul]; exact hswaps.1 _ (hswap.2 v hv))
      have ha2 : a ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a
      have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha2)
      exact (eq_inv_of_mul_eq_one_left hba).trans hainv
  have hsubset : (Set.univ : Set A) ⊆ {1, a} := by
    intro b _
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hcover b
  have hsmall : Nat.card A ≤ 2 := by
    have hh := Set.ncard_le_ncard hsubset (Set.toFinite _)
    rw [Set.ncard_univ] at hh
    by_cases ha : (1 : A) = a
    · simp only [← ha, Set.pair_eq_singleton, Set.ncard_singleton] at hh
      omega
    · rw [Set.ncard_pair ha] at hh
      exact hh
  omega
