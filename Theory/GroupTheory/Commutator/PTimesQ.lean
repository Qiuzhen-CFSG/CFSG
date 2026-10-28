module
public import Theory.GroupTheory.Commutator.CoprimeQuadratic
public import Theory.GroupTheory.Hall.Conjugacy
public import Mathlib.GroupTheory.Nilpotent

/-!
# The general P × Q centralizer theorem

Let P and B be finite p-subgroups of a common ambient group, with a
p-prime subgroup Q commuting with P. If both actors normalize B and Q
centralizes C_B(P), then Q centralizes B. B need not be abelian.

Induct on the order of B. Nilpotence of B P makes [B,P] proper in B.
The induction hypothesis kills [[B,P],Q]. The three-subgroups lemma
then puts [B,Q] in C_B(P), hence in C_B(Q) by the fixed-point hypothesis.
Coprime commutator idempotence concludes [B,Q]=1.

Source: Kurzweil–Stellmacher 8.2.8, promoted from the existing proof in
GorensteinWalter.Section2.ThompsonPQ with its public theorem preserved
as a wrapper. Only the needed nilpotent commutator argument is retained
from the former complement-conjugacy dependency. This general form also
supplies the odd-core elimination in Stellmacher (10.1)(a3), source (10).
-/

open scoped Pointwise commutatorElement
namespace Subgroup
universe u

private theorem commutator_lt_of_pGroups
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (B P : Subgroup G) (hBp : IsPGroup p B) (hPp : IsPGroup p P)
    (hPB : P ≤ Subgroup.normalizer (B : Set G)) (hBne : B ≠ ⊥) :
    ⁅B, P⁆ < B := by
  have hle : ⁅B, P⁆ ≤ B :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hPB
  refine lt_of_le_of_ne hle ?_
  intro heq
  let S : Subgroup G := B ⊔ P
  have hBnormS : (B.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (H := B) (K := S) le_sup_left).2
    exact sup_le Subgroup.le_normalizer hPB
  let : (B.subgroupOf S).Normal := hBnormS
  have hBPp : IsPGroup p S :=
    IsPGroup.to_sup_of_normal_left' hBp hPp hPB
  have hnil : Group.IsNilpotent ↑S :=
    IsPGroup.isNilpotent (p := p) hBPp
  obtain ⟨n, hn⟩ :=
    (Subgroup.nilpotent_iff_lowerCentralSeries (G := ↑S)).mp hnil
  have hB_le_lcs :
      ∀ n : ℕ, B.subgroupOf S ≤
        (⊤ : Subgroup ↑S).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => simp [Subgroup.lowerCentralSeries_zero]
    | succ n ih =>
        rw [Subgroup.lowerCentralSeries_succ]
        have hcomm_sub :
            ⁅B.subgroupOf S, P.subgroupOf S⁆ = B.subgroupOf S := by
          apply (Subgroup.map_subtype_inj (H := S)).mp
          calc
            (⁅B.subgroupOf S, P.subgroupOf S⁆).map S.subtype = B := by
              rw [Subgroup.map_commutator,
                Subgroup.map_subgroupOf_eq_of_le le_sup_left,
                Subgroup.map_subgroupOf_eq_of_le le_sup_right, heq]
            _ = (B.subgroupOf S).map S.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le le_sup_left).symm
        rw [← hcomm_sub]
        exact Subgroup.commutator_mono ih le_top
  have hBsub_bot : B.subgroupOf S = ⊥ := by
    apply bot_unique
    exact (hB_le_lcs n).trans_eq hn
  apply hBne
  calc
    B = (B.subgroupOf S).map S.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le le_sup_left).symm
    _ = ⊥ := by rw [hBsub_bot]; simp

/-- If `Q` normalizes `B` and centralizes `P`, then it normalizes `[B,P]`. -/
private theorem normalizes_commutator_of_normalizes_left_of_commutes
    {G : Type u} [Group G] {B P Q : Subgroup G}
    (hBQ : Q ≤ Subgroup.normalizer (B : Set G))
    (hPQ : ⁅P, Q⁆ = ⊥) :
    Q ≤ Subgroup.normalizer ((⁅B, P⁆ : Subgroup G) : Set G) := by
  have hQP : ⁅Q, P⁆ = ⊥ := by
    simpa [Subgroup.commutator_comm] using hPQ
  have hQcentP : Q ≤ Subgroup.centralizer (P : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hQP
  have hQnormP : Q ≤ Subgroup.normalizer (P : Set G) :=
    hQcentP.trans (Subgroup.centralizer_le_normalizer (P : Set G))
  apply subgroup_le_normalizer_of_conj_mem
  intro q x hx
  have hmapB : B.map (MulAut.conj (q : G)).toMonoidHom = B := by
    have h := map_conj_mul_right_eq_of_mem_normalizer (H := B) (g := (1 : G))
      ⟨q, hBQ q.property⟩
    have hid : B.map (MulAut.conj (1 : G)).toMonoidHom = B := by
      ext y
      simp [MulAut.conj]
    simpa only [one_mul] using h.trans hid
  have hmapP : P.map (MulAut.conj (q : G)).toMonoidHom = P := by
    have h := map_conj_mul_right_eq_of_mem_normalizer (H := P) (g := (1 : G))
      ⟨q, hQnormP q.property⟩
    have hid : P.map (MulAut.conj (1 : G)).toMonoidHom = P := by
      ext y
      simp [MulAut.conj]
    simpa only [one_mul] using h.trans hid
  have hmapU : (⁅B, P⁆).map (MulAut.conj (q : G)).toMonoidHom = ⁅B, P⁆ := by
    rw [Subgroup.map_commutator, hmapB, hmapP]
  have hxmap : (MulAut.conj (q : G)).toMonoidHom x ∈
      (⁅B, P⁆).map (MulAut.conj (q : G)).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hmapU] at hxmap
  simpa [MulAut.conj] using hxmap


/-- **Thompson's P × Q lemma** (Kurzweil--Stellmacher 8.2.8), in the
ambient-subgroup form needed by Bender's Statement 1.1.

Here `P` and `B` are `p`-groups, `Q` has order prime to `p`, `P` and `Q`
commute, and both normalize `B`.  The fixed-point containment is written as
`C_B(P) ≤ C_G(Q)`. -/
public theorem p_times_q_centralizer
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P Q B : Subgroup G)
    (hPp : IsPGroup p P) (hBp : IsPGroup p B)
    (hQcop : Nat.Coprime p (Nat.card Q))
    (hPB : P ≤ Subgroup.normalizer (B : Set G))
    (hQB : Q ≤ Subgroup.normalizer (B : Set G))
    (hPQ : ⁅P, Q⁆ = ⊥)
    (hfixed : B ⊓ Subgroup.centralizer (P : Set G) ≤
      Subgroup.centralizer (Q : Set G)) :
    ⁅B, Q⁆ = ⊥ := by
  classical
  induction hcard : Nat.card B using Nat.strong_induction_on generalizing B with
  | h n ih =>
      by_cases hBbot : B = ⊥
      · simp [hBbot]
      let U : Subgroup G := ⁅B, P⁆
      have hUleB : U ≤ B :=
        (Subgroup.le_normalizer_iff_commutator_le_left).mp hPB
      have hUltB : U < B := by
        simpa [U] using
          (commutator_lt_of_pGroups B P hBp hPp hPB hBbot)
      have hUcard : Nat.card U < n := by
        rw [← hcard]
        exact lt_of_le_of_ne (Subgroup.card_le_of_le hUltB.le) (fun heq =>
          hUltB.ne (Subgroup.eq_of_le_of_card_ge hUltB.le heq.ge))
      have hUp : IsPGroup p U := hBp.to_le hUleB
      have hPnormU : P ≤ Subgroup.normalizer (U : Set G) := by
        simpa [U] using Subgroup.normalizer_commutator_ge_right B P
      have hQnormU : Q ≤ Subgroup.normalizer (U : Set G) := by
        simpa [U] using
          normalizes_commutator_of_normalizes_left_of_commutes hQB hPQ
      have hfixedU : U ⊓ Subgroup.centralizer (P : Set G) ≤
          Subgroup.centralizer (Q : Set G) := by
        intro x hx
        exact hfixed ⟨hUleB hx.1, hx.2⟩
      have hUQ : ⁅U, Q⁆ = ⊥ :=
        ih (Nat.card U) hUcard (B := U) hUp hPnormU hQnormU hfixedU rfl
      have hPQB : ⁅⁅P, Q⁆, B⁆ = ⊥ := by simp [hPQ]
      have hQBP : ⁅⁅Q, B⁆, P⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate hUQ hPQB
      have hBQcentP : ⁅B, Q⁆ ≤ Subgroup.centralizer (P : Set G) := by
        have h := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hQBP
        simpa [Subgroup.commutator_comm] using h
      have hBQleB : ⁅B, Q⁆ ≤ B :=
        (Subgroup.le_normalizer_iff_commutator_le_left).mp hQB
      have hBQcentQ : ⁅B, Q⁆ ≤ Subgroup.centralizer (Q : Set G) :=
        (le_inf hBQleB hBQcentP).trans hfixed
      have hdouble : ⁅⁅B, Q⁆, Q⁆ = ⊥ :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hBQcentQ
      let : Group.IsNilpotent B := hBp.isNilpotent
      have hBsolv : Group.IsSolvable B := inferInstance
      obtain ⟨m, hm⟩ := hBp.exists_card_eq
      have hQcopB : Nat.Coprime (Nat.card Q) (Nat.card B) := by
        rw [hm]
        exact hQcop.symm.pow_right m
      exact commutator_eq_bot_of_coprime_quadratic B Q hQB hBsolv hQcopB hdouble

end Subgroup
