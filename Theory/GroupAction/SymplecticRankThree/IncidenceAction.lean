module
public import Theory.GroupAction.SymplecticRankThree.ProjectiveIncidence
public import Theory.GroupAction.SymplecticRankThree.RankThree

/-!
# Projective incidence axioms for Higman's actual rank-three action

The closed-neighbor polarity design constructed from the three source
orbits satisfies Veblen's axiom. Every line meets every block, a
noncollinear triple has a unique block, and four points are not coplanar.
All these assertions are derived from the action and the kernel bound;
no projective coordinates are supplied. The binary case follows with the
same hypotheses at q=2, without using the printed q>2 theorem.

Source: Higman (1964), Lemma 10 and Theorem 2(i), pp.153–155.
Field coordinatization, null-polarity realization and symplectic recognition
remain necessary subsequent steps.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree
open MulAction
variable {G Ω : Type*} [Group G] [Fintype Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] [IsPreprimitive G Ω]

/-- The geometric incidence output, proved from the original action data. -/
theorem condition_i_incidence {q : ℕ} (hq : 2 ≤ q)
    (a b c : Ω) (hab : a ≠ b) (t : G) (hta : t • a = b) (htb : t • b = a)
    (hc : orbit (stabilizer G a) c = (insert a (orbit (stabilizer G a) b))ᶜ)
    (hdegree : Nat.card Ω = q^3+q^2+q+1)
    (hsubdegree : Nat.card (orbit (stabilizer G a) b) = q*(q+1))
    (hk : q ≤ Nat.card (fixingSubgroup G (insert a (orbit (stabilizer G a) b)))) :
    ∃ D : PolarityDesign Ω q,
      (∀ x y, D.incident x y ↔ y = x ∨ (SwappedOrbital.graph a b hab t hta htb).Adj x y) ∧
      D.block a = insert a (orbit (stabilizer G a) b) ∧
      (∀ x y, x ≠ y → (D.line x y).ncard = q+1) ∧
      (∀ x y p, x ≠ y → (D.line x y ∩ D.block p).Nonempty) ∧
      (∀ x y z, x ≠ y → z ∉ D.line x y →
        ∃! p, x ∈ D.block p ∧ y ∈ D.block p ∧ z ∈ D.block p) ∧
      (∀ x y z w, z ≠ w → x ≠ z → y ≠ w →
        (D.line x y ∩ D.line z w).Nonempty → (D.line x z ∩ D.line y w).Nonempty) ∧
      (∃ x y z w, x ≠ y ∧ z ∉ D.line x y ∧
        ¬ ∃ p, x ∈ D.block p ∧ y ∈ D.block p ∧ z ∈ D.block p ∧ w ∈ D.block p) := by
  obtain ⟨D,hD,hblock,hline⟩ := condition_i_lines hq a b c hab t hta htb hc hdegree hsubdegree hk
  refine ⟨D,hD,hblock,hline,?_,?_,?_,D.exists_noncoplanar hline hq hdegree⟩
  · exact fun x y p hxy => D.line_meets_block hline (by omega) hxy p
  · exact fun x y z hxy hz => D.existsUnique_block_of_noncollinear hline (by omega) hxy hz
  · exact fun x y z w hzw hxz hyw hh => D.veblen hline (by omega) hzw hxz hyw hh

end Theory.GroupAction.SymplecticRankThree
