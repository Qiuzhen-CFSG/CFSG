module
public import Theory.GroupTheory.SemidihedralCenter
public import Stellmacher.MainDefs
public import Theory.GroupTheory.QuaternionGenerated

/-!
# Normal forms for the quasi-dihedral presentation

For generators `a, b`, where `a` has positive finite order, `b` is an
involution, and conjugation by `b` sends `a` to a power of `a`, every group
element is `a ^ i` or `a ^ i * b`, with `i` below the order of `a`.
The explicit-generator interface lets all subsequent calculations use the
same presentation witnesses. The final theorem extracts those witnesses
from `Stellmacher.IsSemidihedralGroup` without altering its definition.
The more general integer normal forms also allow `b²` to be any power of
`a`; this supports the dihedral and quaternion subgroups of the ambient
group. The generator-subtype lemma records generation inside the resulting
subgroup.

The shared integer-normal-form and generator-subtype results are re-exported
from `Theory.GroupTheory.QuaternionGenerated`; natural-power movement and
bounded normal forms forward to `Theory.GroupTheory.SemidihedralCenter`.
The bounded form specializes the shared square normal form to `b² = 1`,
then reduces integer exponents modulo `orderOf a`, without repeating the
closure induction. This is the
basic calculation implicit in the presentation in Chapter I, article p. 2,
and the proof of Chapter II, §1, Lemma 1, article p. 9, of
`refs/latex/alperin-brauer-gorenstein.tex`. Stellmacher's order parameter is
one larger than the article's parameter.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]

/-- Move the involutory generator past an integer power of the cyclic generator. -/
public theorem move_zpow (a b : G) (k : ℕ)
    (hconj : b * a * b⁻¹ = a ^ k) (i : ℤ) :
    b * a ^ i = a ^ ((k : ℤ) * i) * b :=
  Subgroup.move_zpow a b k hconj i

/-- Move the involutory generator past a natural power of the cyclic generator. -/
public theorem move_pow (a b : G) (k : ℕ)
    (hconj : b * a * b⁻¹ = a ^ k) (i : ℕ) :
    b * a ^ i = a ^ (k * i) * b :=
  Semidihedral.move_pow a b k hconj i

/-- The two integer normal forms remain valid when the second generator's square
is an arbitrary integer power of the first generator. -/
public theorem square_normal_form_int (a b : G) (k : ℕ)
    (r : ℤ) (hb : b ^ 2 = a ^ r) (hconj : b * a * b⁻¹ = a ^ k)
    (x : G) (hx : x ∈ Subgroup.closure ({a, b} : Set G)) :
    ∃ i : ℤ, x = a ^ i ∨ x = a ^ i * b :=
  Subgroup.square_normal_form_int a b k r hb hconj x hx

/-- The two designated elements generate the subgroup they generate in the ambient group. -/
public theorem generated_subtype (a b : G) :
    Subgroup.closure ({(⟨a, Subgroup.subset_closure (by simp)⟩ : Subgroup.closure ({a,b}:Set G)),
      ⟨b, Subgroup.subset_closure (by simp)⟩} : Set (Subgroup.closure ({a,b}:Set G)))=⊤ :=
  Subgroup.generated_subtype a b

/-- Every element of a group with this presentation has one of the two bounded normal forms. -/
public theorem normal_form (a b : G) (m k : ℕ)
    (hm : 0 < m) (ha : orderOf a = m) (hb : b ^ 2 = 1)
    (hconj : b * a * b⁻¹ = a ^ k)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (x : G) :
    ∃ i : ℕ, i < m ∧ (x = a ^ i ∨ x = a ^ i * b) :=
  Semidihedral.normal_form a b m k hm ha hb hconj hgen x
end ABG.QuasiDihedral

namespace ABG.QuasiDihedral
/-- The normal forms supplied by the actual semidihedral presentation. -/
public theorem exists_normal_form {G : Type*} [Group G]
    (hG : Stellmacher.IsSemidihedralGroup G) :
    ∃ (n : ℕ) (a b : G), 4 ≤ n ∧ Nat.card G = 2 ^ n ∧
      orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
      b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧
      Subgroup.closure ({a, b} : Set G) = ⊤ ∧
      ∀ x : G, ∃ i : ℕ, i < 2 ^ (n - 1) ∧ (x = a ^ i ∨ x = a ^ i * b) := by
  obtain ⟨n, hn, hcard, a, b, ha, hb, hconj, hgen⟩ := hG
  refine ⟨n, a, b, hn, hcard, ha, hb, hconj, hgen, ?_⟩
  exact normal_form a b (2 ^ (n - 1)) (2 ^ (n - 2) - 1)
    (by positivity) ha (by rw [← hb]; exact pow_orderOf_eq_one b) hconj hgen
end ABG.QuasiDihedral
