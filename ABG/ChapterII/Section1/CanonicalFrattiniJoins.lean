module
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Canonical joins with the cyclic square subgroup

For generators `a,b` and a parameter `n ≥ 4`, adjoining the canonical four
subgroup generators to `⟨a²⟩` gives `⟨a²,b⟩`; adjoining the canonical
quaternion subgroup generators gives `⟨a²,ab⟩`. The latter two subgroups
jointly generate the whole group. Only the generation hypothesis is needed:
there are no order or conjugation assumptions on the generators.

The half-order and quarter-order exponents are both even, so the associated
powers already lie in `⟨a²⟩`. Closure inclusions give the first two equalities.
The final join contains `b` and `ab`, hence also `a`, and is therefore the
whole group. These calculations underlie the Frattini joins in ABG Chapter
II, §1, Proposition 1, using the canonical subgroups of Lemma 1(ii)–(iv),
article pages 9–11 of `refs/latex/alperin-brauer-gorenstein.tex`.

The downstream assembly identifies `⟨a²⟩` with the Frattini subgroup and
transports these canonical equalities to arbitrary representatives.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]

private theorem cyclic_sup_pair (a b c : G) (hc : c ∈ Subgroup.zpowers a) :
    Subgroup.zpowers a ⊔ Subgroup.closure ({c,b} : Set G) =
      Subgroup.closure ({a,b} : Set G) := by
  have ha : a ∈ Subgroup.closure ({a,b} : Set G) := Subgroup.subset_closure (by simp)
  have hb : b ∈ Subgroup.closure ({a,b} : Set G) := Subgroup.subset_closure (by simp)
  have hle : Subgroup.zpowers a ≤ Subgroup.closure ({a,b} : Set G) :=
    Subgroup.zpowers_le.mpr ha
  apply le_antisymm
  · apply sup_le hle
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases (by simpa using hx : x = c ∨ x = b) with hx | hx
    · rw [hx]; exact hle hc
    · rw [hx]; exact hb
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases (by simpa using hx : x = a ∨ x = b) with hx | hx
    · rw [hx]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    · rw [hx]; exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

private theorem even_power_mem (a : G) (k : ℕ) :
    a ^ (2 ^ (k + 1)) ∈ Subgroup.zpowers (a ^ 2) := by
  rw [show (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k by rw [Nat.pow_succ, Nat.mul_comm], pow_mul]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

/-- The canonical four and quaternion generators give the two noncyclic
maximal-subgroup joins, whose combined join is the whole group. -/
public theorem canonical_frattini_joins {n : ℕ} (hn : 4 ≤ n) (a b : G)
    (hgen : Subgroup.closure ({a,b} : Set G) = ⊤) :
    let K := Subgroup.zpowers (a^2)
    let T₀ := Subgroup.closure ({a^(2^(n-2)),b} : Set G)
    let Q₀ := Subgroup.closure ({a^(2^(n-3)),a*b} : Set G)
    let D₀ := Subgroup.closure ({a^2,b} : Set G)
    let Y₀ := Subgroup.closure ({a^2,a*b} : Set G)
    K ⊔ T₀ = D₀ ∧ K ⊔ Q₀ = Y₀ ∧ D₀ ⊔ Y₀ = ⊤ := by
  dsimp only
  refine ⟨cyclic_sup_pair (a^2) b _ ?_, cyclic_sup_pair (a^2) (a*b) _ ?_, ?_⟩
  · rw [show n-2 = (n-3)+1 by omega]
    exact even_power_mem a (n-3)
  · rw [show n-3 = (n-4)+1 by omega]
    exact even_power_mem a (n-4)
  · let J := Subgroup.closure ({a^2,b} : Set G) ⊔ Subgroup.closure ({a^2,a*b} : Set G)
    have hb : b ∈ J := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    have hab : a*b ∈ J := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have ha : a ∈ J := by
      have h := J.mul_mem hab (J.inv_mem hb)
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using h
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases (by simpa using hx : x = a ∨ x = b) with hx | hx
    · rw [hx]; exact ha
    · rw [hx]; exact hb
end ABG.QuasiDihedral
