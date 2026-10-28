module

public import CFSG.Quasithin.ChapterE.Section03.Parameters

/-!
# The weak-closure minimum and its offenders

The parameter in E.3.23 is the minimum index at which the actual weak closure
escapes the relative centralizer in the specified Sylow subgroup. It takes
values in the extended naturals: an empty minimizing family has value infinity.
A finite minimum is attained by an actual generator of the weak closure.
Offenders are the normalizers in conjugates of `V`, with the noncentralization
and quotient-rank conditions of E.3.27.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.3.22–27,
printed pp. 236–237.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- E.3.22, together with the nontrivial elementary abelian module from the
section setup. `normalizes` expresses normality in `T`, not in `G`. -/
structure HypothesisE322 (V : Subgroup G) (T : Sylow 2 G)
    [IsElementaryAbelian 2 V] : Prop where
  nontrivial : V ≠ ⊥
  le_sylow : V ≤ T
  normalizes : (T : Subgroup G) ≤ normalizer (V : Set G)

/-- E.3.23; infinity records an empty minimizing family. -/
noncomputable def globalW (V T : Subgroup G) : ℕ∞ :=
  ⨅ (j : ℕ) (_ : ¬ indexedWeakClosure V T j ≤ T ⊓ centralizer (V : Set G)), (j : ℕ∞)

/-- E.3.24, with the genuine FF-module condition on the actual automizer. -/
def HypothesisE324 (V T : Subgroup G) [IsElementaryAbelian 2 V] : Prop :=
  0 < globalW V T ∨ ¬ IsFFModule (automizerRepresentation V)

/-- The relative normalizer `N_{Vᵍ}(V)`. -/
def offenderNormalizer (V : Subgroup G) (g : G) : Subgroup G :=
  V.map (MulAut.conj g).toMonoidHom ⊓ normalizer (V : Set G)

/-- The conjugating element in E.3.27 witnesses both noncentralization and the
precise quotient rank. No minimizing witness is silently chosen. -/
def IsWOffenderAt (V T : Subgroup G) (g : G) : Prop :=
  ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
    globalW V T = (subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) : ℕ∞)

/-- E.3.27: a subgroup is a `w`-offender if it is such a relative normalizer. -/
def IsWOffender (V T A : Subgroup G) : Prop :=
  ∃ g : G, A = offenderNormalizer V g ∧ IsWOffenderAt V T g

theorem globalW_le_of_escape {V T : Subgroup G} {j : ℕ}
    (h : ¬ indexedWeakClosure V T j ≤ T ⊓ centralizer (V : Set G)) :
    globalW V T ≤ (j : ℕ∞) :=
  iInf_le_of_le j (iInf_le_of_le h le_rfl)

/-- All weak closures below the minimum centralize `V`, including when it is infinite. -/
theorem weakClosure_le_centralizer_of_lt_globalW {V T : Subgroup G} {j : ℕ}
    (h : (j : ℕ∞) < globalW V T) :
    indexedWeakClosure V T j ≤ T ⊓ centralizer (V : Set G) := by
  by_contra hn
  exact (not_le_of_gt h) (globalW_le_of_escape hn)

/-- The value infinity is equivalent to emptiness of the escaping family. -/
theorem globalW_eq_top_iff (V T : Subgroup G) :
    globalW V T = ⊤ ↔ ∀ j, indexedWeakClosure V T j ≤ T ⊓ centralizer (V : Set G) := by
  constructor
  · intro h j
    by_contra hn
    have he := globalW_le_of_escape hn
    rw [h] at he
    exact (by simp : ¬ (⊤ : ℕ∞) ≤ (j : ℕ∞)) he
  · intro h
    apply top_unique
    apply le_iInf
    intro j
    apply le_iInf
    intro hn
    exact (hn (h j)).elim

/-- Every finite minimum is attained; this does not presuppose nonemptiness. -/
theorem globalW_attained {V T : Subgroup G} {n : ℕ} (h : globalW V T = n) :
    ¬ indexedWeakClosure V T n ≤ T ⊓ centralizer (V : Set G) := by
  obtain ⟨j, hj⟩ := (ENat.iInf_eq_natCast_iff.mp h).1
  obtain ⟨hn, hnval⟩ := (ENat.iInf_eq_natCast_iff.mp hj).1
  have : j = n := ENat.natCast_inj.mp hnval
  subst j
  exact hn

/-- A finite minimum has a noncentralizing conjugate-subgroup generator in `T`.
The later Sylow transport argument upgrades this generator to a `w`-offender. -/
theorem globalW_generator {V T : Subgroup G} {n : ℕ} (h : globalW V T = n) :
    ∃ A ∈ gamma V T n, ¬ A ≤ centralizer (V : Set G) := by
  classical
  by_contra! hn
  apply globalW_attained h
  apply le_inf (indexedWeakClosure_le V T n)
  rw [weakClosure_eq_sSup_gamma]
  exact sSup_le hn

/-- At index zero, the minimum detects a whole noncentralizing conjugate in `T`. -/
theorem globalW_eq_zero_iff (V T : Subgroup G) :
    globalW V T = 0 ↔ ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T ∧
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
  constructor
  · intro h
    obtain ⟨A, hA, hn⟩ := globalW_generator h
    obtain ⟨g, rfl, hg⟩ := (mem_gamma_zero_iff V T A).mp hA
    exact ⟨g, hg, hn⟩
  · rintro ⟨g, hg, hn⟩
    apply le_antisymm _ bot_le
    apply globalW_le_of_escape (j := 0)
    intro h
    exact hn ((gamma_le_weakClosure
      ((mem_gamma_zero_iff V T _).mpr ⟨g, rfl, hg⟩)).trans (h.trans inf_le_right))

/-- A conjugate already lying in the chosen Sylow subgroup centralizes `V`
when the weak-closure minimum is positive. -/
theorem conjugate_le_centralizer_of_le_sylow_of_globalW_pos
    {V T : Subgroup G} (h : 0 < globalW V T) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ T) :
    V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
  exact (gamma_le_weakClosure
    ((mem_gamma_zero_iff V T _).mpr ⟨g, rfl, hg⟩)).trans
    ((weakClosure_le_centralizer_of_lt_globalW h).trans inf_le_right)

theorem IsWOffenderAt.globalW_ne_top {V T : Subgroup G} {g : G}
    (h : IsWOffenderAt V T g) : globalW V T ≠ ⊤ := by
  rw [h.2]
  simp

/-- The centralizer inside the offender equals the centralizer inside its conjugate. -/
theorem offenderNormalizer_inf_centralizer (V : Subgroup G) (g : G) :
    offenderNormalizer V g ⊓ centralizer (V : Set G) =
      V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) := by
  rw [offenderNormalizer, inf_assoc, inf_eq_right.mpr (centralizer_le_normalizer _)]

/-- A zero-corank subgroup of an elementary abelian group is the whole group. -/
theorem subgroup_eq_of_corank_zero [Finite G] {V A : Subgroup G}
    [IsElementaryAbelian 2 V] (hAV : A ≤ V) (h : subgroupCorank V A = 0) : A = V := by
  have he : A.relIndex V = 1 := by
    rw [Subgroup.relIndex_eq_two_pow_quotient_finrank,
      ← subgroupCorank_eq_quotient_finrank, h, pow_zero]
  exact le_antisymm hAV (Subgroup.relIndex_eq_one.mp he)

/-- An offender at `w = 0` is the full conjugate, hence normalizes `V`. -/
theorem IsWOffenderAt.normalizes_of_globalW_eq_zero [Finite G]
    {V T : Subgroup G} [IsElementaryAbelian 2 V] {g : G}
    (h : IsWOffenderAt V T g) (hw : globalW V T = 0) :
    V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) := by
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hz : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) = 0 := by
    exact_mod_cast (h.2.symm.trans hw)
  have he := subgroup_eq_of_corank_zero (A := offenderNormalizer V g) inf_le_left hz
  rw [← he]
  exact inf_le_right

end CFSG.Quasithin.ChapterE
