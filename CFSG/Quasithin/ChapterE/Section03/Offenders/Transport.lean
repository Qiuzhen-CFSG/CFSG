module

public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport.Foundations

/-!
# Sylow transport and realization of weak-closure offenders

Conjugation preserves the extended weak-closure minimum and the hypotheses on
the specified Sylow subgroup. Sylow conjugacy inside `N_G(V)` bounds that minimum
by the corank of every noncentralizing subgroup of a conjugate that normalizes
`V`. An escaping generator at a finite minimum therefore gives an actual
offender. At index zero this also proves the normalization equivalences of
E.3.25. The non-FF obstruction handles the zero branch of E.3.26 and E.3.28(4).

For the reverse-normalizer bound used in E.3.31, a hypothetical smaller corank
first forces centralization by the conjugated minimum. Centralizer rigidity
below `r` then contradicts E.3.25. The argument keeps the value infinity intact;
only an actual offender or an explicit finite minimum supplies finiteness.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.3.22–31,
printed pp. 236–238 (PDF pp. 247–249).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE
open Subgroup Representation.BinaryOffender
variable {G : Type*} [Group G]

/-- The extended minimum is unchanged by simultaneous conjugation, including
the case of an empty escaping family. -/
theorem globalW_conj (V T : Subgroup G) (g : G) :
    globalW (V.map (MulAut.conj g).toMonoidHom)
      (T.map (MulAut.conj g).toMonoidHom) = globalW V T := by
  unfold globalW
  simp_rw [indexedWeakClosure_conj_le_centralizer_iff]

/-- E.3.22 transports to the actual conjugate Sylow subgroup. -/
theorem HypothesisE322.conj {V : Subgroup G} [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} (hT : HypothesisE322 V T) (g : G) :
    letI : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
      IsElementaryAbelian.map _
    HypothesisE322 (V.map (MulAut.conj g).toMonoidHom) (g • T) := by
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  obtain ⟨hV, hVT, hTN⟩ := offender_conjugate_sylow_data V T
    hT.nontrivial hT.le_sylow hT.normalizes g
  exact ⟨hV, hVT, hTN⟩

variable [Finite G]

/-- Sylow conjugacy inside `N_G(V)` makes a noncentralizing normalizing
subgroup of a conjugate an upper bound for the weak-closure minimum. -/
theorem globalW_le_corank_of_noncentralizing_normalizes
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) (g : G) {A : Subgroup G}
    (hA : A ≤ V.map (MulAut.conj g).toMonoidHom ⊓ normalizer (V : Set G))
    (hAC : ¬ A ≤ centralizer (V : Set G)) :
    globalW V T ≤ (subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A : ℕ∞) :=
  globalW_le_of_escape (indexedWeakClosure_escape_at_corank V T hT.normalizes g hA hAC)

/-- Below the minimum, every normalizing subgroup of a conjugate centralizes
`V`, even when the subgroup does not lie in the specified Sylow subgroup. -/
theorem centralizes_of_corank_lt_globalW
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) (g : G) {A : Subgroup G}
    (hA : A ≤ V.map (MulAut.conj g).toMonoidHom ⊓ normalizer (V : Set G))
    (hc : (subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A : ℕ∞) < globalW V T) :
    A ≤ centralizer (V : Set G) := by
  by_contra hn
  exact (not_le_of_gt hc) (globalW_le_corank_of_noncentralizing_normalizes hT g hA hn)

/-- Every finite value of the minimum is realized by the actual normalizer
inside a noncentralizing conjugate of `V`. -/
theorem exists_isWOffenderAt_of_globalW_eq_nat
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) {n : ℕ} (hw : globalW V T = n) :
    ∃ g : G, IsWOffenderAt V T g := by
  obtain ⟨A, ⟨⟨g, hAW, hi⟩, hAT⟩, hAC⟩ := globalW_generator hw
  let W := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hAB : A ≤ offenderNormalizer V g := le_inf hAW (hAT.trans hT.normalizes)
  have hBC : ¬ offenderNormalizer V g ≤ centralizer (V : Set G) :=
    fun h => hAC (hAB.trans h)
  have hcorA : subgroupCorank W A = n := by
    change Nat.log 2 (A.relIndex W) = n
    rw [hi, Nat.log_pow (by decide)]
  have hcorB : subgroupCorank W (offenderNormalizer V g) ≤ n := by
    have h := offender_corank_add (W := W) hAB
      (show offenderNormalizer V g ≤ W from inf_le_left)
    rw [hcorA] at h
    omega
  refine ⟨g, ?_, le_antisymm
    (globalW_le_corank_of_noncentralizing_normalizes hT g le_rfl hBC) ?_⟩
  · intro hc
    exact hAC (hAW.trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)))
  · rw [hw]
    exact_mod_cast hcorB

/-- A finite extended minimum has a conjugating element realizing it. -/
theorem exists_isWOffenderAt_of_globalW_ne_top
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) (hw : globalW V T ≠ ⊤) :
    ∃ g : G, IsWOffenderAt V T g :=
  exists_isWOffenderAt_of_globalW_eq_nat hT (ENat.natCast_toNat hw).symm

/-- Finiteness is equivalent to existence of an actual offender. -/
theorem globalW_ne_top_iff_exists_isWOffender
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) :
    globalW V T ≠ ⊤ ↔ ∃ A : Subgroup G, IsWOffender V T A := by
  constructor
  · intro hw
    obtain ⟨g, hg⟩ := exists_isWOffenderAt_of_globalW_ne_top hT hw
    exact ⟨offenderNormalizer V g, g, rfl, hg⟩
  · rintro ⟨A, g, _, hg⟩
    exact hg.globalW_ne_top

/-- Aschbacher–Smith E.3.25: the four normalization and centralization
conditions are equivalent when `w > 0`. -/
theorem lemma_E_3_25
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) (hw : 0 < globalW V T) (g : G) :
    (V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ↔
      V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) ∧
    (V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) ↔
      V ≤ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ∧
    (V ≤ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) ↔
      V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :=
  conjugate_normalization_equivalences_of_weakClosure_zero hT.normalizes
    ((weakClosure_le_centralizer_of_lt_globalW hw).trans inf_le_right) g

/-- Aschbacher–Smith E.3.26: under E.3.24, a noncentralizing conjugate that
normalizes `V` cannot also be normalized by `V`. -/
theorem lemma_E_3_26
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) (h24 : HypothesisE324 V T) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G))
    (hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  rcases h24 with hw | hFF
  · intro hn
    exact hcomm (commutator_eq_bot_iff_le_centralizer.mpr
      ((lemma_E_3_25 hT hw g).2.2.mpr hn))
  · exact lemma_E_3_11 V g hFF hg hcomm

/-- Aschbacher–Smith E.3.28(4), including the `w = 0` branch. -/
theorem lemma_E_3_28_4
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) (h24 : HypothesisE324 V T) {g : G}
    (h : IsWOffenderAt V T g) :
    (¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ∧
    (0 < globalW V T → ¬ V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G)) := by
  have hpos (hw : 0 < globalW V T) :
      (¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      (¬ V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G)) := by
    have he := lemma_E_3_25 hT hw g
    constructor
    · intro hn
      exact h.1 (commutator_eq_bot_iff_le_centralizer.mpr (he.2.2.mpr hn))
    · intro hn
      exact h.1 (commutator_eq_bot_iff_le_centralizer.mpr (he.2.1.mp (he.1.mp hn)))
  refine ⟨?_, fun hw => (hpos hw).2⟩
  by_cases hw : globalW V T = 0
  · exact lemma_E_3_26 hT h24 g (h.normalizes_of_globalW_eq_zero hw) h.1
  · exact (hpos (pos_iff_ne_zero.mpr hw)).1

/-- The reverse-normalizer corank bound used in E.3.31. The assumption `w < r`
is essential to this argument; noncentralization alone supplies no such bound. -/
theorem IsWOffenderAt.le_reverse_normalizer_corank
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) {g : G} (h : IsWOffenderAt V T g)
    (hwr : globalW V T < globalR V) :
    globalW V T ≤ (subgroupCorank V
      (V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) : ℕ∞) := by
  by_contra hn
  have hc := lt_of_not_ge hn
  have hw : 0 < globalW V T := lt_of_le_of_lt zero_le hc
  let W := V.map (MulAut.conj g).toMonoidHom
  let B := V ⊓ normalizer (W : Set G)
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hinv : W.map (MulAut.conj g⁻¹).toMonoidHom = V :=
    offender_map_conj_inverse V g
  have hB : B ≤ W.map (MulAut.conj g⁻¹).toMonoidHom ⊓ normalizer (W : Set G) := by
    rw [hinv]
  have hsmall : (subgroupCorank (W.map (MulAut.conj g⁻¹).toMonoidHom) B : ℕ∞) <
      globalW W (g • T : Sylow 2 G) := by
    rw [hinv]
    change (subgroupCorank V B : ℕ∞) < globalW
      (V.map (MulAut.conj g).toMonoidHom) ((T : Subgroup G).map (MulAut.conj g).toMonoidHom)
    rw [globalW_conj]
    exact hc
  have hBC : B ≤ centralizer (W : Set G) :=
    centralizes_of_corank_lt_globalW (hT.conj g) g⁻¹ hB hsmall
  have hWN : W ≤ normalizer (V : Set G) :=
    (le_centralizer_iff.mp hBC).trans
      (centralizer_le_normalizer_of_corank_lt_globalR inf_le_left (hc.trans hwr))
  exact h.1 (commutator_eq_bot_iff_le_centralizer.mpr
    ((lemma_E_3_25 hT hw g).2.1.mp ((lemma_E_3_25 hT hw g).1.mp hWN)))

end CFSG.Quasithin.ChapterE
