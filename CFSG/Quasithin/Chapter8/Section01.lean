module

public import CFSG.Quasithin.Chapter8.Defs
public import CFSG.Quasithin.ChapterE.Section03.Offenders

/-!
# Eliminating shadows of the Fischer groups: weak-closure reductions

This module proves the ambient-group steps of Theorem 8.1.3. Centralizer
rigidity places the literal corank-five span inside the reverse normalizer;
the weak-closure minimum then bounds its codimension. The fundamental
inequality excludes the numerical M₂₃ row, forces all numerical equalities
in the M₂₄ row, and reduces the M₂₂ row to the two fixed-space calculations
H.15.4.4 and H.15.5.

The hypotheses supplying the row bounds and those two model calculations
remain explicit. In particular these results do not yet assert 8.1.1,
8.1.2, or the complete 8.1.3: their source assembly also needs Chapter 7,
C.4.8, and the Mathieu module identifications.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), §8.1,
printed pp. 711–714; the last paragraph of 8.1.3 is on p. 714.
-/

public section
namespace CFSG.Quasithin.Chapter8
open Subgroup ChapterE Representation.BinaryOffender
variable {G : Type*} [Group G]

/-- The span is a subgroup of the original module. -/
theorem offenderCentralizerSpan_le (V : Subgroup G) (g : G) (k : ℕ) :
    offenderCentralizerSpan V g k ≤ V := by
  exact iSup_le fun _ => iSup_le fun _ => inf_le_left

/-- Rigidity below `r` applies to every member of the actual family, after
transporting `r` to the conjugate `Vᵍ`. This is the normalizer inclusion
in the M₂₂ paragraph of 8.1.3. -/
theorem offenderCentralizerSpan_le_reverse_normalizer
    {V : Subgroup G} (g : G) {k : ℕ} (hk : (k : ℕ∞) < globalR V) :
    offenderCentralizerSpan V g k ≤
      V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  apply le_inf (offenderCentralizerSpan_le V g k)
  apply iSup_le
  intro B
  apply iSup_le
  intro hB
  apply inf_le_right.trans
  apply centralizer_le_normalizer_of_corank_lt_globalR (hB.1.trans inf_le_left)
  rw [hB.2.2, globalR_map_equiv]
  exact hk

variable [Finite G]

/-- The image-rank equation in the M₂₂ paragraph. Retaining the additive
equation avoids ambiguous truncated subtraction in `m(Ā) + w - 5`. -/
theorem offenderCorankFamily_image_rank
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Subgroup G}
    {g : G} (h : IsWOffenderAt V T g) {k : ℕ} {B : Subgroup G}
    (hB : B ∈ offenderCorankFamily V g k) :
    k + rank (inducedAutomizer V B) = (globalW V T).toNat +
      rank (inducedAutomizer V (offenderNormalizer V g)) := by
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hker : B ⊓ centralizer (V : Set G) =
      offenderNormalizer V g ⊓ centralizer (V : Set G) :=
    le_antisymm (inf_le_inf_right _ hB.1) (le_inf hB.2.1 inf_le_right)
  have hadd := offender_corank_add
    (show B ⊓ centralizer (V : Set G) ≤ B from inf_le_left)
    (hB.1.trans (show offenderNormalizer V g ≤
      V.map (MulAut.conj g).toMonoidHom from inf_le_left))
  rw [← rank_inducedAutomizer V B (hB.1.trans inf_le_right), hker,
    offender_centralizer_corank, hB.2.2] at hadd
  rw [h.2, ENat.toNat_natCast]
  exact hadd.symm

/-- The rank-to-corank step of 8.1.2. The substantive hypothesis is a bound
on each escaping subspace; the minimum is the actual `r(G,V)`. -/
theorem globalR_lower_of_escaping_rank_bound
    {V : Subgroup G} [IsElementaryAbelian 2 V] {b : ℕ}
    (hb : ∀ U : Subgroup G, U ≤ V →
      ¬ centralizer (U : Set G) ≤ normalizer (V : Set G) → rank U ≤ b) :
    ((rank V - b : ℕ) : ℕ∞) ≤ globalR V := by
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hUV, hescape⟩
  have hadd := offender_corank_add (B := (⊥ : Subgroup G)) bot_le hUV
  have he : rank V = subgroupCorank V U + rank U := by
    simpa only [subgroupCorank, relIndex_bot_left, rank] using hadd
  have hU := hb U hUV hescape
  exact_mod_cast (show rank V - b ≤ subgroupCorank V U by omega)

/-- The reverse-normalizer bound yields the precise corank obstruction for
the span, with the source's needed strict inequality `w < r`. -/
theorem globalW_le_offenderCentralizerSpan_corank
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) {g : G} (h : IsWOffenderAt V T g)
    (hwr : globalW V T < globalR V) {k : ℕ} (hk : (k : ℕ∞) < globalR V) :
    globalW V T ≤ (subgroupCorank V (offenderCentralizerSpan V g k) : ℕ∞) := by
  have hle := offenderCentralizerSpan_le_reverse_normalizer g hk
  have hadd := offender_corank_add hle (show
    V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) ≤ V from inf_le_left)
  have hc : subgroupCorank V
      (V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ≤
      subgroupCorank V (offenderCentralizerSpan V g k) := by omega
  exact (h.le_reverse_normalizer_corank hT hwr).trans (by exact_mod_cast hc)

/-- Passing to natural values is justified by the actual noncentralizing
offender, rather than by silently excluding infinite minima. -/
private theorem offender_numerical_inequality
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) (h24 : HypothesisE324 V T) {g : G}
    (h : IsWOffenderAt V T g) :
    (globalR V).toNat ≤ (globalW V T).toNat +
      rank (inducedAutomizer V (offenderNormalizer V g)) := by
  have hi := (lemma_E_3_28 hT h24 h).2.1.1
  have hr := ENat.natCast_toNat (globalR_ne_top_of_noncentralizing_conjugate g h.1)
  have hw := ENat.natCast_toNat h.globalW_ne_top
  rw [← hr, ← hw, ← ENat.natCast_add] at hi
  exact_mod_cast hi

/-- The M₂₃ row is impossible once 8.1.2 and Table 7.2.1 provide their bounds.
All parameters here belong to the actual ambient action. -/
theorem m23_row_impossible
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) (h24 : HypothesisE324 V T)
    (hr : 7 ≤ globalR V) (hw : globalW V T ≤ 2)
    (hm : primeRank 2 (Automizer V) ≤ 4) : False := by
  have hi := lemma_E_3_29 hT h24
  have hu : (primeRank 2 (Automizer V) : ℕ∞) + globalW V T ≤ 4 + 2 :=
    add_le_add (by exact_mod_cast hm) hw
  have hb := hr.trans (hi.trans hu)
  norm_num at hb

/-- Application of the rank-to-corank bridge to the M₂₃ row. The remaining
model input is the bound four on escaping subspaces in 8.1.2. -/
theorem m23_impossible_of_escaping_rank_bound
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) (h24 : HypothesisE324 V T)
    (hV : rank V = 11) (hw : globalW V T ≤ 2)
    (hm : primeRank 2 (Automizer V) ≤ 4)
    (hb : ∀ U : Subgroup G, U ≤ V →
      ¬ centralizer (U : Set G) ≤ normalizer (V : Set G) → rank U ≤ 4) : False := by
  have hr := globalR_lower_of_escaping_rank_bound hb
  rw [hV] at hr
  exact m23_row_impossible hT h24 hr hw hm

/-- The equality row for M₂₄, including the rank of the action kernel.
The dimension-eleven premise is the actual rank of `V`; conjugation
transports it to `Vᵍ` in the cardinal calculation. -/
theorem m24_row_equalities
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) (h24 : HypothesisE324 V T) {g : G}
    (h : IsWOffenderAt V T g)
    (hr : 8 ≤ globalR V) (hw : globalW V T ≤ 2)
    (hm : primeRank 2 (Automizer V) ≤ 6)
    (hV : rank V = 11) :
    globalR V = 8 ∧ globalW V T = 2 ∧
      rank (inducedAutomizer V (offenderNormalizer V g)) = 6 ∧
      rank (offenderNormalizer V g ⊓ centralizer (V : Set G)) = 3 := by
  have hrfinite := ENat.natCast_toNat
    (globalR_ne_top_of_noncentralizing_conjugate g h.1)
  have hwfinite := ENat.natCast_toNat h.globalW_ne_top
  have hrnat : 8 ≤ (globalR V).toNat := by rw [← hrfinite] at hr; exact_mod_cast hr
  have hwnat : (globalW V T).toNat ≤ 2 := by rw [← hwfinite] at hw; exact_mod_cast hw
  have hi := offender_numerical_inequality hT h24 h
  have hmA := (offender_automizer_rank_le V g).trans hm
  have hreq : (globalR V).toNat = 8 := by omega
  have hweq : (globalW V T).toNat = 2 := by omega
  have hAeq : rank (inducedAutomizer V (offenderNormalizer V g)) = 6 := by omega
  have hwq : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) = 2 := by
    have hwe : globalW V T = 2 := by rw [← hwfinite, hweq]; rfl
    exact_mod_cast h.2.symm.trans hwe
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hcor := offender_centralizer_corank V g
  rw [hwq, hAeq] at hcor
  have hadd := offender_corank_add (B := (⊥ : Subgroup G)) bot_le
    (show offenderNormalizer V g ⊓ centralizer (V : Set G) ≤
      V.map (MulAut.conj g).toMonoidHom from inf_le_left.trans inf_le_left)
  have hdim : rank (V.map (MulAut.conj g).toMonoidHom) =
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
        (offenderNormalizer V g ⊓ centralizer (V : Set G)) +
      rank (offenderNormalizer V g ⊓ centralizer (V : Set G)) := by
    simpa only [subgroupCorank, relIndex_bot_left, rank] using hadd
  have hVg : rank (V.map (MulAut.conj g).toMonoidHom) = 11 := by
    change Nat.log 2 (Nat.card (V.map (MulAut.conj g).toMonoidHom)) = 11
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hV
  refine ⟨?_, ?_, hAeq, ?_⟩
  · rw [← hrfinite, hreq]; rfl
  · rw [← hwfinite, hweq]; rfl
  · omega

/-- In the equality row, the actual involution-centralizer core is proper.
This is the obstruction used with H.15.3.3 to exclude the sextet kernel;
H.14.1.1 and the marked model transport are still needed to identify `K_T`. -/
theorem m24_row_dualCore_proper
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) (h24 : HypothesisE324 V T) {g : G}
    (h : IsWOffenderAt V T g)
    (hr : 8 ≤ globalR V) (hw : globalW V T ≤ 2)
    (hm : primeRank 2 (Automizer V) ≤ 6) (hV : rank V = 11) :
    automizerDualCore V (inducedAutomizer V (offenderNormalizer V g)) 5 < V := by
  obtain ⟨hr8, hw2, hA6, _⟩ := m24_row_equalities hT h24 h hr hw hm hV
  have hm6 : primeRank 2 (Automizer V) = 6 :=
    le_antisymm hm (hA6 ▸ offender_automizer_rank_le V g)
  have heq : globalR V = globalW V T + (primeRank 2 (Automizer V) : ℕ∞) := by
    rw [hr8, hw2, hm6]
    rfl
  have hc := (lemma_E_3_31 hT h24 h heq).2.1
  rw [hA6, hw2] at hc
  apply lt_of_le_of_ne (automizerDualCore_le V _ 5)
  intro he
  change (2 : ℕ∞) ≤ (subgroupCorank V
    (automizerDualCore V (inducedAutomizer V (offenderNormalizer V g)) 5) : ℕ∞) at hc
  rw [he, subgroupCorank, relIndex_self, Nat.log_one_right] at hc
  norm_num at hc

/-- The image ranks of the actual corank-five family, as used to apply
H.15.4.4 and H.15.5. In rank four every image is a line; in rank five its
rank is `w`, which lies between one and two. -/
theorem m22_corankFamily_image_ranks
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) (h24 : HypothesisE324 V T) {g : G}
    (h : IsWOffenderAt V T g)
    (hr : 6 ≤ globalR V) (hw : globalW V T ≤ 2)
    (hm : primeRank 2 (Automizer V) ≤ 5) :
    1 ≤ (globalW V T).toNat ∧ (globalW V T).toNat ≤ 2 ∧
    (rank (inducedAutomizer V (offenderNormalizer V g)) = 4 ∨
      rank (inducedAutomizer V (offenderNormalizer V g)) = 5) ∧
    ∀ B ∈ offenderCorankFamily V g 5,
      (rank (inducedAutomizer V (offenderNormalizer V g)) = 4 →
        rank (inducedAutomizer V B) = 1) ∧
      (rank (inducedAutomizer V (offenderNormalizer V g)) = 5 →
        rank (inducedAutomizer V B) = (globalW V T).toNat) := by
  have hrfinite := ENat.natCast_toNat
    (globalR_ne_top_of_noncentralizing_conjugate g h.1)
  have hwfinite := ENat.natCast_toNat h.globalW_ne_top
  have hrnat : 6 ≤ (globalR V).toNat := by rw [← hrfinite] at hr; exact_mod_cast hr
  have hwnat : (globalW V T).toNat ≤ 2 := by rw [← hwfinite] at hw; exact_mod_cast hw
  have hi := offender_numerical_inequality hT h24 h
  have hmA := (offender_automizer_rank_le V g).trans hm
  refine ⟨by omega, hwnat, by omega, ?_⟩
  intro B hB
  have hBdim := offenderCorankFamily_image_rank h hB
  constructor <;> intro hA <;> omega

/-- The M₂₂ row is excluded by the two local fixed-space estimates used in
the source: H.14.3.1 plus H.15.4.4 gives the full span at image rank five;
H.15.5 bounds its corank at image rank four. These estimates concern the
literal ambient span, and their Mathieu-model transport remains an input. -/
theorem m22_row_impossible_of_fixed_span_estimates
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hT : HypothesisE322 V T) (h24 : HypothesisE324 V T) {g : G}
    (h : IsWOffenderAt V T g)
    (hr : 6 ≤ globalR V) (hw : globalW V T ≤ 2)
    (hm : primeRank 2 (Automizer V) ≤ 5)
    (hfive : rank (inducedAutomizer V (offenderNormalizer V g)) = 5 →
      offenderCentralizerSpan V g 5 = V)
    (hfour : rank (inducedAutomizer V (offenderNormalizer V g)) = 4 →
      offenderCentralizerSpan V g 5 < V →
      subgroupCorank V (offenderCentralizerSpan V g 5) ≤ 1) : False := by
  have hrfinite := ENat.natCast_toNat
    (globalR_ne_top_of_noncentralizing_conjugate g h.1)
  have hwfinite := ENat.natCast_toNat h.globalW_ne_top
  have hrnat : 6 ≤ (globalR V).toNat := by rw [← hrfinite] at hr; exact_mod_cast hr
  have hwnat : (globalW V T).toNat ≤ 2 := by rw [← hwfinite] at hw; exact_mod_cast hw
  have hi := offender_numerical_inequality hT h24 h
  have hmA := (offender_automizer_rank_le V g).trans hm
  have hwpos : 1 ≤ (globalW V T).toNat := by omega
  have hwr : globalW V T < globalR V :=
    lt_of_le_of_lt hw (lt_of_lt_of_le (by decide : (2 : ℕ∞) < 6) hr)
  have hk : (5 : ℕ∞) < globalR V := lt_of_lt_of_le (by decide) hr
  have hc := globalW_le_offenderCentralizerSpan_corank hT h hwr hk
  have hcnat : (globalW V T).toNat ≤
      subgroupCorank V (offenderCentralizerSpan V g 5) := by
    rw [← hwfinite] at hc
    exact_mod_cast hc
  have hproper : offenderCentralizerSpan V g 5 < V := by
    apply lt_of_le_of_ne (offenderCentralizerSpan_le V g 5)
    intro heq
    have hz : subgroupCorank V (offenderCentralizerSpan V g 5) = 0 := by
      rw [heq, subgroupCorank, relIndex_self, Nat.log_one_right]
    omega
  have hnotfive : rank (inducedAutomizer V (offenderNormalizer V g)) ≠ 5 :=
    fun heq => (ne_of_lt hproper) (hfive heq)
  have hAeq : rank (inducedAutomizer V (offenderNormalizer V g)) = 4 := by omega
  have hsmall := hfour hAeq hproper
  omega

end CFSG.Quasithin.Chapter8
