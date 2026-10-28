module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting
public import CFSG.Quasithin.Chapter3.Defs
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.SolvableNormalSup


/-!
# The Suzuki Borel step in 13.6.27

For a T-normalized subgroup D with actual Suzuki quotient D/O₂(D), restrict
T to D using normality inside ⟨D,T⟩. The matrix Borel geometry lifts through
O₂(D), so every proper overgroup of T ∩ D in D lies in its solvable Borel B.
Since T normalizes B, BT is solvable. The central involution z supplies its
nontrivial two-core, and source 13.6.25(3) therefore puts BT inside M.
Every proper T-overgroup in DT lies in BT, proving the literal HStar
minimality when D lies outside M. The same involution supplies O₂(DT) ≠ 1.

This proves the Borel step, conditional on the actual model equivalence and
T-normalization. It does not infer that an arbitrary component is normalized:
the component-orbit argument and the SQTK model sieve remain upstream.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.6.27, printed p.934 / PDF p.951; F.1.3(1), printed pp.259–260.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open ChapterF.Source
variable {G : Type*} [Group G]

private theorem solvable_join_of_normalizes (B T : Subgroup G)
    [Group.IsSolvable B] [Group.IsSolvable T]
    (hn : T ≤ normalizer (B : Set G)) : Group.IsSolvable (B ⊔ T : Subgroup G) := by
  let J := B ⊔ T
  let : (B.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  let : Group.IsSolvable (B.subgroupOf J) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show B ≤ J from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ J from le_sup_left)).injective
  let : Group.IsSolvable (T.subgroupOf J) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show T ≤ J from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show T ≤ J from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top (B.subgroupOf J) (T.subgroupOf J)
  rw [← subgroupOf_sup le_sup_left le_sup_right]
  exact subgroupOf_self J

private theorem normalizes_borel (D T : Subgroup G)
    (hn : T ≤ normalizer (D : Set G)) : T ≤ normalizer (borel D T : Set G) := by
  have hi : T ≤ normalizer ((T ⊓ D : Subgroup G) : Set G) :=
    (le_inf T.le_normalizer hn).trans inf_normalizer_le_normalizer_inf
  exact (le_inf hn (hi.trans (normalizer _).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

private theorem mem_HOver_of_central_involution (T J : Subgroup G) (z : G)
    (hz : orderOf z = 2) (hzT : z ∈ T) (hTJ : T ≤ J)
    (hJz : J ≤ centralizer ({z} : Set G)) :
    J ∈ Chapter1.HOver G (T : Set G) := by
  have hp : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hz)
  have hzJ : zpowers z ≤ J := zpowers_le.mpr (hTJ hzT)
  have hJN : J ≤ normalizer (zpowers z : Set G) := by
    have hn : centralizer ({z} : Set G) ≤ normalizer (zpowers z : Set G) := by
      rw [← centralizer_closure, ← zpowers_eq_closure]
      exact centralizer_le_normalizer _
    exact hJz.trans hn
  refine ⟨?_, hTJ⟩
  intro he
  have hm := le_pCoreIn_of_normalizes hp hzJ hJN (mem_zpowers z)
  rw [he] at hm
  have hez : z = 1 := hm
  simp [hez] at hz

variable [Finite G]

/-- The actual Borel and T generate a solvable member of H(T), so source
13.6.25(3) places both in M. -/
theorem borel_join_le_M (T : Sylow 2 G) (D M : Subgroup G) (z : G)
    (hz : orderOf z = 2) (hzT : z ∈ T)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hDz : D ≤ centralizer ({z} : Set G))
    (hn : (T : Subgroup G) ≤ normalizer (D : Set G))
    (hf : RankOneBorelFacts D (T : Subgroup G))
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M) :
    borel D (T : Subgroup G) ⊔ (T : Subgroup G) ≤ M := by
  let := hf.solvable
  let := T.isPGroup'.isNilpotent
  have hs := solvable_join_of_normalizes (borel D (T : Subgroup G)) T
    (normalizes_borel D T hn)
  have hm : borel D (T : Subgroup G) ⊔ (T : Subgroup G) ∈
      Chapter1.HOver G (T : Set G) :=
    mem_HOver_of_central_involution (T : Subgroup G)
      (borel D (T : Subgroup G) ⊔ (T : Subgroup G)) z hz hzT le_sup_right
      (sup_le ((borel_le D (T : Subgroup G)).trans hDz) hTz)
  exact h25 _ hm hs

/-- Rank-one Borel geometry proves genuine minimality among outside
Sylow overgroups, including the nontrivial two-core condition. -/
theorem rankOne_join_mem_HStar (T : Sylow 2 G) (D M : Subgroup G) (z : G)
    (hz : orderOf z = 2) (hzT : z ∈ T)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hDz : D ≤ centralizer ({z} : Set G))
    (hn : (T : Subgroup G) ≤ normalizer (D : Set G))
    (hf : RankOneBorelFacts D (T : Subgroup G)) (hout : ¬ D ≤ M)
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M) :
    D ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) M := by
  have hBM := borel_join_le_M T D M z hz hzT hTz hDz hn hf h25
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans hBM
  have hJH : D ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) :=
    mem_HOver_of_central_involution (T : Subgroup G) (D ⊔ (T : Subgroup G))
      z hz hzT le_sup_right (sup_le hDz hTz)
  have hJM : ¬ D ⊔ (T : Subgroup G) ≤ M :=
    fun he => hout (le_sup_left.trans he)
  change Minimal (fun Y : Subgroup G =>
    Y ∈ Chapter1.HOver G (T : Set G) ∧ ¬ Y ≤ M) (D ⊔ (T : Subgroup G))
  refine ⟨⟨hJH, hJM⟩, ?_⟩
  intro Y hY hYJ
  have hTY : (T : Subgroup G) ≤ Y := hY.1.2
  by_contra hne
  have hYD : Y ⊓ D < D := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro he
    apply hne
    apply sup_le _ hTY
    rw [← he]
    exact inf_le_left
  have hYB : Y ⊓ D ≤ borel D (T : Subgroup G) :=
    hf.unique_maximal _ (inf_le_inf hTY le_rfl) hYD
  apply hY.2
  intro x hx
  have hm : x ∈ (D : Set G) * ((T : Subgroup G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left D (T : Subgroup G) hn]
    exact hYJ hx
  obtain ⟨d, hd, t, ht, rfl⟩ := hm
  have hdY : d ∈ Y := by
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using Y.mul_mem hx (Y.inv_mem (hTY ht))
  have hBm : borel D (T : Subgroup G) ≤ M := le_sup_left.trans hBM
  exact M.mul_mem (hBm (hYB ⟨hdY, hd⟩)) (hTM ht)

/-- An actual Suzuki two-core quotient supplies all Borel premises; the
Sylow intersection is derived from relative normalization. -/
theorem suzuki_borelFacts (T : Sylow 2 G) (D : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (D : Set G))
    {m : ℕ} (e : (D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    RankOneBorelFacts D (T : Subgroup G) := by
  let J := D ⊔ (T : Subgroup G)
  obtain ⟨S, hS⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
    (show D ≤ J from le_sup_left) (sup_le D.le_normalizer hn)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)] at hS
  apply rankOneBorelFacts_of_quotient D T S hS
  exact rankOneSylowFacts_of_equiv (quotientSylow S) e (suzuki_rankOneSylowFacts m _)

/-- The Borel step of 13.6.27 for a normalized component with its literal
Suzuki quotient. Normalization and model identification remain upstream inputs. -/
theorem suzuki_join_mem_HStar (T : Sylow 2 G) (D M : Subgroup G) (z : G)
    (hz : orderOf z = 2) (hzT : z ∈ T)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hDz : D ≤ centralizer ({z} : Set G))
    (hn : (T : Subgroup G) ≤ normalizer (D : Set G))
    {m : ℕ} (e : (D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hout : ¬ D ≤ M)
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M) :
    D ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) M :=
  rankOne_join_mem_HStar T D M z hz hzT hTz hDz hn (suzuki_borelFacts T D hn e) hout h25

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
