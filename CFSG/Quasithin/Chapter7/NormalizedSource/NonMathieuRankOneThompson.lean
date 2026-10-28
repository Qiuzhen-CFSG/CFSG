module
public import CFSG.Quasithin.ChapterE.Section05.RankCover
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus
public import CFSG.Quasithin.ChapterE.Section06.Basic

/-!
# Near-offender exclusion and higher Thompson control

An elementary generator A of J_i(X), with V normal in X, has induced
fixed codimension at most rank(Aut_A(V)) + i. Compare C_A(V)V with a
largest elementary subgroup of X to obtain this bound. A strict bound
for all nontrivial induced actors therefore makes J_i(X) centralize V.
The rank-one consumer uses the Suzuki natural fixed-codimension calculation.
Source: Aschbacher--Smith B.2.2--7 and 7.4.1, pp.74--76,700.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterB ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The rank comparison behind the source higher-Thompson argument. -/
theorem thompson_family_fixedCodim_le (V X : Subgroup G)
    [IsElementaryAbelian 2 V] (hVX : V ≤ X)
    (hXN : X ≤ normalizer (V : Set G)) {i : ℕ}
    (A : Subgroup G) (hA : A ∈ thompsonFamily X i) :
    fixedCodim (automizerRepresentation V) (inducedAutomizer V A) ≤
      rank (inducedAutomizer V A) + i := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let C := A ⊓ centralizer (V : Set G)
  have hb := elementary_relativeIndex_le_of_thompsonFamily X A C V
    (i := i) (j := rank (inducedAutomizer V A)) hA inf_le_left
    (by rw [rank_inducedAutomizer V A (hA.1.trans hXN)]; exact le_rfl)
    hVX inf_le_right
  have hVA : V ⊓ C ≤ V ⊓ centralizer (A : Set G) :=
    le_inf inf_le_left ((inf_le_right.trans inf_le_left).trans A.le_centralizer)
  have hc := offender_corank_add hVA inf_le_left
  rw [fixedCodim_inducedAutomizer V A (hA.1.trans hXN)]
  change subgroupCorank V (V ⊓ C) ≤ _ at hb
  omega

/-- A strict codimension gap excludes every moving generator of J_i(X). -/
theorem thompson_centralizes_of_fixedCodim_gap (V X : Subgroup G)
    [IsElementaryAbelian 2 V] (hVX : V ≤ X)
    (hXN : X ≤ normalizer (V : Set G)) {i : ℕ}
    (hgap : ∀ A : Subgroup (Automizer V), IsElementaryTwo A →
      rank A + i < fixedCodim (automizerRepresentation V) A) :
    thompsonJ X i ≤ centralizer (V : Set G) := by
  apply sSup_le
  intro A hA
  by_contra hn
  let : IsElementaryAbelian 2 A := hA.2.1
  have hAN := hA.1.trans hXN
  have hAI : IsElementaryTwo (inducedAutomizer V A) :=
    ⟨fun hb => hn ((inducedAutomizer_eq_bot_iff hAN).mp hb),
      inducedAutomizer_elementary V A hAN⟩
  exact (not_lt_of_ge (thompson_family_fixedCodim_le V X hVX hXN A hA))
    (hgap _ hAI)

/-- Faithfulness bounds the fixed-space-family parameter by automizer rank. -/
theorem localA_le_automizer_rank (V : Subgroup G) [IsElementaryAbelian 2 V] :
    localA V ≤ (primeRank 2 (Automizer V) : ℕ∞) := by
  apply iSup_le
  intro k
  apply iSup_le
  rintro ⟨A,hA⟩
  let : IsElementaryAbelian 2 A := hA.2.1.2
  exact ENat.natCast_le_natCast.mpr
    ((parameter_le_rank_of_mem_fixedSpaceFamily _ (automizerRepresentation_injective V) hA).trans
      (offender_rank_le_primeRank A))
end CFSG.Quasithin.Chapter7.NormalizedSource
