module

public import CFSG.Quasithin.ChapterE.Section05.LocalGeneration
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.BinaryRankDifference
public import Stellmacher.MaxElementaryOffenderEquality

/-!
# Rank bounds for local centralizer covers

Let A have rank m₂(P)-i, and let B ≤ A have codimension at most j.
If the elementary subgroup E ≤ P commutes with B, then E ∩ B has
codimension at most i+j in E. Indeed B E is elementary in P, so
m(B)+m(E/(E∩B)) ≤ m₂(P), whereas m(B) ≥ m₂(P)-i-j.

Together with the conjugate-centralizer cover, this is the counting and
normal-generation argument in the last paragraph of E.5.2. It also gives
the centralizing-residual case. The structural hypotheses producing the
local subgroup and quotient-rank bound are explicit.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), E.5.2, printed p.243.
-/

open Subgroup Stellmacher CFSG.Quasithin.ChapterB
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

private theorem card_pow_log (E : Type*) [Group E] [Finite E]
    [IsElementaryAbelian 2 E] : Nat.card E = 2 ^ Nat.log 2 (Nat.card E) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  rw [hn, Nat.log_pow Nat.one_lt_two]

private theorem index_pow_log (E B : Subgroup G) [IsElementaryAbelian 2 E] :
    B.relIndex E = 2 ^ Nat.log 2 (B.relIndex E) := by
  rw [relIndex_eq_two_pow_quotient_finrank, Nat.log_pow Nat.one_lt_two]

/-- A large subgroup of A bounds the codimension of its intersection with E. -/
public theorem elementary_relativeIndex_le_of_thompsonFamily (P A B E : Subgroup G)
    {i j : ℕ} (hA : A ∈ thompsonFamily P i) (hBA : B ≤ A)
    (hB : Nat.log 2 (B.relIndex A) ≤ j)
    [IsElementaryAbelian 2 E] (hEP : E ≤ P)
    (hBE : B ≤ centralizer (E : Set G)) :
    Nat.log 2 ((E ⊓ B).relIndex E) ≤ i + j := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hBA
  have hJoin : IsElementaryAbelian 2 ↥(B ⊔ E) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hBE)
  have hmax := elementary_card_le_maxOrder P (B ⊔ E)
    (sup_le (hBA.trans hA.1) hEP) hJoin
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes B E
    ((le_centralizer_iff.mp hBE).trans (Subgroup.centralizer_le_normalizer _))
  have hIE : Nat.card ↥(B ⊓ E) * B.relIndex E = Nat.card E := by
    simpa only [relIndex_bot_left, inf_relIndex_right] using
      relIndex_mul_relIndex (⊥ : Subgroup G) (B ⊓ E) E bot_le inf_le_right
  have hBJ : Nat.card B * B.relIndex E = Nat.card ↥(B ⊔ E) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(B ⊓ E)))
    calc
      Nat.card ↥(B ⊓ E) * (Nat.card B * B.relIndex E) =
          Nat.card B * (Nat.card ↥(B ⊓ E) * B.relIndex E) := by ac_rfl
      _ = Nat.card B * Nat.card E := by rw [hIE]
      _ = _ := hprod
  have hBAcard : Nat.card B * B.relIndex A = Nat.card A := by
    simpa only [relIndex_bot_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) B A bot_le hBA
  rw [← hBJ, card_pow_log B, index_pow_log E B, ← pow_add,
    maxOrder_eq_two_pow_rank] at hmax
  have hmax' := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hmax
  rw [card_pow_log B, index_pow_log A B, ← pow_add, card_pow_log A] at hBAcard
  have hBA' := (Nat.pow_right_injective (by decide : 2 ≤ 2)) hBAcard
  have hAr := ((mem_thompsonFamily_iff_rank P A i).mp hA).2.2
  rw [inf_relIndex_left]
  omega

/-- The last paragraph of E.5.2, once the local elementary overgroup and
the rank bound on the intersection of A with the core have been obtained. -/
public theorem residual_le_generators_of_elementary_cover
    (P : Sylow 2 G) (i j : ℕ) (hij : i + j < twoRank (P : Subgroup G))
    (A K B E : Subgroup G) (hA : A ∈ thompsonFamily (P : Subgroup G) i)
    (hK : IsEMember (P : Subgroup G) A K)
    (hBA : B ≤ A) (hB : Nat.log 2 (B.relIndex A) ≤ j)
    [IsElementaryAbelian 2 E] (hEP : E ≤ (P : Subgroup G))
    (hBE : B ≤ centralizer (E : Set G))
    (hDE : higherThompsonCenter (P : Subgroup G) (i + j) ≤ E)
    (hKE : K ≤ normalizer (E : Set G)) :
    (pResidual 2 K).map K.subtype ≤
      thompsonCentralizerGenerators (P : Subgroup G) i j := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  apply residual_le_thompsonCentralizerGenerators_of_cover P i j hij A K E (E ⊓ B)
    hK hDE hKE
  · exact (le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative A)).trans
      (centralizer_le (inf_le_right.trans hBA))
  · exact elementary_relativeIndex_le_of_thompsonFamily _ A B E hA hBA hB hEP hBE

/-- The centralizing-residual case of E.5.2. Only the actual image-rank
bound on A is used; no bound on the rank of the whole core quotient is needed. -/
public theorem residual_le_generators_of_centralizes_core
    (P : Sylow 2 G) (i j : ℕ) (hij : i + j < twoRank (P : Subgroup G))
    (A K : Subgroup G) (hA : A ∈ thompsonFamily (P : Subgroup G) i)
    (hRank : Nat.log 2 ((A ⊓ (pCore 2 K).map K.subtype).relIndex A) ≤ j)
    (hC : (pResidual 2 K).map K.subtype ≤
      centralizer ((pCore 2 K).map K.subtype : Set G)) :
    (pResidual 2 K).map K.subtype ≤
      thompsonCentralizerGenerators (P : Subgroup G) i j := by
  let D := higherThompsonCenter (P : Subgroup G) (i + j)
  let B := A ⊓ (pCore 2 K).map K.subtype
  let _ : IsElementaryAbelian 2 D := omegaOneCenterAmbient_elementaryAbelian _
  have hAD : A ≤ centralizer (D : Set G) :=
    le_centralizer_iff.mp (higherThompsonCenter_le_centralizer _ A i j hA hij)
  have hr := elementary_relativeIndex_le_of_thompsonFamily (P : Subgroup G) A B D
    hA inf_le_left hRank (higherThompsonCenter_le _ _) (inf_le_left.trans hAD)
  apply (hC.trans (centralizer_le
    (show D ⊓ B ≤ (pCore 2 K).map K.subtype from inf_le_right.trans inf_le_right))).trans
  exact centralizer_le_thompsonCentralizerGenerators P i j hij (D ⊓ B) ⟨inf_le_left, hr⟩

end CFSG.Quasithin.ChapterE
