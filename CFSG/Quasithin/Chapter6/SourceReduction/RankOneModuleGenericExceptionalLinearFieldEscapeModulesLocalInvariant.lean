module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalClosure
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesNatural
public import Theory.GroupTheory.SylowIndexThreeProduct
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator

/-!
# Full local invariance of the original cubic closure

The original index-three calculation gives the literal product L₂T = CT.
Since T normalizes the H-span U₀, its C-orbit span N is already its full
L₂T-orbit span. Thus L₂T normalizes N, without a nonabelian-span assumption.

If N is elementary, the full centralizer span U, which lies in T, acts
on N and [N,[N,U]] = 1. The actual conjugation coordinates therefore make
the projected N-action on U/⟨z⟩ quadratic. The Chapter12 application
supplies elementarity and nontriviality from the contrary source branch.

Source: Aschbacher--Smith G.2.3 and 5.1.21--23, printed pp.333--334,
644--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B C : Subgroup G} {n : ℕ} {z : G}

private theorem cubic_sylow_product
    (c : LinearFieldCartan T L H A B C n)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    (C : Set G) * (T : Set G) = (actor T C ⊔ (T : Subgroup G) : Subgroup G) := by
  let J := actor T C ⊔ (T : Subgroup G)
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hCJ : C ≤ J := (le_conjugateSpanBy C (T : Subgroup G)).trans le_sup_left
  have hi : (T : Subgroup G).relIndex J = 3 := by
    have hh := ((T : Subgroup G).subgroupOf J).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hTJ).toEquiv] at hh
    change Nat.card T * (T : Subgroup G).relIndex J = Nat.card J at hh
    rw [cartan_cubic_join_card c hTL hpsl, Nat.mul_comm 3] at hh
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := T)) hh
  have hd : Disjoint (T : Subgroup G) C := by
    obtain ⟨m,hm⟩ := T.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hm,c.cubic_card]
    exact (by decide : Nat.Coprime 2 3).pow_left m
  apply coe_mul_eq_of_relIndex_eq hCJ hTJ
  rw [← inf_relIndex_right, hd.eq_bot, relIndex_bot_left, c.cubic_card, hi]

/-- The cubic closure is the full orbit under the cubic--Sylow join. -/
theorem LocalData.local_cubic_span_eq_join_span
    (c : LinearFieldCartan T L H A B C n)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (d : LocalData T H C z) :
    conjugateSpanBy (setup T H C z).U C =
      conjugateSpanBy (setup T H C z).U (actor T C ⊔ (T : Subgroup G)) := by
  apply le_antisymm
    (conjugateSpanBy_mono le_rfl ((le_conjugateSpanBy _ _).trans le_sup_left))
  apply (closure_le _).mpr
  rintro _ ⟨j,hj,u,hu,rfl⟩
  have hj' : j ∈ (C : Set G) * (T : Set G) := by
    rw [cubic_sylow_product c hTL hpsl]
    exact hj
  obtain ⟨a,ha,t,ht,rfl⟩ := hj'
  have hTU : (T : Subgroup G) ≤ normalizer ((setup T H C z).U : Set G) :=
    (le_sup_right.trans d.g2.local_le).trans (le_normalizer_conjugateSpanBy _ _)
  exact subset_closure ⟨a,ha,t*u*t⁻¹,(mem_normalizer_iff.mp (hTU ht) u).mp hu,by group⟩

/-- No nonabelian-span assumption is needed for this full local normalization. -/
theorem LocalData.local_cubic_span_join_normalized
    (c : LinearFieldCartan T L H A B C n)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (d : LocalData T H C z) :
    actor T C ⊔ (T : Subgroup G) ≤
      normalizer (conjugateSpanBy (setup T H C z).U C : Set G) := by
  rw [d.local_cubic_span_eq_join_span c hTL hpsl]
  exact le_normalizer_conjugateSpanBy _ _

/-- The elementary cubic closure acts quadratically on the full centralizer span. -/
theorem LocalData.local_cubic_span_image_quadratic
    (c : LinearFieldCartan T L H A B C n)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (setup T H C z).U C)) :
    IsQuadratic (SpanAction.representation s)
      (((conjugateSpanBy (setup T H C z).U C).subgroupOf
        (centralizer ({z} : Set G))).map (SpanAction.projection s)) := by
  let N := conjugateSpanBy (setup T H C z).U C
  let D := setup T (centralizer ({z} : Set G)) C z
  let : IsElementaryAbelian 2 N := he
  have hUN : D.U ≤ normalizer (N : Set G) :=
    s.U_normal_in_T.1.trans (le_sup_right.trans
      (d.local_cubic_span_join_normalized c hTL hpsl))
  have hc : ⁅N,⁅N,D.U⁆⁆ = ⊥ := by
    apply bot_unique
    exact (commutator_mono le_rfl
      (le_normalizer_iff_commutator_le_left.mp hUN)).trans
        (commutator_eq_bot_iff_le_centralizer.mpr N.le_centralizer).le
  exact Representation.BinaryConjugationSection.isQuadratic_of_triple_commutator_le
    D.H D.U D.V₁ N (SpanAction.representation s) (SpanAction.projection s)
    (SpanAction.conjugationSection s) (hc.le.trans bot_le)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
