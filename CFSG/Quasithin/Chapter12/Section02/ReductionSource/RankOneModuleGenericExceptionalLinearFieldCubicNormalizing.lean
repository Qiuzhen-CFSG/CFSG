module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldCubicNormalizing
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearField

/-!
# Source applications of the inner cubic and field-size reductions

The first application places the literal cubic in the right Cartan and
therefore in the centralizer of Ω₁(Z(T)). The second combines this with
the two distinct later source steps: for n>2, 5.1.19 gives n≡2 mod 4 and
3∤n, whereas 5.1.20 gives n/2≤4. These force n=6 and a contradiction.
The Cartan orders then identify A=C=B, giving the full Borel containment.

The kernel, inner-action and large-field premises remain explicit until
their source producers discharge them. In particular 5.1.19 alone does
not prove n=2. This remains a conditional assembly of the normalizing branch.

Source: Aschbacher--Smith 5.1.18--20, printed pp.642--644; 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The actual chosen setup obtains cubic centralization from inner action;
no independent centralization premise is used. -/
theorem linear_cubic_eq_right_and_centralizes_of_inner
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (c : LinearFieldCartan T L H A B C n)
    (hCN : C ≤ normalizer (residual H : Set G))
    (hker : Nat.Coprime 3 (Nat.card (linearResidualAction H).ker))
    (hinner : (C.subgroupOf (normalizer (residual H : Set G))).map
      (linearResidualAction H) ≤
        (MulAut.conj : ((residual H) ⧸ pCore 2 (residual H)) →*
          MulAut ((residual H) ⧸ pCore 2 (residual H))).range) :
    C = B ∧ C ≤ omegaCentralizer T := by
  have he := c.cubic_eq_right_of_inner hCN hker hinner
  exact ⟨he, he.symm ▸ (c.right_le.trans inf_le_right).trans
    (D.linear_field_source_geometry h hH hK hnf).1⟩

/-- The numerical source steps finish the normalizing branch on the original
chosen setup. Both source implications remain genuine unproved premises. -/
theorem field_four_and_borel_of_linear_inner_cubic_sources
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (c : LinearFieldCartan T L H A B C n)
    (hCN : C ≤ normalizer (residual H : Set G))
    (hker : Nat.Coprime 3 (Nat.card (linearResidualAction H).ker))
    (hinner : (C.subgroupOf (normalizer (residual H : Set G))).map
      (linearResidualAction H) ≤
        (MulAut.conj : ((residual H) ⧸ pCore 2 (residual H)) →*
          MulAut ((residual H) ⧸ pCore 2 (residual H))).range)
    (hlarge : C = B → 2 < n → n % 4 = 2 ∧ ¬ 3 ∣ n ∧ n / 2 ≤ 4) :
    n = 2 ∧ localBorel T L ≤ omegaCentralizer T := by
  have hCB := c.cubic_eq_right_of_inner hCN hker hinner
  have hn2 : n = 2 := by
    by_contra hne
    obtain ⟨hmod, hthree, hbound⟩ := hlarge hCB (by omega)
    have hn6 : n = 6 := by omega
    exact hthree (hn6.symm ▸ (by decide : 3 ∣ 6))
  exact c.field_four_and_borel D.sylow_normalizes_component
    (D.linear_field_source_geometry h hH hK hnf).1
    (c.left_eq_right_of_cubic_eq hn2 hCB)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
