module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.Basic
public import Theory.GroupTheory.PResidual.MatchedQuotientCover
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# Mathieu deductions in the rank sieve

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 8.2.9, printed p.720 (PDF p.737).

For the cocode row the local quotient L_U/O₂(L_U) is L₃(2). Its trivial
centre and an element of order three supply the model inputs to the
residual-centralizer rank bound. The L₂(4) alternative then gives the literal
quotient cover: O²(I) maps onto I/O₂(I), and this quotient has the same
order as O²(H/O₂(H)). The existing residual lift gives the setwise product
H = IT and the required normalizer conclusions.

These are conditional branch deductions. The bound n(H) ≤ 2, the stronger
3′ assertion in the code row, and the inspection of the complete E.2.2 and
B.6.8 lists remain required for the full sieve. In particular no rank bound
on H or quotient-cover conclusion is assumed in the rank deduction, and
the L₂(4) branch retains both actual model isomorphisms. No binary tensor
identity from the inconsistent printed cocode formula is used.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.Mathieu

private theorem linear_three_two_rank : 1 ≤ primeRank 3 Matrix.PSL3Two.SL := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Matrix.PSL3Two.SL) 3
    (by rw [Matrix.PSL3Two.card_SL]; decide)
  let : IsElementaryAbelian 3 (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (by
      simpa only [hx] using pow_orderOf_eq_one x)
  exact IsElementaryAbelian.primeRank_ge_of_card (zpowers x) (by
    simpa only [Nat.card_zpowers, pow_one] using hx)

private theorem linear_two_four_residual
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4) :
    pResidual 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = ⊤ := by
  let S := Matrix.ProjectiveSpecialLinearGroup (Fin 2) F
  let : Group.IsPerfect S := GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
  apply (pResidual_eq_top_iff 2 S).mpr
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (S ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (S ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (S ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (S ⧸ N) inferInstance

variable {G : Type*} [Group G] [Finite G]

/-- The marked L₃(2) quotient in 8.2.6 gives the cocode three-rank bound. -/
theorem cocode_three_rank_le_one
    (T : Sylow 2 G) (L M H I U : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hIH : I ≤ H) (hIM : ¬ I ≤ M)
    (hIC : I ≤ centralizer (U : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hcomm : ⁅localResidual L U, centralizer (U : Set G)⁆ ≤
      (localResidual L U).pCoreIn 2)
    (e : (localResidual L U ⧸ pCore 2 (localResidual L U)) ≃* Matrix.PSL3Two.SL)
    (hjoin : primeRank 3 (H ⊔ localResidual L U : Subgroup G) ≤ 2) :
    primeRank 3 H ≤ 1 := by
  apply three_rank_le_one_of_local_model T L M H I U hH hIH hIM hIC hTL hTU
    hcomm e _ hjoin
  exact Or.inl ⟨by rw [Matrix.PSL3Two.center_eq_bot, card_bot]; decide,
    linear_three_two_rank⟩

/-- The actual L₂(4) alternative covers O²(H⁺); I need not be normal in H. -/
theorem cocode_linear_quotient_cover (I : Subgroup G)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eI : (I ⧸ pCore 2 I) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (eR : pResidual 2 (G ⧸ pCore 2 G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    pResidual 2 (G ⧸ pCore 2 G) ≤ I.map (QuotientGroup.mk' (pCore 2 G)) :=
  quotient_residual_le_of_matching_pPerfect_model I (linear_two_four_residual hF) eI eR

/-- The L₂(4) cocode alternative proves 8.2.9(1–2) on the literal subgroup pair. -/
theorem cocode_linear_conclusions
    (T : Sylow 2 G) (V I A : Subgroup G) (h : G)
    (hh : h ∈ I) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hP : A ⊔ (V ⊓ I.pCoreIn 2) = I.pCoreIn 2)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eI : (I ⧸ pCore 2 I) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (eR : pResidual 2 (G ⧸ pCore 2 G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    (pResidual 2 I).map I.subtype = pResidual 2 G ∧
      (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) ∧
      (Set.univ : Set G) = (I : Set G) * (T : Set G) ∧
      (T : Subgroup G) ≤ normalizer ((V ⊔ A : Subgroup G) : Set G) :=
  conclusions_of_quotient_cover T V I A h hh hTV hgen hP
    (cocode_linear_quotient_cover I hF eI eR)

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.Mathieu
