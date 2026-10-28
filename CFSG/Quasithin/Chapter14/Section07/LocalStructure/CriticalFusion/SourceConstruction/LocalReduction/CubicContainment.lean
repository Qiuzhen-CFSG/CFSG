module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicHeisenbergExclusion

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCoreEquality

/-!
# Cubic containment and the order-four chief-interval exclusion

In the normal-point branch, O₂(H) moves V₂ while the plane-parabolic
core fixes V₂ and has index two in T. Thus those two cores generate T.
For an escaping cubic Y, the solvable-model reduction and the binary
Heisenberg norm calculation make both vertex cores equal O₂(D).
Consequently Y normalizes the plane core as well as O₂(H), so it
normalizes T. This is impossible in the literal S₃ quotient of YT.

This proves the normal-point specialization of 14.5.3(2) needed by the
original extraspecial reduction. Applied to the escaping cubic constructed
from an order-four chief interval, it excludes that interval. The final
original-group reduction preserves the exact order-sixteen kernel and
both central flanks, together with the established central and faithful
order-sixty-four alternatives. The order-sixteen exclusion and the full
residual classification through 14.7.52 remain required.

Source: Aschbacher–Smith, 14.5.3(2), printed p.1013; 14.5.12–13,
pp.1016–1017; 14.7.4(1), p.1043; and 14.7.20, p.1049,
refs/quasithin.pdf. No Data or extra local classification premise is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem plane_core_sylow_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ((F.P L).pCoreIn 2).relIndex (T : Subgroup G) = 2 := by
  let P := F.P L
  let S := T.subtype (F.binary_sylow_le_P L)
  let e := planeParabolicQuotientEquiv (F := F) h structural
  have hi := relIndex_mul_index (pCore_isPGroup.le_sylow_of_normal S)
  rw [SymmetricThreeTwoCore.core_index e,SymmetricThreeTwoCore.sylow_index_three e S] at hi
  have hi2 : (pCore 2 P).relIndex (S : Subgroup P) = 2 := by
    dsimp only [P]
    omega
  have he := relIndex_map_map_of_injective (pCore 2 P) (S : Subgroup P) P.subtype_injective
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.binary_sylow_le_P L)] at he
  exact he.trans hi2

/-- The point-normalizer core supplements the literal plane core in T. -/
theorem cubic_point_core_plane_core_generate_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    F.H.pCoreIn 2 ⊔ (F.P L).pCoreIn 2 = (T : Subgroup G) := by
  let := h.chosen.elementary
  let A := F.H.pCoreIn 2
  let B := (F.P L).pCoreIn 2
  have hAT : A ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
    exact hh.trans_eq (map_subgroupOf_eq_of_le (F.invariant 1))
  have hBT : B ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (F.P L) (T.subtype (F.binary_sylow_le_P L))
    exact hh.trans_eq (map_subgroupOf_eq_of_le (F.binary_sylow_le_P L))
  have hBC : B ≤ centralizer (F.Vi 2 : Set G) := by
    change (F.P L).pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)
    rw [←(F.binary_parabolic_core (by decide) L h.chosen.normalizes
      (h.full_LT_action structural) (h.centralizer_LT structural)).1]
    exact inf_le_right
  have hnot : ¬ A ≤ B := fun hh => plane_moved_of_point_normal h structural hn (hh.trans hBC)
  have hi : B.relIndex (T : Subgroup G) = 2 := plane_core_sylow_index h structural
  have hjoin := sup_le hAT hBT
  have hd : (A ⊔ B).relIndex (T : Subgroup G) ∣ 2 := by
    have hd := relIndex_dvd_of_le_left (T : Subgroup G) (show B ≤ A ⊔ B from le_sup_right)
    rwa [hi] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact le_antisymm hjoin (relIndex_eq_one.mp h1)
  · have hh := relIndex_mul_relIndex B (A ⊔ B) (T : Subgroup G) le_sup_right hjoin
    rw [hi,h2] at hh
    have h1 : B.relIndex (A ⊔ B) = 1 := by omega
    exact (hnot (le_sup_left.trans (relIndex_eq_one.mp h1))).elim

/-- In the normal-point branch, the source's T-invariant symmetric-three
subgroup is contained in the original normalizer. -/
theorem cubic_containment_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    Y ≤ normalizer (L : Set G) := by
  by_contra hout
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  have hYP : Y ≤ normalizer ((F.P L).pCoreIn 2 : Set G) := by
    rw [(cubic_generated_equal_two_cores h hab structural previous faithful hn
      Y hYH hYp hYT hout he).1]
    exact (show Y ≤ D from le_sup_left.trans le_sup_right).trans
      (D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))
  have hYHcore : Y ≤ normalizer (F.H.pCoreIn 2 : Set G) :=
    hYH.trans (F.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))
  have hYTnorm : Y ≤ normalizer (T : Set G) := by
    change Y ≤ normalizer ((T : Subgroup G) : Set G)
    rw [←cubic_point_core_plane_core_generate_sylow h structural hn]
    exact (le_inf hYHcore hYP).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let B := Y ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ B from le_sup_right)
  have hBnorm : B ≤ normalizer (T : Set G) := sup_le hYTnorm (T : Subgroup G).le_normalizer
  have hSnorm : (S : Subgroup B).Normal := normal_subgroupOf_of_le_normalizer hBnorm
  have hs : (S : Subgroup B) = ⊤ := by
    rw [←SymmetricThreeTwoCore.sylow_self_normalizing he.some S]
    exact (normalizer_eq_top_iff.mpr hSnorm)
  have hi := SymmetricThreeTwoCore.sylow_index_three he.some S
  rw [hs,index_top] at hi
  omega

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The original point-central chief interval cannot have order four. -/
theorem extraspecial_no_four_interval
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype) :
    Nat.card (Section N B) ≠ 4 := by
  intro hc
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact hout (cubic_containment_of_point_normal h hab structural previous faithful hn Y hYH hYp hYT he)

open NoncentralChiefRefinement in
/-- The original centralizer-core reduction with the order-four interval removed.
The order-sixteen interval retains its exact kernel and both central flanks. -/
theorem extraspecial_centralizer_core_reduction_no_four
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (((F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2) ∧
      (⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
        ∃ N B : NormalNode F.H, N ⋖ B ∧
          F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
          ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
          Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)) ∨
    (⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U ∧
      ∃ N B : NormalNode F.H, N ⋖ B ∧
        F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
        ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
        Nat.card (Section N B) = 16 ∧
        (sectionAction N B).ker = pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ∧
        ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
        ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U) := by
  rcases extraspecial_centralizer_core_reduction h hab structural previous he with hc | hp
  · exact Or.inl hc
  obtain ⟨hp,N,B,hNB,hUN,hBC,hm,hker,h4 | h16⟩ := hp
  · obtain ⟨e⟩ := he
    have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
      (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
    have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
      (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
    have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
      (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
    exact (extraspecial_no_four_interval h hab structural previous faithful hex hcard hexp
      N B hNB hUN hBC hp hm h4.1).elim
  · exact Or.inr ⟨hp,N,B,hNB,hUN,hBC,hm,h16⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
