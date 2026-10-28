module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureScalarSplitting
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralPointRestriction

/-!
# The original whole core splits under the scalar residual

The actual cubic complement acts coprimely on the whole two-core of KT.
Its fixed subgroup equals the fixed subgroup of X because the chosen U
centralizes that core. Coprime decomposition and [O₂(KT),X]=U then give
the entire core, with its full fixed factor retained. The scalar action
kernel on U is also exactly U, using the original nonzero vector.

Source: the opening reduction of Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Retain the full scalar action kernel and the full residual-fixed
factor in the unchanged two-core of KT. -/
theorem original_tripleSix_central_closure_core_scalar_splitting
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let X := tripleSixScalarResidual K
    let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
    X ⊓ centralizer (U : Set G) = U ∧
      Q = U ⊔ (Q ⊓ centralizer (X : Set G)) ∧
      Disjoint U (Q ⊓ centralizer (X : Set G)) := by
  let X := tripleSixScalarResidual K
  let M := K ⊔ (T : Subgroup G)
  let Q := M.pCoreIn 2
  obtain ⟨hk,Y,hYX,hYcard,hXY,_⟩ :=
    original_tripleSix_central_closure_scalar_splitting h structural D a z hz hzT hnot houter
  change X ⊓ K.pCoreIn 2=U at hk
  change Y ≤ X at hYX
  change X=U ⊔ Y at hXY
  have hUX : U ≤ X := (original_tripleSix_scalar_residual_contains_module
    h structural D a z hz hzT hnot houter).1
  have hXM : X ≤ M := (map_subtype_le _).trans le_sup_left
  have hXQ : X ≤ normalizer (Q : Set G) := hXM.trans (M.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image M (pCore 2 M)))
  have hcentral : U ≤ centralizer (Q : Set G) := le_centralizer_iff.mp D.core_centralizes
  have hkernel : X ⊓ centralizer (U : Set G)=U := by
    apply le_antisymm
    · apply le_trans _ hk.le
      refine le_inf inf_le_left ?_
      exact (inf_le_inf_left X (centralizer_le (Set.singleton_subset_iff.mpr z.property))).trans
        (tripleSixScalarResidual_point_centralizer_le_core D a z hz)
    · let := D.elementary
      exact le_inf hUX (Subgroup.le_centralizer U)
  have hfixY : Q ⊓ centralizer (Y : Set G)=Q ⊓ centralizer (X : Set G) := by
    apply le_antisymm
    · refine le_inf inf_le_left ?_
      apply le_centralizer_iff.mp
      rw [hXY]
      exact sup_le (hcentral.trans (centralizer_le inf_le_left))
        (le_centralizer_iff.mp inf_le_right)
    · exact inf_le_inf_left _ (centralizer_le hYX)
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card Q) := by
    rw [hYcard]
    obtain ⟨n,hn⟩ := (isPGroup_pCoreIn 2 M).exists_card_eq
    change Nat.card Q=2^n at hn
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  let : Group.IsNilpotent Q := (isPGroup_pCoreIn 2 M).isNilpotent
  have hs := eq_commutator_sup_centralizer_of_solvable_coprime Q Y
    (hYX.trans hXQ) inferInstance hcop
  rw [hfixY] at hs
  have hbound := original_tripleSix_central_closure_scalar_core h structural D a z hz hzT hnot houter
  refine ⟨hkernel,le_antisymm ?_ (sup_le D.le_core inf_le_left),disjoint_iff.mpr ?_⟩
  · exact hs.le.trans (sup_le_sup ((commutator_mono le_rfl hYX).trans hbound) le_rfl)
  · apply bot_unique
    exact (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans
      (tripleSixScalarResidual_fixed_eq_bot D a).le

end CFSG.Quasithin.Chapter12.Section07
