module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Statements
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.KernelApplications
public import CFSG.Quasithin.Chapter4.Section04.OddActorResidual
public import Theory.GroupTheory.PCoreCoverEquiv

/-!
# The original nonbinary odd actor and its covering residual

Faithfulness of the literal central-quotient action identifies C_L(V) with
O2(L), including the full SL3 center. An actor centralizing the unchanged V
therefore centralizes L/O2(L). The perfect residual of C_L(A) covers L,
contains V in its two-core and generates V by commutators. The quotient
comparison records the original inclusion on every representative.
The natural marking also gives |V| at least 64, including nonsplit central parts.

Source: Aschbacher--Smith, Remark 4.4.2 and 4.4.5, printed pp.619--620;
the original nonbinary setup is on pp.759--760.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

theorem centralizer_eq_core : L ⊓ centralizer (V : Set G) = L.pCoreIn 2 := by
  have h := congrArg (Subgroup.map L.subtype)
    (D.actionCentralizer_eq_twoCore_of_injective S.faithful)
  simpa only [subgroupOf_map_subtype, inf_comm, pCoreIn] using h

theorem actor_commutator {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G)) :
    ⁅A,L⁆ ≤ L.pCoreIn 2 := by
  rw [← centralizer_eq_core D S]
  refine le_inf (le_normalizer_iff_commutator_le_right.mp (hA.trans inf_le_left)) ?_
  exact (commutator_mono (hA.trans inf_le_right) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp
      (D.normalizes.trans (normalizer_le_normalizer_centralizer V)))

theorem actor_cover {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (ho : Odd (Nat.card A)) :
    (L : Set G) = (oddActorResidual L A : Set G) * (L.pCoreIn 2 : Set G) ∧
    V = ⁅V,oddActorResidual L A⁆ ∧ V ≤ (oddActorResidual L A).pCoreIn 2 ∧
    (oddActorResidual L A).pCoreIn 2 ≠ ⊥ :=
  chosen_oddActorResidual_cover S.source.toHypothesis1221 D A (hA.trans inf_le_left)
    (actor_commutator D S hA) ho (hA.trans inf_le_right)

omit D S in
theorem cover_quotient {I : Subgroup G} (hIL : I ≤ L)
    (hc : (L : Set G) ⊆ (I : Set G) * (L.pCoreIn 2 : Set G)) :
    ∃ e : (I ⧸ pCore 2 I) ≃* (L ⧸ pCore 2 L),
      ∀ i : I, e (QuotientGroup.mk' (pCore 2 I) i) =
        QuotientGroup.mk' (pCore 2 L) (inclusion hIL i) :=
  exists_pCoreQuotientEquiv_of_cover hIL hc

/-- The residual has the same full quotient; no center is discarded. -/
theorem actor_cover_quotient {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (ho : Odd (Nat.card A)) :
    ∃ e : (oddActorResidual L A ⧸ pCore 2 (oddActorResidual L A)) ≃*
        (L ⧸ pCore 2 L),
      ∀ i : oddActorResidual L A, e (QuotientGroup.mk' (pCore 2 _) i) =
        QuotientGroup.mk' (pCore 2 L)
          (inclusion ((oddActorResidual_le L A).trans inf_le_left) i) :=
  cover_quotient ((oddActorResidual_le L A).trans inf_le_left) (actor_cover D S hA ho).1.subset

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

theorem module_card_ge : 64 ≤ Nat.card V := by
  have hq : 4 ≤ Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact Nat.pow_le_pow_right (n := 2) (by decide) S.nonbinary
  have hV : Nat.card D.chosenCentralQuotient ≤ Nat.card V := by
    exact (Nat.card_le_card_of_surjective D.toCentralQuotient D.toCentralQuotient_surjective)
  have h := hV
  cases S.natural with
  | sl3 hm =>
    rw [Nat.card_congr hm.some.linearEquiv.toEquiv, Nat.card_fun, Nat.card_fin] at h
    exact le_trans (show 64 ≤ Nat.card S.field.Carrier ^ 3 from
      Nat.pow_le_pow_left hq 3) h
  | sp4 hm =>
    rw [Nat.card_congr hm.some.linearEquiv.toEquiv, Nat.card_fun, Nat.card_sum,
      Nat.card_fin] at h
    exact le_trans (by have := Nat.pow_le_pow_left hq 4; norm_num at this ⊢; omega) h
  | g2 hm =>
    rw [Nat.card_congr hm.some.linearEquiv.toEquiv,
      Module.natCard_eq_pow_finrank (K := S.field.Carrier), Atlas.G2.Natural.finrank_space] at h
    exact le_trans (by have := Nat.pow_le_pow_left hq 6; norm_num at this ⊢; omega) h

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
