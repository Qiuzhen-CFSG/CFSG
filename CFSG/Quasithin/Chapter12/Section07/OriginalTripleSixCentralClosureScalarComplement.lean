module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureCoreRecovery
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureScalarFrattini

/-!
# The actual scalar-cubic complement in the original central-closure normalizer

The original scalar residual has an actual cubic subgroup whose full
normalizer is disjoint from U and supplements U in KT. The secondary-module
contradiction and core recovery identify KT with the whole N_G(K). Transport
the same cubic and its literal normalizer into N_G(K) to obtain an internal
complement to the full original kernel U.

Source: Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The normalizer of an actual scalar cubic complements the whole original
module U in N_G(K); the cubic lies in the literal scalar residual in G. -/
theorem original_tripleSix_central_closure_scalar_complement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧ RankOneModule.SmallExit T (localResidual H))
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let M := normalizer (K : Set G)
    ∃ Y : Subgroup M, Nat.card Y = 3 ∧
      Y.map M.subtype ≤ tripleSixScalarResidual K ∧
      (U.subgroupOf M).IsComplement' (normalizer (Y : Set M)) := by
  obtain ⟨_,_,_,hNU,_,hM⟩ := original_tripleSix_central_closure_core_recovery
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  obtain ⟨Y,hYX,hYcard,_,hsplit,_,hdis⟩ :=
    original_tripleSix_central_closure_scalar_frattini h structural D a z hz hzT hnot houter
  let M := normalizer (K : Set G)
  change M = K ⊔ (T : Subgroup G) at hM
  have hUM : U ≤ M := D.le_component.trans K.le_normalizer
  have hYM : Y ≤ M := hYX.trans ((map_subtype_le _).trans K.le_normalizer)
  let Y' := Y.subgroupOf M
  let V := U.subgroupOf M
  let C := normalizer (Y' : Set M)
  have hCmap : C.map M.subtype = M ⊓ normalizer (Y : Set G) := by
    change (normalizer (Y.subgroupOf M : Set M)).map M.subtype = _
    rw [←subgroupOf_normalizer_eq hYM,subgroupOf_map_subtype,inf_comm]
  have hVC : Disjoint V C := by
    apply disjoint_def.mpr
    intro x hx hxC
    apply Subtype.ext
    exact disjoint_def.mp hdis hx (show (x : G) ∈ normalizer (Y : Set G) from
      (hCmap ▸ mem_map_of_mem M.subtype hxC).2)
  have hsup : V ⊔ C = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hUM,hCmap,
      ←MonoidHom.range_eq_map,range_subtype]
    rw [hM]
    exact hsplit.symm
  let : V.Normal := normal_subgroupOf_of_le_normalizer hNU.symm.le
  refine ⟨Y',(Nat.card_congr (subgroupOfEquivOfLe hYM).toEquiv).trans hYcard,
    (map_subgroupOf_eq_of_le hYM).le.trans hYX,?_⟩
  apply isComplement'_of_card_mul_and_disjoint ?_ hVC
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint V C
    (by rw [V.normalizer_eq_top]; exact le_top) hVC
  rw [hsup,Nat.card_congr Subgroup.topEquiv.toEquiv] at hc
  exact hc.symm

end CFSG.Quasithin.Chapter12.Section07
