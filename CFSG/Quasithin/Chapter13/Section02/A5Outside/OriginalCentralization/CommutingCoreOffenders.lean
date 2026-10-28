module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.CoreOffender
public import CFSG.Quasithin.Chapter13.Section02.A5Local.EvenThompson
public import Theory.GroupTheory.NormalClosureCentralizerCore

/-!
# Opposite-module offenders in the two original cores

If both core Thompson subgroups centralized the opposite module, each
would lie in the intersection of the cores. Thompson heredity would make
them equal. This common nontrivial two-subgroup would be normalized by
both LT and the outside H, contradicting the original unique maximal
local overgroup. Thus one core Thompson subgroup moves the other module.

When the original natural modules commute, each lies in the opposite core.
The actual maximum elementary offender can therefore be extracted there.
Its odd action is measured by the same local actor or the supplied marked
H→S₅, respectively. No equality of core orders or bound on their orders is
needed. Source application: Aschbacher--Smith 13.2.8(1), p.880, using
13.2.4(1), B.2.3 and B.3.2(4). The residual lift remains a separate step.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative


namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

theorem original_pair_core_thompson_moves
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    (¬ elementaryAbelianMaxJ (H.pCoreIn 2) ≤ centralizer (V : Set G)) ∨
      (¬ elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤
        centralizer (W : Set G)) := by
  by_contra hn
  push Not at hn
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let P := H.pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) :=
    (d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left
  have hPT : P ≤ (T : Subgroup G) :=
    map_le_iff_le_comap.mpr (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2))
  have hJQ : elementaryAbelianMaxJ Q ≤ P := by
    change _ ≤ H.pCoreIn 2
    rw [←hjoin,←e.sylow_centralizer e.normalizes_L]
    exact le_inf ((sSup_le fun _ hA => hA.1).trans hQT) hn.2
  have hJP : elementaryAbelianMaxJ P ≤ Q := by
    rw [show Q = (T : Subgroup G) ⊓ centralizer (V : Set G) from
      (d.sylow_centralizer d.normalizes_L).symm]
    exact le_inf ((sSup_le fun _ hA => hA.1).trans hPT) hn.1
  have heq : elementaryAbelianMaxJ P = elementaryAbelianMaxJ Q := by
    have hp := elementaryAbelianMaxJ_eq_of_intermediate P (P ⊓ Q)
      (le_inf (sSup_le fun _ hA => hA.1) hJP) inf_le_left
    have hq := elementaryAbelianMaxJ_eq_of_intermediate Q (P ⊓ Q)
      (le_inf hJQ (sSup_le fun _ hA => hA.1)) inf_le_right
    exact hp.symm.trans hq
  have hQN : (L ⊔ (T : Subgroup G)) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))
  have hQne : Q ≠ ⊥ := fun hb => d.chosen.ne_bot (bot_unique (d.chosen.le_core.trans_eq hb))
  have hN := normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
    ((isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).to_le
      (show elementaryAbelianMaxJ Q ≤ Q from sSup_le fun _ hA => hA.1))
    (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q (isPGroup_pCoreIn 2 _) hQne)
    (hQN.trans (normalizer_le_normalizer_elementaryAbelianMaxJ Q))
  have hPN : H ≤ normalizer (P : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hHN := hPN.trans (normalizer_le_normalizer_elementaryAbelianMaxJ P)
  rw [heq] at hHN
  exact hH.1.2 (hHN.trans hN)
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- A commuting original pair has an elementary odd actor in at least one
of the two cores, measured on the opposite natural module. -/
theorem original_commuting_pair_core_offender
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (q : H →* Equiv.Perm (Fin 5)) (hk : q.ker = pCore 2 H)
    (he : ∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
      h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
        e.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q h) w)))
    (hVW : V ≤ centralizer (W : Set G)) :
    (∃ A ∈ elementaryAbelianMaxSubgroups (H.pCoreIn 2),
      ¬ (A.subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor ≤
        alternatingGroup (Fin 5)) ∨
    (∃ A ∈ elementaryAbelianMaxSubgroups ((L ⊔ (T : Subgroup G)).pCoreIn 2),
      ¬ (A.subgroupOf H).map q ≤ alternatingGroup (Fin 5)) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let P := H.pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) :=
    (d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left
  have hPT : P ≤ (T : Subgroup G) :=
    map_le_iff_le_comap.mpr (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2))
  have hVP : V ≤ P := by
    change V ≤ H.pCoreIn 2
    rw [←hjoin,←e.sylow_centralizer e.normalizes_L]
    exact le_inf d.chosen.le_sylow hVW
  have hWQ : W ≤ Q := by
    rw [show Q = (T : Subgroup G) ⊓ centralizer (V : Set G) from
      (d.sylow_centralizer d.normalizes_L).symm]
    exact le_inf e.chosen.le_sylow (le_centralizer_iff.mp hVW)
  rcases original_pair_core_thompson_moves d e hjoin hH with hmove | hmove
  · left
    apply d.max_elementary_odd_cross_action (L ⊔ (T : Subgroup G)) P
      (d.chosen.le_sylow.trans le_sup_right) hVP (hPT.trans le_sup_right)
      d.localActor d.localActor_kernel
      (sup_le d.chosen.normalizes d.flag.T_normalizes) _ hmove
    intro g v
    exact d.flag.normalizer_equivariant
      ⟨g.val,(sup_le d.chosen.normalizes d.flag.T_normalizes) g.property⟩ v
  · right
    have hWH : W ≤ H := e.chosen.le_sylow.trans hH.1.1.2
    have hCW := (e.local_centralizers e.normalizes_L).1
    rw [hjoin] at hCW
    have hkW : q.ker = centralizer (W.subgroupOf H : Set H) := by
      rw [hk]
      apply map_injective H.subtype_injective
      change H.pCoreIn 2 = _
      rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hWH]
      exact hCW.symm
    exact e.max_elementary_odd_cross_action H Q hWH hWQ (hQT.trans hH.1.1.2)
      q hkW (hjoin.ge.trans (sup_le e.chosen.normalizes e.flag.T_normalizes)) he hmove
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
