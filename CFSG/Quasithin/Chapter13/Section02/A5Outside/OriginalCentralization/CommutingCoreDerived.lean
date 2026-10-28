module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableCores
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalizedCommutator

/-!
# Noncyclic derived subgroups in the original commuting cores

The two original local cores are incomparable. Consequently each moves
the opposite natural module. Their Sylow normalization and the same
surjective local markings force an elementary commutator of order at least
four. When the natural modules commute, each is inside the opposite core,
so neither core can have a cyclic derived subgroup.

Both relative cores, original contexts and literal action maps are kept.
SourceAssembly/NonsolvableDerived applies this obstruction to construct
an actual residual four-group lift and invoke 5.2.3 in the cyclic-derived
case. Source: Aschbacher--Smith 13.2.8(1), p.880, and 13.2.3--4, pp.878--879.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- A commuting original pair has noncyclic derived subgroups in both cores. -/
theorem original_commuting_pair_noncyclic_cores
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hd : Function.Surjective d.localActor)
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 H)
    (he : ∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
      h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
        e.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q h) w)))
    (hVW : V ≤ centralizer (W : Set G)) :
    ¬ IsCyclic (⁅H.pCoreIn 2,H.pCoreIn 2⁆ : Subgroup G) ∧
      ¬ IsCyclic (⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,
        (L ⊔ (T : Subgroup G)).pCoreIn 2⁆ : Subgroup G) := by
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
  have hTP : (T : Subgroup G) ≤ normalizer (P : Set G) :=
    hH.1.1.2.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))))
  obtain ⟨hPQ,hQP⟩ := original_pair_cores_incomparable d hH hd q hq hk
  have hPV : ¬ P ≤ centralizer (V : Set G) := by
    intro h
    apply hPQ
    rw [←d.sylow_centralizer d.normalizes_L]
    exact le_inf hPT h
  have hQW : ¬ Q ≤ centralizer (W : Set G) := by
    intro h
    apply hQP
    rw [←hjoin,←e.sylow_centralizer e.normalizes_L]
    exact le_inf hQT h
  have hWH : W ≤ H := e.chosen.le_sylow.trans hH.1.1.2
  have hCW := (e.local_centralizers e.normalizes_L).1
  rw [hjoin] at hCW
  have hkW : q.ker = centralizer (W.subgroupOf H : Set H) := by
    rw [hk]
    apply map_injective H.subtype_injective
    change H.pCoreIn 2 = _
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hWH]
    exact hCW.symm
  refine ⟨d.noncyclic_derived_of_sylow_normal (L ⊔ (T : Subgroup G)) P
    le_sup_right hVP hPT hTP d.localActor hd d.localActor_kernel ?_ hPV,
    e.noncyclic_derived_of_sylow_normal H Q hH.1.1.2 hWQ hQT hTQ q hq hkW he hQW⟩
  intro g v
  exact d.flag.normalizer_equivariant
    ⟨g.val,(sup_le d.chosen.normalizes d.flag.T_normalizes) g.property⟩ v
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
