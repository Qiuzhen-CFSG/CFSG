module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableCores
public import Theory.GroupAction.TransitiveCentralQuotientInvolutions

/-!
# The original core cannot have a transitive central quotient

The opposite elementary sixteen supplies an involution outside the chosen
central sixteen. Transitivity on the nonidentity central cosets would then
make the entire core elementary. That core would centralize the opposite
module and lie in the opposite core, contradicting the proved original
incomparability. No module classification or residual lift is assumed.

Source application: Aschbacher--Smith 13.2.8(1), printed p.880.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ W : Subgroup G}

/-- The actual component action transports an opposite elementary lift. -/
theorem core_elementary_of_transitive_cosets
    (d : Context T L V V₁ V₂ V₃)
    (htrans : ∀ x ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2, x ∉ V →
      ∀ y ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2, y ∉ V →
        ∃ l : L, (l.val * x * l.val⁻¹) / y ∈ V)
    (hWQ : W ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hWV : ¬ W ≤ V) (hW : IsElementaryAbelian 2 W) :
    IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let H := L ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let U := V.subgroupOf Q
  have hLQ : L ≤ normalizer (Q : Set G) :=
    (show L ≤ H from le_sup_left).trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  let : Normalizes L Q := ⟨hLQ⟩
  have hcentral : U ≤ center Q := by
    intro v hv
    rw [mem_center_iff]
    intro q
    exact Subtype.ext ((d.chosen.core_centralizes q.property) v hv).symm
  have hexp (v : Q) (hv : v ∈ U) : v ^ 2 = 1 := by
    let := d.elementary
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v.val hv)
  have ht (x : Q) (hx : x ∉ U) (y : Q) (hy : y ∉ U) :
      ∃ l : L, (l • x) / y ∈ U := by
    obtain ⟨l,hl⟩ := htrans x x.property hx y y.property hy
    exact ⟨l,hl⟩
  obtain ⟨w,hw,hwV⟩ := SetLike.not_le_iff_exists.mp hWV
  let := hW
  exact IsElementaryAbelian.of_transitive_central_quotient_involution U hcentral hexp ht
    ⟨⟨w,hWQ hw⟩,hwV,Subtype.ext (elemPow_eq_one_of_isElementaryAbelian w hw)⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- The commuting original pair rules out transitivity on the central
quotient of the first core, with its actual component action. -/
theorem original_commuting_pair_core_cosets_not_transitive
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hd : Function.Surjective d.localActor)
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 H) (hVW : V ≤ centralizer (W : Set G)) :
    ¬ (∀ x ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2, x ∉ V →
      ∀ y ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2, y ∉ V →
        ∃ l : L, (l.val * x * l.val⁻¹) / y ∈ V) := by
  intro ht
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) :=
    (d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left
  have hWQ : W ≤ Q := by
    rw [show Q = (T : Subgroup G) ⊓ centralizer (V : Set G) from
      (d.sylow_centralizer d.normalizes_L).symm]
    exact le_inf e.chosen.le_sylow (le_centralizer_iff.mp hVW)
  have hinc := (original_pair_cores_incomparable d hH hd q hq hk).2
  have hWV : ¬ W ≤ V := by
    intro hw
    have heq : W = V := eq_of_le_of_card_ge hw (by rw [e.module_card,d.module_card])
    apply hinc
    rw [←hjoin,←e.sylow_centralizer e.normalizes_L,heq]
    exact (d.sylow_centralizer d.normalizes_L).ge
  let := d.core_elementary_of_transitive_cosets ht hWQ hWV e.elementary
  have hQW : Q ≤ centralizer (W : Set G) :=
    (le_centralizer Q).trans (centralizer_le hWQ)
  apply hinc
  rw [←hjoin,←e.sylow_centralizer e.normalizes_L]
  exact le_inf hQT hQW

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
