module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.CrossModule
public import Theory.Representation.BinaryPermutation.FiveEvenDisplacement

/-!
# The centralizer intersection of two noncommuting original A₅ modules

The cross-action has order four, hence its kernel in the original natural
sixteen has order four. A nontrivial even image moves a four-group in the
other natural module. Mutual Sylow normalization puts that commutator in
both modules. Comparing orders identifies the entire cross-centralizer
with this intersection, so it lies in the other natural module.

The original marked action is retained. Source application:
Aschbacher--Smith 13.2.8(1), p.880, using 13.2.3(1), pp.878--879.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ K W W₁ W₂ W₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
include d e

theorem cross_centralizer_le_module
    {J : Subgroup G} (hVJ : V≤J) (hWJ : W≤J)
    (q : J →* Equiv.Perm (Fin 5))
    (hk : q.ker=centralizer (W.subgroupOf J : Set J))
    (he : ∀ j : J, ∀ w : BinaryPermutation.core (Fin 5),
      j.val * e.flag.module.map (Multiplicative.ofAdd w) * j.val⁻¹ =
        e.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q j) w)))
    (hm : ¬ V≤centralizer (W:Set G)) :
    V⊓centralizer (W:Set G) ≤ W := by
  let A := V.subgroupOf J
  let B := A.map q
  let := d.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hVJ
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map q
  have hc : Nat.card B=4 := d.cross_action_card hVJ hWJ e.chosen.le_sylow e.flag.T_normalizes q hk hm
  have hmeet : B⊓alternatingGroup (Fin 5)≠⊥ := by
    intro hz
    have hi := (alternatingGroup (Fin 5)).relIndex_dvd_index_of_normal B
    rw [alternatingGroup.index_eq_two] at hi
    have he : (alternatingGroup (Fin 5)).relIndex B=4 := by
      rw [←inf_relIndex_left B (alternatingGroup (Fin 5)),hz,relIndex_bot_left,hc]
    rw [he] at hi
    norm_num at hi
  obtain ⟨g,hgne⟩ := ne_bot_iff_exists_ne_one.mp hmeet
  obtain ⟨v,hv,hvg⟩ := g.property.1
  have hge : q v∈alternatingGroup (Fin 5) := hvg.symm ▸ g.property.2
  have hgn : q v≠1 := fun h => hgne (Subtype.ext (hvg.symm.trans h))
  have hgp : (q v)^2=1 := elemPow_eq_one_of_isElementaryAbelian (q v) (mem_map_of_mem q hv)
  have hmoved := BinaryPermutation.FiveEvenDisplacement.four_le_card_commutator
    e.flag.module.map e.flag.module.injective v.val (q v) hgn hgp hge
    (fun w => (he v w.toAdd).symm)
  rw [e.flag.module.range_eq] at hmoved
  have hcommW : ⁅V,W⁆≤W := le_normalizer_iff_commutator_le_right.mp
    (d.chosen.le_sylow.trans e.flag.T_normalizes)
  have hcommV : ⁅V,W⁆≤V := le_normalizer_iff_commutator_le_left.mp
    (e.chosen.le_sylow.trans d.flag.T_normalizes)
  have hfour : 4≤Nat.card (⁅V,W⁆ : Subgroup G) := hmoved.trans
    (card_le_of_le (commutator_mono (zpowers_le.mpr hv) le_rfl))
  have hle : ⁅V,W⁆≤V⊓centralizer (W:Set G) :=
    le_inf hcommV (hcommW.trans (by let := e.elementary;exact le_centralizer W))
  have hcard : Nat.card (V⊓centralizer (W:Set G) : Subgroup G)=4 := by
    have hprod := IsElementaryAbelian.card_inf_ker_mul_card_map A q
    have hmap : (A⊓q.ker).map J.subtype=V⊓centralizer (W:Set G) := by
      rw [hk,←map_inf_centralizer_of_injective J.subtype J.subtype_injective,
        map_subgroupOf_eq_of_le hWJ,map_subgroupOf_eq_of_le hVJ]
    have hc' : Nat.card (A⊓q.ker : Subgroup J)=Nat.card (V⊓centralizer (W:Set G) : Subgroup G) :=
      (card_map_of_injective J.subtype_injective).symm.trans (congrArg (fun X:Subgroup G=>Nat.card X) hmap)
    rw [hc',hc,Nat.card_congr (subgroupOfEquivOfLe hVJ).toEquiv,d.module_card] at hprod
    omega
  have heq : ⁅V,W⁆=V⊓centralizer (W:Set G) := eq_of_le_of_card_ge hle (by rwa [hcard])
  exact heq.ge.trans hcommW
end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
