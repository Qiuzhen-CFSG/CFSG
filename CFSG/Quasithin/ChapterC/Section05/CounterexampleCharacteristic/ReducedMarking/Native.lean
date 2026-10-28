module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.Thompson
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Stellmacher.BaumannMap

/-!
# The literal reduced module inside KT

The short block's ambient module is normal in KT. Its intrinsic centralizer
is O₂(KT), so the published reducedness condition follows from the trivial
core of the core quotient. Injective transport also turns the established
ambient Thompson movement into the exact intrinsic Sylow hypothesis.

Source: Aschbacher–Smith C.5.3–4 and C.5.9, printed pp.154–155 and161.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem native_centralizer (A V : Subgroup G) (hVA : V ≤ A) :
    centralizer (V.subgroupOf A : Set A) = (centralizer (V : Set G)).subgroupOf A := by
  ext a
  constructor
  · intro h v hv
    exact congrArg Subtype.val (h ⟨v,hVA hv⟩ hv)
  · intro h v hv
    exact Subtype.ext (h v hv)

omit [Finite G] in
theorem reduced_module_normal (K T : Subgroup G)
    (hn : T ≤ normalizer (K : Set G)) : ((U K).subgroupOf (K ⊔ T)).Normal :=
  (normal_subgroupOf_iff_le_normalizer ((map_subtype_le _).trans le_sup_left)).mpr
    ((sup_le K.le_normalizer hn).trans
      (normalizer_le_normalizer_characteristic_image K (blockU K)))

omit [Finite G] in
theorem reduced_module_elementary (K T : Subgroup G) (hK : IsShort K) :
    IsElementaryAbelian 2 ((U K).subgroupOf (K ⊔ T)) := by
  let : IsElementaryAbelian 2 (U K) := hK.elementary.map K.subtype
  exact IsElementaryAbelian.subgroupOf (show U K ≤ K ⊔ T from
    (map_subtype_le _).trans le_sup_left)

theorem reduced_module_core (K T : Subgroup G) (hK : IsShort K)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G)) :
    centralizer ((U K).subgroupOf (K ⊔ T) : Set (K ⊔ T : Subgroup G)) =
      pCore 2 (K ⊔ T : Subgroup G) := by
  rw [native_centralizer (K ⊔ T) (U K) ((map_subtype_le (blockU K)).trans le_sup_left)]
  apply map_injective (K ⊔ T).subtype_injective
  rw [subgroupOf_map_subtype,inf_comm]
  exact normal_short_extension_centralizer K T hK hT hn

theorem reduced_module_reduced (K T : Subgroup G) (hK : IsShort K)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G)) :
    IsPReduced 2 ((U K).subgroupOf (K ⊔ T)) := by
  let := reduced_module_normal K T hn
  let : IsElementaryAbelian 2 (U K) := hK.elementary.map K.subtype
  refine ⟨inferInstance,IsElementaryAbelian.subgroupOf (show U K ≤ K ⊔ T from (map_subtype_le _).trans le_sup_left),?_⟩
  let e := QuotientGroup.quotientMulEquivOfEq (reduced_module_core K T hK hT hn)
  apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  rw [pCore_map_iso, pCore_quotient_pCore_eq_bot]

theorem native_thompson_moves (K T : Subgroup G) (hK : IsShort K)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hno : ∀ N : Subgroup G, N ≤ T → normalizer (T : Set G) ≤ normalizer (N : Set G) →
      K ⊔ T ≤ normalizer (N : Set G) → N = ⊥) :
    ¬ elementaryAbelianMaxJ (P : Subgroup (K ⊔ T : Subgroup G)) ≤
      centralizer ((U K).subgroupOf (K ⊔ T) : Set (K ⊔ T : Subgroup G)) := by
  intro hh
  rw [native_centralizer (K ⊔ T) (U K) ((map_subtype_le (blockU K)).trans le_sup_left)] at hh
  have hm := map_mono (f := (K ⊔ T).subtype) hh
  rw [← elementaryAbelianMaxJ_map_injective (K ⊔ T).subtype (K ⊔ T).subtype_injective, hP,subgroupOf_map_subtype] at hm
  exact thompson_moves_block K T hK hT hn ⟨P,hP⟩ hno (hm.trans inf_le_left)
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
