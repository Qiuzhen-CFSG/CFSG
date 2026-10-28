module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Orbit
public import Theory.GroupTheory.Commutator.NormalClosureSupplement
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.SylowCentralizerComplement

/-!
# The component orbit of the original Sylow omega-center

Because T normalizes L and centralizes Z, the L-orbit of Z is also its
LT-orbit. Characteristic two and B.2.14 put this literal orbit inside T
and make it elementary abelian. The centralizing supplement T gives
[⟨Z^L⟩,LT] = [⟨Z^L⟩,L] = [Z,L]. Odd-index Sylow averaging gives
⟨Z^L⟩ = [Z,L] C_Z(L), without assuming a direct-sum decomposition.

These facts apply to the actual chosen component; Module/Source combines
them with left fixed-space vanishing and the original seed inclusion.
Source: Aschbacher--Smith, B.2.14 and 11.3.7, printed pp.78,773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original L-orbit of the Sylow omega-center. -/
def componentOmegaSpan (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  conjugateSpanBy (omegaCenter T) L

include D in
omit [Finite G] in
/-- The original LT normalizes the component orbit. -/
theorem componentOmegaSpan_normalized :
    L ⊔ (T : Subgroup G) ≤ normalizer (componentOmegaSpan T L : Set G) := by
  apply sup_le (le_normalizer_conjugateSpanBy _ _)
  exact normalizes_conjugateSpanBy _ _ _
    ((le_centralizer_iff.mp (omegaCenter_le_sylow_centralizer T)).trans
      (Subgroup.centralizer_le_normalizer _)) D.sylow_normalizes_component

include D in
omit [Finite G] in
/-- Adjoining the centralizing Sylow subgroup adds no orbit generators. -/
theorem componentOmegaSpan_eq_join :
    componentOmegaSpan T L = omegaClosure T (L ⊔ (T : Subgroup G)) := by
  rw [omegaClosure_eq_span]
  apply le_antisymm (conjugateSpanBy_mono le_rfl le_sup_left)
  exact conjugateSpanBy_le (le_conjugateSpanBy _ _) (componentOmegaSpan_normalized D)

include D S

private theorem join_characteristic :
    centralizer (pCore 2 ↥(L ⊔ (T : Subgroup G)) : Set ↥(L ⊔ (T : Subgroup G))) ≤
      pCore 2 ↥(L ⊔ (T : Subgroup G)) := by
  apply Chapter1.mem_He_iff.mp
  apply Chapter1.lemma_1_1_4_6 T (S.source.simpleQTKE.evenCharacteristic T)
  refine ⟨?_,fun t ht => (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right) ht⟩
  intro he
  exact D.ne_bot (bot_unique (D.le_core.trans he.le))

/-- B.2.14 applies in the literal subgroup LT. -/
theorem componentOmegaSpan_reduced :
    IsPReduced 2 ((componentOmegaSpan T L).subgroupOf (L ⊔ (T : Subgroup G))) := by
  let J := L ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hz : Stellmacher.omegaOneCenterAmbient (P : Subgroup J) =
      (omegaCenter T).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [← Stellmacher.omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective,
      Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right,
      map_subgroupOf_eq_of_le ((omegaCenter_le_sylow T).trans le_sup_right)]
    exact omegaCenterIn_eq_omegaOneAmbient _
  have hr := omegaCenter_normalClosure_reduced P (join_characteristic D S)
  rw [hz, normalClosure_subgroupOf_eq_conjugateSpanBy _ J
    ((omegaCenter_le_sylow T).trans le_sup_right)] at hr
  rw [componentOmegaSpan_eq_join D,omegaClosure_eq_span]
  exact hr

/-- The component orbit lies in the original Sylow subgroup. -/
theorem componentOmegaSpan_le_sylow : componentOmegaSpan T L ≤ (T : Subgroup G) := by
  have hr := map_mono (f := (L ⊔ (T : Subgroup G)).subtype)
    (componentOmegaSpan_reduced D S).le_pCore
  have hU : componentOmegaSpan T L ≤ L ⊔ (T : Subgroup G) :=
    conjugateSpanBy_le ((omegaCenter_le_sylow T).trans le_sup_right)
      (le_sup_left.trans (L ⊔ (T : Subgroup G)).le_normalizer)
  rw [map_subgroupOf_eq_of_le hU] at hr
  have hq := map_mono (f := (L ⊔ (T : Subgroup G)).subtype)
    (pCore_isPGroup.le_sylow_of_normal (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)))
  change (pCore 2 ↥(L ⊔ (T : Subgroup G))).map (L ⊔ (T : Subgroup G)).subtype ≤
    ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map (L ⊔ (T : Subgroup G)).subtype at hq
  rw [map_subgroupOf_eq_of_le le_sup_right] at hq
  exact hr.trans hq

/-- The component orbit is elementary abelian. -/
theorem componentOmegaSpan_elementary : IsElementaryAbelian 2 (componentOmegaSpan T L) := by
  let := (componentOmegaSpan_reduced D S).elementary
  have he := IsElementaryAbelian.map (p := 2)
    (A := (componentOmegaSpan T L).subgroupOf (L ⊔ (T : Subgroup G)))
    (L ⊔ (T : Subgroup G)).subtype
  rwa [map_subgroupOf_eq_of_le ((componentOmegaSpan_le_sylow D S).trans le_sup_right)] at he

/-- The centralizing Sylow supplement reduces all LT-commutators to [Z,L]. -/
theorem componentOmegaSpan_join_commutator :
    ⁅componentOmegaSpan T L,L ⊔ (T : Subgroup G)⁆ = ⁅omegaCenter T,L⁆ := by
  let J := L ⊔ (T : Subgroup G)
  let A := (omegaCenter T).subgroupOf J
  let K := L.subgroupOf J
  let P := (T : Subgroup G).subgroupOf J
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hgen : K ⊔ P = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hc : A ≤ centralizer (P : Set J) := by
    intro a ha p hp
    exact Subtype.ext (omegaCenter_le_sylow_centralizer T ha p hp)
  have hw : normalClosure (A : Set J) = (componentOmegaSpan T L).subgroupOf J := by
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy _ J
      ((omegaCenter_le_sylow T).trans le_sup_right),componentOmegaSpan_eq_join D,
      omegaClosure_eq_span]
  have hh := congrArg (map J.subtype)
    (normalClosure_commutator_eq_of_centralizing_supplement A K P hgen hc)
  rw [hw,map_commutator,map_commutator,
    map_subgroupOf_eq_of_le ((componentOmegaSpan_le_sylow D S).trans le_sup_right),
    ← MonoidHom.range_eq_map,range_subtype,
    map_subgroupOf_eq_of_le ((omegaCenter_le_sylow T).trans le_sup_right),
    map_subgroupOf_eq_of_le le_sup_left] at hh
  exact hh

/-- The original component moves its orbit by exactly [Z,L]. -/
theorem componentOmegaSpan_commutator :
    ⁅componentOmegaSpan T L,L⁆ = ⁅omegaCenter T,L⁆ := by
  apply le_antisymm
  · exact (commutator_mono le_rfl le_sup_left).trans
      (componentOmegaSpan_join_commutator D S).le
  · exact commutator_mono (le_conjugateSpanBy _ _) le_rfl

omit D S in
private theorem omega_le_moved_sup_fixed
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hUT : U ≤ (T : Subgroup G)) (hZU : omegaCenter T ≤ U)
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer (U : Set G)) :
    omegaCenter T ≤ ⁅U,L ⊔ (T : Subgroup G)⁆ ⊔
      (omegaCenter T ⊓ centralizer (L : Set G)) := by
  let J := L ⊔ (T : Subgroup G)
  let W := ⁅U,J⁆
  have hWU : W ≤ U := le_normalizer_iff_commutator_le_left.mp hn
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWU
  intro z hz
  obtain ⟨w,hw,hwC⟩ := fixed_coset_of_sylow J W
    (normalizer_commutator_ge_right U J)
    (fun w hw => elemPow_eq_one_of_isElementaryAbelian w hw)
    (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)) z
    (fun j hj => by
      change ⁅j,z⁆ ∈ ⁅U,J⁆
      rw [commutator_comm]
      exact commutator_mem_commutator hj (hZU hz))
    (fun t ht => omegaCenter_le_sylow_centralizer T hz t ht)
  have hwU : w*z ∈ U := U.mul_mem (hWU hw) (hZU hz)
  have hwZ : w*z ∈ omegaCenter T := by
    rw [omegaCenter, ← omegaCenterIn_eq_omegaOneAmbient (T : Subgroup G)]
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨hUT hwU,elemPow_eq_one_of_isElementaryAbelian _ hwU,
      fun t ht => hwC t ((show (T : Subgroup G) ≤ J from le_sup_right) ht)⟩
  have hm := (W ⊔ (omegaCenter T ⊓ centralizer (L : Set G))).mul_mem
    (mem_sup_left (W.inv_mem hw))
    (mem_sup_right ⟨hwZ,centralizer_le (show L ≤ J from le_sup_left) hwC⟩)
  simpa only [inv_mul_cancel_left] using hm

/-- Sylow averaging supplies the source product with the original central seed. -/
theorem componentOmegaSpan_splitting :
    componentOmegaSpan T L = ⁅componentOmegaSpan T L,L⁆ ⊔
      (omegaCenter T ⊓ centralizer (L : Set G)) := by
  let U := componentOmegaSpan T L
  let J := L ⊔ (T : Subgroup G)
  let W := ⁅U,J⁆
  let : IsElementaryAbelian 2 U := componentOmegaSpan_elementary D S
  have hWU : W ≤ U := le_normalizer_iff_commutator_le_left.mp
    (componentOmegaSpan_normalized D)
  have hW : W = ⁅U,L⁆ := (componentOmegaSpan_join_commutator D S).trans
    (componentOmegaSpan_commutator D S).symm
  have hZ := omega_le_moved_sup_fixed (T := T) (L := L) U (componentOmegaSpan_le_sylow D S)
    (le_conjugateSpanBy _ _) (componentOmegaSpan_normalized D)
  have hnW : L ≤ normalizer (W : Set G) :=
    le_sup_left.trans (normalizer_commutator_ge_right U J)
  have hnC : L ≤ normalizer (omegaCenter T ⊓ centralizer (L : Set G) : Set G) := by
    apply (le_centralizer_iff.mpr (show omegaCenter T ⊓ centralizer (L : Set G) ≤
      centralizer (L : Set G) from inf_le_right)).trans
    exact Subgroup.centralizer_le_normalizer _
  have he : U = W ⊔ (omegaCenter T ⊓ centralizer (L : Set G)) :=
    le_antisymm (conjugateSpanBy_le hZ
      ((le_inf hnW hnC).trans (normalizer_inf_normalizer_le_normalizer_sup W (omegaCenter T ⊓ centralizer (L : Set G)))))
      (sup_le hWU (inf_le_left.trans (le_conjugateSpanBy _ _)))
  exact he.trans (congrArg (fun Q : Subgroup G => Q ⊔
    (omegaCenter T ⊓ centralizer (L : Set G))) hW)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
