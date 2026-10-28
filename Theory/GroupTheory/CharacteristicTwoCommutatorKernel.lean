module
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupTheory.CComponent.QuotientLifting
/-!
# The component kernel of a reduced internal module

In a finite group of characteristic two, suppose V is reduced and
[O₂(G),L]≤V. An element of L centralizing V fixes both layers of O₂(G),
so the two-layer lemma puts it in O₂(G). For normal L, the action kernel
is precisely O₂(L). Consequently the canonical map G/O₂(G)→G/C_G(V)
is injective on the actual image of L, while the ambient quotients need
not be isomorphic.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem centralizer_intersection_le_twoCore_of_core_commutator
    (V L : Subgroup G) [V.Normal] (hV : IsPGroup 2 V)
    (hG : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hc : ⁅pCore 2 G,L⁆ ≤ V) : L ⊓ centralizer (V : Set G) ≤ pCore 2 G := by
  have ht := two_layer_le_radical (pCore 2 G) V (pCore 2 G) hV
    (pCore_quotient_pCore_eq_bot 2) (inf_le_right.trans hG)
  apply (le_inf inf_le_right ?_).trans ht
  apply le_commutatorPreimage le_top
  rw [commutator_comm]
  exact (commutator_mono le_rfl inf_le_left).trans hc

theorem reduced_component_action_kernel (V L : Subgroup G)
    [V.Normal] [L.Normal] (hV : Theory.GroupTheory.IsPReduced 2 V)
    (hG : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hc : ⁅pCore 2 G,L⁆ ≤ V) :
    ((QuotientGroup.mk' (centralizer (V : Set G))).subgroupMap L).ker = pCore 2 L := by
  have hh := centralizer_intersection_le_twoCore_of_core_commutator V L
    hV.elementary.isPGroup hG hc
  have hcomap : (pCore 2 G).comap L.subtype ≤ pCore 2 L :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective L.subtype L.subtype_injective⟩
  have hmap : (pCore 2 L).map L.subtype ≤ pCore 2 G :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map L.subtype⟩
  rw [ker_subgroupMap,QuotientGroup.ker_mk']
  apply le_antisymm
  · intro l hl
    exact hcomap (hh ⟨l.property,hl⟩)
  · intro l hl
    exact le_centralizer_iff.mp hV.le_centralizer_pCore (hmap (mem_map_of_mem L.subtype hl))

theorem reduced_component_action_equiv (V L : Subgroup G)
    [V.Normal] [L.Normal] (hV : Theory.GroupTheory.IsPReduced 2 V)
    (hG : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hc : ⁅pCore 2 G,L⁆ ≤ V) :
    Nonempty ((L ⧸ pCore 2 L) ≃* L.map (QuotientGroup.mk' (centralizer (V : Set G)))) := by
  let f := (QuotientGroup.mk' (centralizer (V : Set G))).subgroupMap L
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (reduced_component_action_kernel V L hV hG hc).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' (centralizer (V : Set G))).subgroupMap_surjective L))⟩
@[expose] noncomputable def twoCoreToCentralizer (V : Subgroup G)
    [V.Normal] (hV : Theory.GroupTheory.IsPReduced 2 V) :
    (G ⧸ pCore 2 G) →* (G ⧸ centralizer (V : Set G)) :=
  QuotientGroup.lift (pCore 2 G) (QuotientGroup.mk' (centralizer (V : Set G))) (by
    rw [QuotientGroup.ker_mk']
    exact le_centralizer_iff.mp hV.le_centralizer_pCore)
omit [Finite G] in
@[simp] theorem twoCoreToCentralizer_mk (V : Subgroup G)
    [V.Normal] (hV : Theory.GroupTheory.IsPReduced 2 V) (g : G) :
    twoCoreToCentralizer V hV (QuotientGroup.mk' (pCore 2 G) g) =
      QuotientGroup.mk' (centralizer (V : Set G)) g := rfl

theorem twoCoreToCentralizer_component_injective (V L : Subgroup G)
    [V.Normal] (hV : Theory.GroupTheory.IsPReduced 2 V)
    (hG : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hc : ⁅pCore 2 G,L⁆ ≤ V) :
    Function.Injective ((twoCoreToCentralizer V hV).subgroupMap
      (L.map (QuotientGroup.mk' (pCore 2 G)))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro a ha
  obtain ⟨l,hl,hlq⟩ := a.property
  have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
  change twoCoreToCentralizer V hV a.val = 1 at hh
  rw [← hlq,twoCoreToCentralizer_mk] at hh
  have hp := centralizer_intersection_le_twoCore_of_core_commutator V L
    hV.elementary.isPGroup hG hc ⟨hl,(QuotientGroup.eq_one_iff _).mp hh⟩
  apply Subtype.ext
  change a.val = 1
  rw [← hlq]
  exact (QuotientGroup.eq_one_iff _).mpr hp

omit [Finite G] in
theorem twoCoreToCentralizer_image (V L : Subgroup G)
    [V.Normal] (hV : Theory.GroupTheory.IsPReduced 2 V) :
    (L.map (QuotientGroup.mk' (pCore 2 G))).map (twoCoreToCentralizer V hV) =
      L.map (QuotientGroup.mk' (centralizer (V : Set G))) := by
  rw [map_map]
  rfl
end Subgroup
