module
public import CFSG.Quasithin.Chapter5.A5Source.BaumannReduction
public import CFSG.Quasithin.Chapter5.A5Source.LocalAction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.ExternalCharacteristic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport

/-!
# The original alternating block forced by Baumann escape

Apply the actual C.1.24 characteristic pair to LT and its original Sylow.
An escaping full Baumann normalizer excludes both normal alternatives.
The resulting block is the original L, and its moved support is the chosen
V by the genuine Irr+ commutator-generation identity.
Source: Aschbacher--Smith 5.1.7(1), printed pp.633--634, using E.2.3(4).
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter5.A5Source
open Chapter13.Section05.A5Source ChapterB ChapterC
open ChapterC.RankOne ChapterC.RankOne.FiveBlockSource
open ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem alternating_block_of_baumann_escape
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) ∧ IsAlternatingBlock L 5 ∧
      (blockU L).map L.subtype = V ∧ L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let U := V.subgroupOf H
  let R := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let := d.reduced.normal
  let := d.reduced.elementary
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer d.normalizes_L)
  have hRmap : (R : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hfit : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
        (d.hypothesis.qtke.evenCharacteristic T) ⟨d.maximal_local.1.2.2,fun _ hx => (le_sup_right : (T : Subgroup G) ≤ H) hx⟩))
  have hprod : A ⊔ (R : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,hRmap,
      ←MonoidHom.range_eq_map,range_subtype]
  let e : A ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  let eL : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans d.quotient
  have hJ : ¬elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) :=
    fun hc => hout (baumann_normalizer_of_thompson_centralizes d hc)
  have hq := d.localActor_surjective_of_thompson_moves hJ
  let ρ := NormalElementaryQuotient.representation U d.localActor hq d.localActor_kernel
  let f := d.localModuleCoordinates
  have he : ∀ g v, f.symm (ρ g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (f.symm v) := local_full_equivariant d hq
  have hJmap : (elementaryAbelianMaxJ (R : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hRmap]
  have hJR : ¬elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (U : Set H) := by
    intro hc
    apply hJ
    rw [←hJmap]
    rintro x ⟨x,hx,rfl⟩ v hv
    exact congrArg H.subtype (hc hx ⟨v,(le_sup_right : (T : Subgroup G) ≤ H)
      (d.chosen.le_sylow hv)⟩ hv)
  have hTne : (T : Subgroup G) ≠ ⊥ :=
    fun hz => d.chosen.ne_bot (bot_unique (d.chosen.le_sylow.trans_eq hz))
  obtain ⟨D,hD⟩ := exists_baumann_universal_pair.{u,u} (T : Subgroup G) T.isPGroup' hTne
  have hno (C : Subgroup (baumann (T : Subgroup G))) (hc : C.Characteristic)
      (hne : C ≠ ⊥) : ¬H ≤ normalizer (C.map (baumann (T : Subgroup G)).subtype : Set G) := by
    intro hn
    exact hne (no_characteristic_baumann_of_escape d hout C hc
      (normal_subgroupOf_of_le_normalizer hn))
  have hBR : baumann (T : Subgroup G) ≤ (R : Subgroup H).map H.subtype := hRmap ▸ inf_le_left
  rcases external_normal_source_conclusion (T : Subgroup G) H R hBR hRmap.le hfit A
      d.hypothesis.local_component.1.1 hprod eL U d.localActor hq d.localActor_kernel
      d.localActor_component_image f.symm.toLinearMap f.symm.surjective he
      (fun v hv _ _ => by
        have hz : v = 0 := f.symm.injective (hv.trans (map_zero f.symm).symm)
        subst v
        exact map_zero _) hJR D hD with hfirst | hsecond | hb
  · exact (hno D.first D.first_characteristic D.first_ne_bot hfirst).elim
  · exact (hno D.second D.second_characteristic D.second_ne_bot hsecond).elim
  · obtain ⟨hb,ha,hm,hs,_⟩ := hb
    have hAN : A.map H.subtype = L := map_subgroupOf_eq_of_le le_sup_left
    have hVN : U.map H.subtype = V := map_subgroupOf_eq_of_le (d.chosen.le_sylow.trans le_sup_right)
    have hsame : (blockU A).map (H.subtype.comp A.subtype) = (blockU L).map L.subtype := by
      rw [←RankOne.Solvable.blockU_map_equiv e,map_map]
      rfl
    rw [hAN] at hm
    rw [hsame,hVN,hAN,←d.chosen.eq_commutator] at hs
    exact ⟨hb,RankOne.Solvable.isAlternatingBlock_of_equiv e ha,hs,hm⟩

end CFSG.Quasithin.Chapter5.A5Source
