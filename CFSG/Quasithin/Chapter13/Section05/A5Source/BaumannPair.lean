module
public import CFSG.Quasithin.Chapter5.A5Source.LocalAction
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.ExternalCharacteristic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport

/-!
# One prescribed Baumann pair in the original A₅ context

Apply C.1.24 to the original LT, its Sylow subgroup and the actual natural
module map. The characteristic pair is supplied before this application,
so another original local group can use exactly the same pair. The two
normalizer alternatives retain its full members. The block alternative
retains the original L, its subnormal placement, the equality U(L)=V and
the literal Thompson commutator.

OriginalCentralization/BaumannPair compares the two applications using
local uniqueness. No escape of the Baumann normalizer is assumed here.
Source: Aschbacher--Smith C.1.18 and C.1.24(a), pp.126,130--131, applied to
the original pair in 13.2.8(1), p.880.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open ChapterB ChapterC Chapter5.A5Source
open ChapterC.RankOne ChapterC.RankOne.FiveBlockSource
open ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- C.1.24 with a prescribed pair and the original module support. -/
theorem original_baumann_pair_alternatives
    (hJ : ¬elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u}) :
    (L ⊔ (T : Subgroup G) ≤ normalizer
      (D.first.map (baumann (T : Subgroup G)).subtype : Set G)) ∨
    (L ⊔ (T : Subgroup G) ≤ normalizer
      (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) ∨
    (IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) ∧ IsAlternatingBlock L 5 ∧
      (blockU L).map L.subtype = V ∧ L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆) := by
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
  have hBR : baumann (T : Subgroup G) ≤ (R : Subgroup H).map H.subtype := hRmap ▸ inf_le_left
  rcases external_normal_source_conclusion (T : Subgroup G) H R hBR hRmap.le hfit A
      d.hypothesis.local_component.1.1 hprod eL U d.localActor hq d.localActor_kernel
      d.localActor_component_image f.symm.toLinearMap f.symm.surjective he
      (fun v hv _ _ => by
        have hz : v = 0 := f.symm.injective (hv.trans (map_zero f.symm).symm)
        subst v
        exact map_zero _) hJR D hD with hfirst | hsecond | hb
  · exact Or.inl hfirst
  · exact Or.inr (Or.inl hsecond)
  · obtain ⟨hb,ha,hm,hs,_⟩ := hb
    have hAN : A.map H.subtype = L := map_subgroupOf_eq_of_le le_sup_left
    have hVN : U.map H.subtype = V := map_subgroupOf_eq_of_le (d.chosen.le_sylow.trans le_sup_right)
    have hsame : (blockU A).map (H.subtype.comp A.subtype) = (blockU L).map L.subtype := by
      rw [←RankOne.Solvable.blockU_map_equiv e,map_map]
      rfl
    rw [hAN] at hm
    rw [hsame,hVN,hAN,←d.chosen.eq_commutator] at hs
    exact Or.inr (Or.inr ⟨hb,RankOne.Solvable.isAlternatingBlock_of_equiv e ha,hs,hm⟩)

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
