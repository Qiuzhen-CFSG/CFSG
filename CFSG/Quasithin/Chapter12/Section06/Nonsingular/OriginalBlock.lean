module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalThreeBlock
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.ShortSeedPropagation

/-!
# Propagating the original cubic block to L

The literal O^2(X) lies in L because LT/L is a two-group. Its cubic quotient
prevents its image in the actual centerless L/O2(L) from being central, so it
normally generates L. The original Q normalizes this seed. Characteristic
two and the checked short-seed propagation theorem reconstruct every short
clause of L, including the central elementary layer and irreducibility.

The consumer constructs the cubic seed from normalizer escape; it does not
assume any block conclusion. The next module identifies its layer with the
original V and its module with the marked natural A8 module. Source:
Aschbacher--Smith C.1.21 and 12.6.18(1), printed pp.128 and 827, combined
manuscript of 1 March 2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- A short cubic residual in the original three-letter overgroup propagates
to the original L, using its actual simple two-core quotient. -/
theorem SourceHypothesis.nonsingular_short_of_three_block
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (X : Subgroup G) (hX : X ≤ LT T L) (hQ : Q T L ≤ X)
    (hs : ChapterC.IsShort (pResidual 2 X))
    (hthree : Nat.card (pResidual 2 X ⧸ pCore 2 (pResidual 2 X)) = 3) :
    ChapterC.IsShort L := by
  let J := LT T L
  let C := L.subgroupOf J
  let Y := (pResidual 2 X).map X.subtype
  have hLJ : L ≤ J := le_sup_left
  have hJM : J ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer H.chosen.sylow_normalizes_component
  let : C.Normal := normal_subgroupOf_of_le_normalizer hJM
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect H.source.maximal_faithful.1.1
  have hp : IsPPerfect 2 L := by
    intro N hN hq
    let := hN
    by_contra hne
    let : Nontrivial (L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (L ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (L ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (L ⧸ N) inferInstance
  have hCL : C ≃* L := subgroupOfEquivOfLe hLJ
  have hpC : IsPPerfect 2 C := hp.of_surjective hCL.symm.toMonoidHom hCL.symm.surjective
  have hCP : C ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup hLJ (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hres : pResidual 2 J = C := pResidual_eq_of_isPPerfect_sup C _ hpC
    T.isPGroup'.comap_subtype hCP
  have hYL : Y ≤ L := by
    rintro y ⟨x,hx,rfl⟩
    have hm := map_pResidual_le 2 (inclusion hX)
    rw [hres] at hm
    exact hm (mem_map_of_mem (inclusion hX) hx)
  let a : pResidual 2 X ≃* Y := equivMapOfInjective _ X.subtype X.subtype_injective
  let A := Y.subgroupOf L
  let b : A ≃* Y := subgroupOfEquivOfLe hYL
  have hA : ChapterC.IsShort A := hs.of_mulEquiv (a.trans b.symm)
  have hcJ := H.original_core_overgroup_characteristic_two J le_rfl (pCoreIn_le 2 J)
  have hcL : centralizer (pCore 2 L : Set L) ≤ pCore 2 L :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 hCL).mp (normal_core_selfCentralizing hcJ C)
  have hfL := generalizedFitting_eq_pCore_of_selfCentralizing 2 hcL
  have hQY : Q T L ≤ normalizer (Y : Set G) := hQ.trans
    (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pResidual 2 X)))
  have hQL : L.pCoreIn 2 ≤ Q T L := pCoreIn_mono_of_normalizes hLJ hJM
  have hQA : pCore 2 L ≤ normalizer (A : Set L) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    exact le_normalizer_iff.mp hQY x (hQL (mem_map_of_mem L.subtype hx)) y hy
  have hcenter := D.coreQuotient_center_eq_bot H.chosen H.source.quasisimple
  have hnoncentral : ¬ A.map (QuotientGroup.mk' (pCore 2 L)) ≤ center (Star L) := by
    intro hcent
    have hAp : A ≤ pCore 2 L := by
      simpa only [hcenter,le_bot_iff,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] using hcent
    have hpp : IsPGroup 2 (pResidual 2 X) :=
      (pCore_isPGroup.to_le hAp).of_equiv (a.trans b.symm).symm
    obtain ⟨n,hn⟩ := hpp.exists_card_eq
    have hd : 3 ∣ 2 ^ n := by
      rw [←hn,←hthree]
      exact card_quotient_dvd_card _
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  let := H.source.quasisimple
  exact ChapterC.RankOne.GlaubermanArgument.isShort_of_normal_generation A hA hp hfL
    (Or.inl H.source.quasisimple) hQA
    (ChapterC.RankOne.GlaubermanArgument.normal_generation_of_noncentral_core_image A hp hnoncentral)

/-- Normalizer escape now constructs the short structure of the original L;
no block or core-module equality is supplied as an input. -/
theorem SourceHypothesis.nonsingular_original_short
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (v : V) (hv : D.Nonsingular v)
    (hn : ¬ normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    ChapterC.IsShort L := by
  obtain ⟨X,hX,hRX,_,_,_,_,_,_,hthree,hb,_⟩ := H.nonsingular_original_three_block D hTV v hv hn
  exact H.nonsingular_short_of_three_block D X hX ((Q_le_Rv H.chosen v).trans hRX) hb.short hthree

end CFSG.Quasithin.Chapter12.Section06
