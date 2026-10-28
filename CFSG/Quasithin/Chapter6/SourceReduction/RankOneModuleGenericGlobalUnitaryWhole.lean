module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySplit
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import FeitThompson.FinalTheorem
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# The whole core in the proper unitary overcomponent

Write K = O²(H), Q = O₂(K), and R = O₂(J). The natural or dual
moved module [R,J] = K ∩ R has a fixed complement. The original enlarged
right parabolic has characteristic two and two-core Q, including the
degree-two extension. Since R lies in the source overlap, every element
of C_R(J) therefore lies in Q and hence in K ∩ R. Disjointness of the
moved and fixed spaces kills the complement. Thus R = K ∩ R has order
q³ and the entire original core action is natural or dual.

This removes the extra fixed binary dimension without identifying the
extended overlap core with Q. Comparing actual group orders then gives
|J:K| = q³-1 and T ∩ J = T ∩ L. Original uniqueness places the whole
normalizer of O₂(L) in N_G(L). Its normalizer inside J has odd quotient
modulo its intersection with L, so its terminal derived subgroup lies in L.
The rank-one Borel bound makes that normalizer solvable. The nonnormal
overcomponent still requires the intrinsic second-parabolic calculation
contradicting this solvability.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitarySplit

/-- A split natural core has no fixed complement if all fixed core elements
already lie in its commutator subgroup. -/
theorem SplitCoreAction.core_eq_moved_of_fixed_le
    {G : Type*} [Group G] [Finite G]
    {h : HasCharacteristicTwo G} {m : ℕ} (d : SplitCoreAction h m)
    (hphi : frattini (pCore 2 G) = ⊥)
    (hfixed : pCore 2 G ⊓ center G ≤ ⁅pCore 2 G,(⊤ : Subgroup G)⁆) :
    pCore 2 G = ⁅pCore 2 G,(⊤ : Subgroup G)⁆ := by
  let R := pCore 2 G
  let E := R ⧸ frattini R
  let q := QuotientGroup.mk' (frattini R)
  let a := QuotientGroup.mk' R
  let β := (quotientAut (frattini R)).comp (MulAut.conjNormal : G →* MulAut R)
  let α := QuotientGroup.lift R β (pCore_frattini_action_kernel 2 h).ge
  have hα (g : G) (r : R) : α (a g) (q r) = q (MulAut.conjNormal g r) :=
    quotientAut_apply_mk (frattini R) (MulAut.conjNormal g) r
  have hρ : ProjectiveRadicalSplitting.linearAction α = UnitaryCover.frattiniAction h := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective R g
    rw [ProjectiveRadicalSplitting.linearAction_apply]
    exact (UnitaryCover.frattiniAction_apply h g v.toMul).symm
  have he := ProjectiveRadicalSplitting.commutatorImage_eq_coinvariants R a
    (QuotientGroup.mk'_surjective R) q (QuotientGroup.mk'_surjective _) α hα
  rw [hρ] at he
  have hqi : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    rw [QuotientGroup.ker_mk',hphi]
  obtain ⟨F,_,_,_,hF,e,C,hC,hcompl,hdegree,hfd,hmodel⟩ := d
  have hIC : (UnitaryCover.frattiniAction h).invariants ≤ C.toSubmodule := by
    intro v hv
    obtain ⟨r,hr⟩ := QuotientGroup.mk'_surjective (frattini R) v.toMul
    have hvr : v = Additive.ofMul (q r) := congrArg Additive.ofMul hr.symm
    have hcent : (r : G) ∈ center G := by
      apply mem_center_iff.mpr
      intro g
      have hh := hv (a g)
      rw [hvr,←hρ,ProjectiveRadicalSplitting.linearAction_apply] at hh
      have hh' : α (a g) (q r) = q r := congrArg Additive.toMul hh
      rw [hα] at hh'
      have hg := congrArg Subtype.val (hqi hh')
      change g * (r : G) * g⁻¹ = (r : G) at hg
      exact mul_inv_eq_iff_eq_mul.mp hg
    have hrm := hfixed ⟨r.property,hcent⟩
    rw [hC,←he]
    change v.toMul ∈ (⁅R,(⊤ : Subgroup G)⁆.subgroupOf R).map q
    exact ⟨r,hrm,hr⟩
  have hIt : (UnitaryCover.frattiniAction h).invariants = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    exact hcompl.disjoint.le_bot ⟨hIC hv,hv⟩
  have hCt : C.toSubmodule = ⊤ := by
    have hh := hcompl.sup_eq_top
    rwa [hIt,sup_bot_eq] at hh
  apply le_antisymm _ (commutator_le_left R ⊤)
  intro r hr
  have hm : Additive.ofMul (q ⟨r,hr⟩) ∈ Coinvariants.ker (UnitaryCover.frattiniAction h) := by
    rw [←hC,hCt]
    exact Submodule.mem_top
  rw [←he] at hm
  obtain ⟨s,hs,hse⟩ := (show q ⟨r,hr⟩ ∈ (⁅R,(⊤ : Subgroup G)⁆.subgroupOf R).map q from hm)
  have hs' : s = ⟨r,hr⟩ := hqi hse
  rw [hs'] at hs
  exact hs

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitarySplit

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- Characteristic two in the original enlarged right parabolic places the
fixed core inside the original intersection, also in the degree-two extension. -/
theorem Preparation.unitary_overcomponent_fixed_core_le
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H ≤ J) :
    J.pCoreIn 2 ⊓ centralizer (J : Set G) ≤ residual H ⊓ J.pCoreIn 2 := by
  let K := residual H
  let Q := K.pCoreIn 2
  let P := ChapterF.Source.parabolic ![L,K] (sourceS L H) 1
  let Y := P ⊔ (T : Subgroup G)
  have hKP : K ≤ P := le_sup_left.trans le_sup_left
  have hYK : Y ≤ normalizer (K : Set G) := sup_le
    ((normal_subgroupOf_iff_le_normalizer hKP).mp
      ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1))
    (hH.1.1.2.trans (le_normalizer_residual H))
  have hSY : sourceS L H ≤ Y := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hchar := Chapter1.mem_He_iff.mpr
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp
      (characteristic_two_of_sourceS_right h hH hYK hSY))
  change Y ⊓ centralizer (Y.pCoreIn 2 : Set G) ≤ Y.pCoreIn 2 at hchar
  have hcore : Y.pCoreIn 2 = Q := d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp
    (he.elim (.unitary m hm) (.unitaryExtension m hm)) 1
  rw [hcore] at hchar
  have hRS := (d.unitary_overcomponent_core_intersection h hH hp m hm he hJ hKJ).1
  intro x hx
  have hxQ := hchar ⟨hSY (hRS hx.1),centralizer_le ((pCoreIn_le 2 K).trans hKJ) hx.2⟩
  exact ⟨pCoreIn_le 2 K hxQ,hx.1⟩

/-- The fixed complement vanishes: the whole overcomponent core is the
original intersection in both ordinary and extended unitary rows. -/
theorem Preparation.unitary_overcomponent_core_eq_intersection
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    J.pCoreIn 2 = residual H ⊓ J.pCoreIn 2 := by
  obtain ⟨_,hphi,_,hc,hsplit⟩ := d.unitary_overcomponent_split_core h hH hp m hm he hJ hKJ hQR
  have hmove := (d.unitary_overcomponent_moved_eq_intersection h hH hp m hm he hJ hKJ hQR).1
  have hmap : (⁅pCore 2 J,(⊤ : Subgroup J)⁆).map J.subtype = ⁅J.pCoreIn 2,J⁆ := by
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype]
    rfl
  have hfixed : pCore 2 J ⊓ center J ≤ ⁅pCore 2 J,(⊤ : Subgroup J)⁆ := by
    intro x hx
    have hxR : (x : G) ∈ J.pCoreIn 2 := mem_map_of_mem J.subtype hx.1
    have hxC : (x : G) ∈ centralizer (J : Set G) := by
      intro j hj
      exact congrArg Subtype.val (mem_center_iff.mp hx.2 ⟨j,hj⟩)
    have hh := d.unitary_overcomponent_fixed_core_le h hH hp m hm he hJ hKJ.le ⟨hxR,hxC⟩
    rw [←hmove,←hmap] at hh
    exact (mem_map_iff_mem J.subtype_injective).mp hh
  have heq := hsplit.core_eq_moved_of_fixed_le hphi hfixed
  have hh := congrArg (Subgroup.map J.subtype) heq
  exact hh.trans (hmap.trans hmove)

/-- The entire original core lies in Q, has order q³, and carries the
natural or dual action of the actual quotient J/O₂(J) ≃ SL₃(q). -/
theorem Preparation.unitary_overcomponent_whole_natural_core
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    J.pCoreIn 2 ≤ (residual H).pCoreIn 2 ∧
      Nat.card (J.pCoreIn 2) = (2^m)^3 ∧
      ∃ hc : HasCharacteristicTwo J, UnitaryCover.NaturalCoreAction hc m := by
  have heq := d.unitary_overcomponent_core_eq_intersection h hH hp m hm he hJ hKJ hQR
  have hle := (d.unitary_overcomponent_core_intersection h hH hp m hm he hJ hKJ.le).2.1
  have hcard := (d.unitary_overcomponent_proper_intersection h hH hp m hm he hJ hKJ.le hQR).2
  rw [←heq] at hle hcard
  obtain ⟨_,_,hc,hsection⟩ := d.unitary_overcomponent_full_linear_action h hH hp m hm he hJ hKJ hQR
  refine ⟨hle,hcard,hc,hsection.whole_of_card_le ?_⟩
  change Nat.card ((pCore 2 J) ⧸ frattini (pCore 2 J)) ≤ _
  calc
    _ ≤ Nat.card (pCore 2 J) := Nat.card_le_card_of_surjective
      (QuotientGroup.mk' (frattini (pCore 2 J))) (QuotientGroup.mk'_surjective _)
    _ = Nat.card (J.pCoreIn 2) := Nat.card_congr
      ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).toEquiv
    _ = (2^m)^3 := hcard

/-- The literal inclusion K ≤ J has odd index q³-1, after the fixed
complement is removed. No quotient-image index is substituted for it. -/
theorem Preparation.unitary_overcomponent_index
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    (residual H).relIndex J = (2^m)^3-1 := by
  let K := residual H
  have hRc := (d.unitary_overcomponent_whole_natural_core h hH hp m hm he hJ hKJ hQR).2.1
  obtain ⟨_,_,_,hc,F,_,_,_,hF,e,_⟩ :=
    d.unitary_overcomponent_split_core h hH hp m hm he hJ hKJ hQR
  have hRc' : Nat.card (pCore 2 J) = (2^m)^3 := by
    rw [Nat.card_congr ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).toEquiv]
    exact hRc
  have hJc : Nat.card J = (2^m)^6*((2^m)^2-1)*((2^m)^3-1) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 J),Nat.card_congr e.toEquiv,
      Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF,hRc']
    ring
  have hf := he.elim (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  obtain ⟨E,_,_,hE,⟨a⟩⟩ := hf.2.2.2.2
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  have hquot : Nat.card (K ⧸ pCore 2 K) = 2^m*((2^m)^2-1) := by
    rw [Nat.card_congr (a.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := E)).symm).toEquiv,
      GorensteinWalter.sl2_card_formula,hE]
  have hQc := (d.unitary_core_structure h hH.1.1.2 hp m hm he).2.2.2.2.1
  have hKc : Nat.card K = (2^m)^6*((2^m)^2-1) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 K),hquot,hQc]
    ring
  have hh := (K.subgroupOf J).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hKJ.le).toEquiv,hJc,←hKc] at hh
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hh

/-- The original common Sylow is the full intersection T ∩ J, including
the degree-two extension. It need not equal the original sourceS. -/
theorem Preparation.unitary_overcomponent_full_common_sylow
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    (T : Subgroup G) ⊓ J = (T : Subgroup G) ⊓ L := by
  let K := residual H
  have hindex : ¬ 2 ∣ (K.subgroupOf J).index := by
    change ¬ 2 ∣ K.relIndex J
    rw [d.unitary_overcomponent_index h hH hp m hm he hJ hKJ hQR]
    have hc : (2^m)^3 % 2 = 0 := by simp [Nat.pow_mod,Nat.ne_of_gt (show 0 < m by omega)]
    have hpos : 0 < (2^m)^3 := by positivity
    omega
  obtain ⟨P,hP⟩ := exists_sylow_component
    (hH.1.1.2.trans (le_normalizer_residual H))
  let f := inclusion hKJ.le
  have hf : Function.Injective f := inclusion_injective hKJ.le
  have hpi : ¬ 2 ∣ ((P : Subgroup K).map f).index := by
    rw [index_map_of_injective _ hf,inclusion_range]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index hindex
  let S : Sylow 2 J := (P.isPGroup'.map f).toSylow hpi
  have hST : (S : Subgroup J) ≤ (T : Subgroup G).subgroupOf J := by
    rintro _ ⟨x,hx,rfl⟩
    exact (hP ▸ mem_map_of_mem K.subtype hx).1
  have hSeq := S.is_maximal' T.isPGroup'.comap_subtype hST
  have hmap := congrArg (Subgroup.map J.subtype) hSeq
  change ((T : Subgroup G).subgroupOf J).map J.subtype = ((P : Subgroup K).map f).map J.subtype at hmap
  rw [subgroupOf_map_subtype,map_map] at hmap
  have hcomp : J.subtype.comp f = K.subtype := rfl
  rw [hcomp,hP] at hmap
  exact hmap.trans (d.common_sylow_of_comparison h hH.1.1.2 hp
    (he.elim (.unitary m hm) (.unitaryExtension m hm))).symm

/-- The literal left-core normalizer in J contains R and the full common
Sylow. Original uniqueness controls its ambient normalizer; its quotient
by the intersection with L has odd order, so its terminal derived subgroup
lies in L. This does not yet identify it as a parabolic. -/
theorem Preparation.unitary_overcomponent_left_core_normalizer
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    L.pCoreIn 2 ≤ J ∧
      normalizer (L.pCoreIn 2 : Set G) = normalizer (L : Set G) ∧
      (let Y := J ⊓ normalizer (L.pCoreIn 2 : Set G)
       J.pCoreIn 2 ≤ Y ∧
         (∃ P : Sylow 2 Y, (P : Subgroup Y).map Y.subtype = (T : Subgroup G) ⊓ L) ∧
         (solvableResidual Y).map Y.subtype ≤ L) := by
  let U := L.pCoreIn 2
  let Y := J ⊓ normalizer (U : Set G)
  have hs := d.unitary_overcomponent_full_common_sylow h hH hp m hm he hJ hKJ hQR
  obtain ⟨P,hP⟩ := exists_sylow_component h.sylow_normalizes
  have hUTL : U ≤ (T : Subgroup G) ⊓ L := (pCoreIn_le_sylow L P).trans_eq hP
  have hUJ : U ≤ J := (hUTL.trans_eq hs.symm).trans inf_le_right
  have hUne : U ≠ ⊥ := by
    intro hz
    have hc := (d.unitary_core_structure h hH.1.1.2 hp m hm he).2.2.2.1
    have heq : Nat.card U = (2^m)^4 :=
      (Nat.card_congr ((pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective).symm.toEquiv).trans hc
    rw [hz,card_bot] at heq
    have hb : 2 ≤ 2^m := by simpa using Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hm
    have hh := Nat.pow_le_pow_left hb 4
    omega
  have hnorm : normalizer (U : Set G) = normalizer (L : Set G) := by
    apply le_antisymm
    · exact normalizer_le_of_unique_maximalTwoLocal d.unique_left (isPGroup_pCoreIn 2 L)
        hUne (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    · exact normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  have hTY : (T : Subgroup G) ⊓ J ≤ Y := le_inf inf_le_right
    (inf_le_left.trans (h.sylow_normalizes.trans hnorm.symm.le))
  have hYJ : Y ≤ J := inf_le_left
  have hYM : Y ≤ normalizer (L : Set G) := inf_le_right.trans hnorm.le
  have hRY : J.pCoreIn 2 ≤ Y := by
    have hRT := (d.unitary_overcomponent_core_intersection h hH hp m hm he hJ hKJ.le).1.trans
      (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
    exact (le_inf hRT (pCoreIn_le 2 J)).trans hTY
  obtain ⟨_,_,_,S,hS,_⟩ := d.unitary_overcomponent_embedding_context h hH hp m hm he hJ hKJ
  have hSm : (S : Subgroup J).map J.subtype = (T : Subgroup G) ⊓ J := by
    rw [hS,subgroupOf_map_subtype]
  obtain ⟨Q,hQ⟩ := S.exists_map_subtype_eq_of_le hYJ (hSm ▸ hTY)
  have hQm : (Q : Subgroup Y).map Y.subtype = (T : Subgroup G) ⊓ L :=
    hQ.trans (hSm.trans hs)
  let N := L.subgroupOf Y
  let : N.Normal := normal_subgroupOf_of_le_normalizer hYM
  have hQN : (Q : Subgroup Y) ≤ N := by
    intro y hy
    exact (hQm ▸ mem_map_of_mem Y.subtype hy).2
  have hodd : Odd (Nat.card (Y ⧸ N)) := by
    change Odd N.index
    exact Nat.not_even_iff_odd.mp (by
      rw [even_iff_two_dvd]
      exact fun hd => Q.not_dvd_index (hd.trans (index_dvd_of_le hQN)))
  let : Group.IsSolvable (Y ⧸ N) := odd_order_theorem _ hodd
  have hres : (solvableResidual Y).map Y.subtype ≤ L := by
    rintro _ ⟨y,hy,rfl⟩
    exact solvableResidual_le_of_solvable_quotient N hy
  exact ⟨hUJ,hnorm,hRY,⟨Q,hQm⟩,hres⟩

/-- Original uniqueness prevents L ≤ J. Thus the left intersection lies
in the rank-one Borel, and the actual left-core normalizer in J is solvable.
The remaining second-parabolic geometry must contradict this conclusion. -/
theorem Preparation.unitary_overcomponent_left_core_normalizer_solvable
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    Group.IsSolvable (J ⊓ normalizer (L.pCoreIn 2 : Set G) : Subgroup G) := by
  let Y := J ⊓ normalizer (L.pCoreIn 2 : Set G)
  have hLJ : ¬ L ≤ J := by
    intro hLJ
    have hcore : pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G) ≠ ⊥ := by
      intro hz
      apply hJ.2.2
      change (pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G)).map (J ⊔ (T : Subgroup G)).subtype = ⊥
      rw [hz,Subgroup.map_bot]
    obtain ⟨X,hX,hYX⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
      (J ⊔ (T : Subgroup G)) hcore
    have hx := d.unique_left X hX (hLJ.trans (le_sup_left.trans hYX))
    exact d.right_outside (hx ▸ hKJ.le.trans (le_sup_left.trans hYX))
  have hs := d.unitary_overcomponent_full_common_sylow h hH hp m hm he hJ hKJ hQR
  have hf : ChapterF.Source.RankOneBorelFacts L (sourceS L H) :=
    (d.hypothesisF11 h hH.1.1.2).rankOneBorelFacts 0
  have hIB : L ⊓ J ≤ ChapterF.Source.borel L (sourceS L H) := by
    apply hf.unique_maximal
    · rw [d.left_intersection]
      exact le_inf inf_le_right (hs.symm ▸ inf_le_right)
    · exact lt_of_le_of_ne inf_le_left (fun hh => hLJ (hh ▸ inf_le_right))
  have hres := (d.unitary_overcomponent_left_core_normalizer h hH hp m hm he hJ hKJ hQR).2.2.2.2
  have hRB : (solvableResidual Y).map Y.subtype ≤ ChapterF.Source.borel L (sourceS L H) :=
    (le_inf hres ((map_subtype_le _).trans inf_le_left)).trans hIB
  let : Group.IsSolvable (ChapterF.Source.borel L (sourceS L H)) := hf.solvable
  let : Group.IsSolvable ((solvableResidual Y).map Y.subtype) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hRB)
  let : Group.IsSolvable (solvableResidual Y) := Group.isSolvable_of_isSolvable_injective
    (f := ((solvableResidual Y).equivMapOfInjective Y.subtype Y.subtype_injective).toMonoidHom)
    ((solvableResidual Y).equivMapOfInjective Y.subtype Y.subtype_injective).injective
  exact isSolvable_of_normal_subgroup_and_quotient (solvableResidual Y)

end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
