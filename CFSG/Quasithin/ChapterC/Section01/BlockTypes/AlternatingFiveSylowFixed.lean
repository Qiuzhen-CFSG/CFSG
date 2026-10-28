module
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# The Sylow-fixed line of an alternating-five block

The actual binary permutation module has a fixed subgroup of order two for
any Sylow two-group. Transport through the defining block model preserves
this bound. The A₅ two-core splitting then projects a radical-fixed subgroup
onto that line and the component centralizer. An actor normalizing both the
component and its radical fixes the line, so its commutators centralize the
component.

Source: Aschbacher–Smith C.1.13(c), pp.124–125, and the A₅ argument in
15.3.19, p.1127. The latter application retains the actual radical Sylow
hypothesis; no arbitrary transposition subgroup is treated as Sylow.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC
open BinaryPermutation.CubicFixedSpace.Five

private theorem alternatingFive_fixed_card
    (P : Sylow 2 (alternatingGroup (Fin 5))) :
    Nat.card (fixedSpace (BinaryPermutation.alternatingCoreRepresentation (Fin 5))
      (P : Subgroup _)) ≤ 2 := by
  let r := BinaryPermutation.alternatingCoreRepresentation (Fin 5)
  have hk : Nat.card (fixedSpace r klein) ≤ 2 := by
    let f : fixedSpace r klein → ZMod 2 := fun v => v.val.val 0
    have hf : Function.Injective f := by
      intro x y he
      have hh : ∀ x y : BinaryPermutation.Full (Fin 5),
          (∑ i, x i) = 0 → (∑ i, y i) = 0 →
          BinaryPermutation.representation (Fin 5) first.val x = x →
          BinaryPermutation.representation (Fin 5) second.val x = x →
          BinaryPermutation.representation (Fin 5) first.val y = y →
          BinaryPermutation.representation (Fin 5) second.val y = y →
          x 0 = y 0 → x = y := by
        simp only [funext_iff, BinaryPermutation.representation_apply]
        decide +kernel
      exact Subtype.ext (Subtype.ext (hh x.val.val y.val.val x.val.property y.val.property
        (congrArg Subtype.val (x.property ⟨first,first_mem⟩))
        (congrArg Subtype.val (x.property ⟨second,second_mem⟩))
        (congrArg Subtype.val (y.property ⟨first,first_mem⟩))
        (congrArg Subtype.val (y.property ⟨second,second_mem⟩)) he))
    simpa using Nat.card_le_card_of_injective f hf
  obtain ⟨Q,hQ⟩ := klein_isPGroup.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) Q P
  have hP : (Q : Subgroup _).map (MulAut.conj g).toMonoidHom = (P : Subgroup _) := by
    rw [←hg]
    rfl
  have hle : klein.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup _) :=
    (map_mono hQ).trans_eq hP
  have hfix : fixedSpace r (P : Subgroup _) ≤
      fixedSpace r (klein.map (MulAut.conj g).toMonoidHom) := by
    intro v hv a
    exact hv ⟨a,hle a.property⟩
  have hc := Nat.card_le_card_of_injective
    (Submodule.inclusion hfix) (Submodule.inclusion_injective hfix)
  rw [←Nat.card_congr (fixedSpaceConjEquiv r klein g).toEquiv] at hc
  exact hc.trans hk

variable {L : Type*} [Group L] [Finite L]
/-- The actual fixed subgroup of the binary A₅ block module is a line. -/
theorem IsAlternatingBlock.sylow_fixed_card_le_two (h : IsAlternatingBlock L 5)
    (P : Sylow 2 L) :
    Nat.card (blockU L ⊓ centralizer (P : Set L) : Subgroup L) ≤ 2 := by
  obtain ⟨r,⟨m⟩,hr⟩ := h.2.2
  let q := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  let e := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let f : blockU L → BinaryPermutation.core (Fin 5) := fun u =>
    e.symm (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)).toAdd
  have hf : Function.Injective f := e.symm.injective.comp
    (Multiplicative.toAdd.injective.comp (m.moduleIso.injective.comp
      ((QuotientGroup.mk' (blockFixed L)).ker_eq_bot_iff.mp (by
        rw [QuotientGroup.ker_mk',h.blockFixed_eq_bot]))))
  let j : (blockU L ⊓ centralizer (P : Set L) : Subgroup L) →
      fixedSpace (BinaryPermutation.alternatingCoreRepresentation (Fin 5))
        ((P.mapSurjective hq : Sylow 2 (alternatingGroup (Fin 5))) : Subgroup _) := fun u =>
    ⟨f ⟨u,u.property.1⟩,by
      intro a
      obtain ⟨l,hl,he⟩ := a.property
      change q l = (a : alternatingGroup (Fin 5)) at he
      apply e.injective
      change e (BinaryPermutation.coreRepresentation (Fin 5) (a.val.val)
        (f ⟨u,u.property.1⟩)) = e (f ⟨u,u.property.1⟩)
      rw [BinaryPermutation.coreEquivNatural_equivariant]
      change BinaryPermutation.alternatingNaturalRepresentation (Fin 5) a
        (e (f ⟨u,u.property.1⟩)) = _
      simp only [f,e.apply_symm_apply]
      rw [←he]
      have hconj : blockConjugate L l ⟨u,u.property.1⟩ = ⟨u,u.property.1⟩ := by
        apply Subtype.ext
        change l * (u:L) * l⁻¹ = (u:L)
        rw [(mem_centralizer_iff.mp u.property.2) l hl,mul_inv_cancel_right]
      have hh := congrArg Multiplicative.toAdd (m.intertwining l ⟨u,u.property.1⟩)
      rw [hconj] at hh
      exact (hh.trans (hr (q l) (m.moduleIso (QuotientGroup.mk' _ ⟨u,u.property.1⟩)))).symm⟩
  have hj : Function.Injective j := by
    intro u v he
    have hh : (⟨u,u.property.1⟩ : blockU L) = ⟨v,v.property.1⟩ :=
      hf (congrArg Subtype.val he)
    exact Subtype.ext (congrArg (fun z : blockU L => (z : L)) hh)
  exact (Nat.card_le_card_of_injective j hj).trans (alternatingFive_fixed_card _)
end CFSG.Quasithin.ChapterC
public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem fixed_split
    (U C R : Subgroup G) (hUC : C ≤ centralizer (U : Set G)) (hd : Disjoint U C)
    (hRU : R ≤ normalizer (U : Set G)) (hRC : R ≤ normalizer (C : Set G)) :
    (U ⊔ C) ⊓ centralizer (R : Set G) ≤
      (U ⊓ centralizer (R : Set G)) ⊔ C := by
  rintro v ⟨hv,hvR⟩
  have hv' : v ∈ (U : Set G) * (C : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left U C
      (hUC.trans (Subgroup.centralizer_le_normalizer _))]
    exact hv
  obtain ⟨u,hu,c,hc,rfl⟩ := hv'
  have huR : u ∈ centralizer (R : Set G) := by
    intro r hr
    have he : (r*u*r⁻¹)*(r*c*r⁻¹) = u*c := by
      calc
        _ = r*(u*c)*r⁻¹ := by group
        _ = u*c := by rw [(mem_centralizer_iff.mp hvR) r hr,mul_inv_cancel_right]
    have hh : ((⟨r*u*r⁻¹,(hRU hr u).mp hu⟩,⟨r*c*r⁻¹,(hRC hr c).mp hc⟩) : U × C) =
        (⟨u,hu⟩,⟨c,hc⟩) := mul_injective_of_disjoint hd he
    have h := congrArg (fun p : U × C => (p.1 : G)) hh
    exact mul_inv_eq_iff_eq_mul.mp h
  exact mul_mem_sup ⟨hu,huR⟩ hc

private theorem commutator_fixed_split_le
    (U C R Y V : Subgroup G) (hUC : C ≤ centralizer (U : Set G)) (hd : Disjoint U C)
    (hRU : R ≤ normalizer (U : Set G)) (hRC : R ≤ normalizer (C : Set G))
    (hYU : Y ≤ normalizer (U : Set G)) (hYC : Y ≤ normalizer (C : Set G))
    (hYR : Y ≤ normalizer (R : Set G))
    (hcard : Nat.card (U ⊓ centralizer (R : Set G) : Subgroup G) ≤ 2)
    (hV : V ≤ U ⊔ C) (hVR : V ≤ centralizer (R : Set G)) : ⁅V,Y⁆ ≤ C := by
  let E := U ⊓ centralizer (R : Set G)
  change Nat.card E ≤ 2 at hcard
  have hYE : Y ≤ normalizer (E : Set G) :=
    (le_inf hYU (hYR.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hCE : Y ≤ centralizer (E : Set G) := by
    by_cases he : E = ⊥
    · rw [he]
      intro y hy z hz
      have hz1 : z = 1 := hz
      simp only [hz1,mul_one,one_mul]
    · have hp : 1 < Nat.card E := (E.one_lt_card_iff_ne_bot).mpr he
      exact hYE.trans (normalizer_le_centralizer_of_card_two E (by omega))
  have hVE : V ≤ E ⊔ C := (le_inf hV hVR).trans (fixed_split U C R hUC hd hRU hRC)
  have hEC : E ≤ normalizer (C : Set G) :=
    (inf_le_left.trans (le_centralizer_iff.mp hUC)).trans (Subgroup.centralizer_le_normalizer _)
  have hpre : E ⊔ C ≤ commutatorPreimage (normalizer (C : Set G)) Y C := by
    apply sup_le
    · exact le_commutatorPreimage hEC
        ((commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hCE)).le.trans bot_le)
    · exact le_commutatorPreimage C.le_normalizer
        (le_normalizer_iff_commutator_le_left.mp hYC)
  exact ((le_commutatorPreimage_iff (normalizer (C : Set G)) Y C V le_rfl).mp
    (hVE.trans hpre)).2
end CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.ChapterC
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
open ChapterC

/-- The A₅ Sylow-fixed line kills the residual action modulo C_Q(L). -/
theorem IsAlternatingBlock.commutator_le_centralizer_of_sylow_fixed
    (L R Y V : Subgroup G) (hb : IsAlternatingBlock L 5)
    (hRL : R ≤ normalizer (L : Set G))
    (hYRL : Y ≤ normalizer (L : Set G)) (hYR : Y ≤ normalizer (R : Set G))
    (hSyl : Chapter1.IsSylowIn 2 R (L ⊔ R))
    (hVQ : V ≤ (L ⊔ R).pCoreIn 2) (hVR : V ≤ centralizer (R : Set G)) :
    ⁅V,Y⁆ ≤ centralizer (L : Set G) := by
  let J := L ⊔ R
  let U := (blockU L).map L.subtype
  let Q := J.pCoreIn 2
  let C := Q ⊓ centralizer (L : Set G)
  have hJN : J ≤ normalizer (L : Set G) := sup_le L.le_normalizer hRL
  have hQsplit : Q = U ⊔ C := hb.normalizer_twoCore_eq_module_sup_centralizer
    (show L ≤ J from le_sup_left) hJN
  have hUC : C ≤ centralizer (U : Set G) :=
    inf_le_right.trans (centralizer_le (map_subtype_le _))
  have hd : Disjoint U C := by
    apply disjoint_def.mpr
    intro x hxU hxC
    obtain ⟨u,hu,rfl⟩ := hxU
    have huZ : u ∈ center L := by
      apply mem_center_iff.mpr
      intro l
      exact Subtype.ext (hxC.2 l l.property)
    have hh : u ∈ blockU L ⊓ center L := ⟨hu,huZ⟩
    have hz : blockU L ⊓ center L = ⊥ := by
      rw [←blockFixed_map,hb.blockFixed_eq_bot,Subgroup.map_bot]
    rw [hz] at hh
    exact congrArg Subtype.val (mem_bot.mp hh)
  have hRU : R ≤ normalizer (U : Set G) :=
    hRL.trans (normalizer_le_normalizer_characteristic_image L (blockU L))
  have hRQ : R ≤ normalizer (Q : Set G) :=
    (le_sup_right : R ≤ J).trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hRC : R ≤ normalizer (C : Set G) :=
    (le_inf hRQ (hRL.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hYU : Y ≤ normalizer (U : Set G) :=
    hYRL.trans (normalizer_le_normalizer_characteristic_image L (blockU L))
  have hYJ : Y ≤ normalizer (J : Set G) :=
    (le_inf hYRL hYR).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hYQ : Y ≤ normalizer (Q : Set G) :=
    hYJ.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hYC : Y ≤ normalizer (C : Set G) :=
    (le_inf hYQ (hYRL.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  let : (L.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJN
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl
    (show L ≤ J from le_sup_left) (inferInstance : (L.subgroupOf J).Normal).isSubnormal
  have hcard : Nat.card (U ⊓ centralizer (R : Set G) : Subgroup G) ≤ 2 := by
    let f : (U ⊓ centralizer (R : Set G) : Subgroup G) →
        (blockU L ⊓ centralizer (P : Set L) : Subgroup L) := fun x =>
      ⟨⟨x,(map_subtype_le (blockU L)) x.property.1⟩,by
        refine ⟨?_,?_⟩
        · obtain ⟨l,hl,he⟩ := x.property.1
          exact (Subtype.ext he : l = ⟨x,_⟩) ▸ hl
        · intro p hp
          apply Subtype.ext
          exact x.property.2 p ((hP ▸ mem_map_of_mem L.subtype hp).1)⟩
    have hf : Function.Injective f := by
      intro x y he
      exact Subtype.ext (congrArg (fun z : (blockU L ⊓ centralizer (P : Set L) : Subgroup L) =>
        ((z : L) : G)) he)
    exact (Nat.card_le_card_of_injective f hf).trans (hb.sylow_fixed_card_le_two P)
  exact (commutator_fixed_split_le U C R Y V hUC hd hRU hRC hYU hYC hYR
    hcard (hVQ.trans_eq hQsplit) hVR).trans inf_le_right
end CFSG.Quasithin.ChapterC
