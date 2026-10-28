module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SylowTwoStep
public import Theory.GroupTheory.CentralElementaryCommutatorProduct
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.CommutingSylow
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.BlockRecovery.CoreEquality
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.LocalClass
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Marking
/-!
# Central elementary commutators of the original common Baumann subgroup

The first recovered natural block and its original T-conjugate commute.
A cubic torus makes the first full Sylow's commutators central and
involutory; conjugation gives the same bound in the second factor.
Baumann placement in the component product and full factor Sylows then
identify the Baumann group with their product. Its intrinsic commutator
therefore lies in its central omega subgroup, as required by the second
component's C.1.17 local class.
Source: Aschbacher--Smith 10.2.3(4), printed p.747.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
private theorem original_block_commutes_conjugate
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    L ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  let X := localJoin T L
  let A := L.subgroupOf X
  have hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
  let tX : X := ⟨t,(show (T : Subgroup G) ≤ X from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tX).toMonoidHom
  have hbB : IsBlock B := hb.map_equiv (MulAut.conj tX)
  have hmapA : A.map X.subtype=L := map_subgroupOf_eq_of_le hLX
  have hmapB : B.map X.subtype=L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map (MulAut.conj tX).toMonoidHom from rfl,map_map]
    rw [show X.subtype.comp (MulAut.conj tX).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp X.subtype from rfl,←map_map,hmapA]
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map X.subtype) he).symm.trans hmapA)
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _
      (subgroupOfEquivOfLe hLX).symm (pCore_map_iso 2 (subgroupOfEquivOfLe hLX).symm))
  have hc := congrArg (map X.subtype) (hb.commutator_eq_bot_of_quasisimple_quotient hbB hqA hne)
  rw [map_commutator,hmapA,hmapB,Subgroup.map_bot] at hc
  exact commutator_eq_bot_iff_le_centralizer.mp hc

theorem source_original_common_baumann_commutator
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (A : Subgroup G) (hL : IsL2EvenBlock L 2)
    (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (localOrbit T L ⊔ baumann (T : Subgroup G)))
    (hSO : baumann (T : Subgroup G) ≤ localOrbit T L)
    (hAL : A ≤ L) (hA : Nat.card A=3)
    (hAS : A ≤ normalizer (baumann (T : Subgroup G) : Set G))
    (hSL : baumann (T : Subgroup G) ≤ normalizer (L : Set G)) :
    commutator (baumann (T : Subgroup G)) ≤
      GlaubermanNiles.omegaCenter (baumann (T : Subgroup G)) := by
  let S := baumann (T : Subgroup G)
  let P := S ⊓ L
  have hcL := source_original_block_core_eq_blockU D e hn hb hz hH hZH
  have hzL := source_original_block_center_eq_bot D hn hb hz
  have hSP : Chapter1.IsSylowIn 2 P L := by
    obtain ⟨he,hp⟩ := source_original_natural_commutator_sylow_of_source
      D e hn hb hz hH hZH A hL hS hAL hA hAS hSL
    simpa only [he] using hp
  have hAP : A ≤ normalizer (P : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [commutator_comm]
    exact le_inf ((commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hAS))
      ((commutator_mono inf_le_right le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hAL.trans L.le_normalizer)))
  have hP := hL.ambient_sylow_commutator_le_omegaCenterIn L P A hcL hzL hSP hAL hA hAP
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let f := (MulAut.conj t).toMonoidHom
  let K := L.map f
  have hc : L ≤ centralizer (K : Set G) := original_block_commutes_conjugate D hb ht htn
  have hSm : S.map f=S := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_baumann _ ((T : Subgroup G).le_normalizer ht))
  have hPm : P.map f=S ⊓ K := by
    rw [show P = S ⊓ L from rfl,map_inf _ _ _ (MulAut.conj t).injective,hSm]
  have hKP : Chapter1.IsSylowIn 2 (S ⊓ K) K := by
    have hh := Chapter1.Section02.IndexTwo.isSylowIn_map hSP f
    rwa [hPm] at hh
  have hK : ⁅S ⊓ K,S ⊓ K⁆ ≤ omegaCenterIn (S ⊓ K) := by
    have hh := map_mono (f := f) hP
    change (⁅P,P⁆).map f ≤ (omegaOneCenterAmbient P).map f at hh
    rw [map_commutator,←omegaOneCenterAmbient_map_injective f (MulAut.conj t).injective,hPm] at hh
    exact hh
  have hsplit : S=P ⊔ (S ⊓ K) := eq_sup_sylow_intersections_of_commuting S L K
    (Chapter1.isSylowIn_iff.mp hS).1 (hSO.trans hpair.le) hc hSP hKP
  have hPP : P ≤ centralizer (S ⊓ K : Set G) :=
    inf_le_right.trans (hc.trans (centralizer_le inf_le_right))
  have hcomm : ⁅S,S⁆ ≤ omegaCenterIn S := by
    have hh := commutator_le_omegaCenterIn_join_of_commuting P (S ⊓ K) hPP hP hK
    rwa [←hsplit] at hh
  intro x hx
  have hm : (commutator S).map S.subtype=⁅S,S⁆ := by
    rw [_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype]
  obtain ⟨_,hxc,hx2⟩ := (mem_omegaCenterIn_iff S (x:G)).mp (hcomm (hm ▸ mem_map_of_mem S.subtype hx))
  exact (GlaubermanNiles.mem_omegaCenter_iff x).mpr
    ⟨Subtype.ext hx2,fun y => Subtype.ext (hxc y y.property)⟩
end CFSG.Quasithin.Chapter10
