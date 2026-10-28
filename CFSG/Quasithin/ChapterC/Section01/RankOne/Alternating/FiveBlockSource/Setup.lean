module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.PResidual.SubnormalSupplement
/-!
# The original external-Sylow setup for C.1.23

The larger two-group T remains external to H: only its Baumann subgroup
lies in the actual Sylow R of H. The canonical first subgroup lies in
Ω₁Z(T), whose H-orbit is an elementary reduced normal subgroup. A genuine
C-component with the given two-group supplement is the literal two-residual.
These are the first reductions of C.1.23(1), not a block assumption.
Source: Aschbacher–Smith C.1.23, printed pp.129–130.
-/
@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
variable {A : Type*} [Group A] [Finite A]

noncomputable def firstAmbient (T : Subgroup A) (D : GlaubermanNiles.CharacteristicPair (ChapterB.baumann T)) : Subgroup A :=
  (center T).map T.subtype ⊓ D.first.map (ChapterB.baumann T).subtype

noncomputable def secondAmbient (T : Subgroup A) (D : GlaubermanNiles.CharacteristicPair (ChapterB.baumann T)) : Subgroup A :=
  D.second.map (ChapterB.baumann T).subtype

omit [Finite A] in
theorem omegaCenter_le_baumann (T : Subgroup A) : omegaOneCenterAmbient T ≤ ChapterB.baumann T := by
  have hJT : elementaryAbelianMaxJ T ≤ T := sSup_le fun _ hE => hE.1
  intro z hz
  obtain ⟨hzT,_,hc⟩ := (mem_omegaOneCenterAmbient_iff T z).mp hz
  refine ⟨hzT,?_⟩
  intro w hw
  exact hc w ((show omegaOneCenterAmbient (elementaryAbelianMaxJ T) ≤ T from
    fun x hx => hJT ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1) hw)

omit [Finite A] in
theorem firstAmbient_le_omegaCenter (T : Subgroup A)
    (D : GlaubermanNiles.CharacteristicPair (ChapterB.baumann T)) :
    firstAmbient T D ≤ omegaOneCenterAmbient T := by
  rintro x ⟨⟨z,hz,rfl⟩,hx⟩
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  refine ⟨z.property,?_,?_⟩
  · obtain ⟨b,hb,he⟩ := hx
    obtain ⟨c,hc,hcb⟩ := D.first_le_omegaCenter hb
    let : IsElementaryAbelian 2 (omega₁ (center (ChapterB.baumann T)) (p:=2)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative _
    have hc2 := congrArg (fun c : center (ChapterB.baumann T) => ((c : ChapterB.baumann T) : A))
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) c hc)
    change ((c : ChapterB.baumann T) : A)^2 = 1 at hc2
    have hec : ((c : ChapterB.baumann T) : A) = (z : A) :=
      (congrArg (ChapterB.baumann T).subtype hcb).trans he
    rwa [hec] at hc2
  · intro t ht
    exact congrArg T.subtype ((mem_center_iff.mp hz) ⟨t,ht⟩)

private theorem perfect_twoPerfect {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] : IsPPerfect 2 G := by
  intro N hn hq
  let : N.Normal := hn
  by_contra hne
  let : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (G ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (G ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (G ⧸ N) inferInstance

theorem component_residual (H L R : Subgroup A) (hLH : L ≤ H) (hRH : R ≤ H)
    (hL : (L.subgroupOf H).IsCComponent) (hR : IsPGroup 2 R)
    (hprod : ∀ g ∈ H, ∃ l ∈ L, ∃ r ∈ R, l*r=g) :
    pResidual 2 H = L.subgroupOf H := by
  let : Group.IsPerfect (L.subgroupOf H) := hL.perfect
  apply pResidual_eq_of_subnormal_product (L.subgroupOf H) (R.subgroupOf H)
    hL.subnormal perfect_twoPerfect hR.comap_subtype
  intro g
  obtain ⟨l,hl,r,hr,he⟩ := hprod g g.property
  exact ⟨⟨l,hLH hl⟩,hl,⟨r,hRH hr⟩,hr,Subtype.ext he⟩

theorem omega_span_reduced (T H R : Subgroup A)
    (hBR : ChapterB.baumann T ≤ R) (hRT : R ≤ T)
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = R)
    (hH : generalizedFitting H = pCore 2 H) :
    let Z := (omegaOneCenterAmbient T).subgroupOf H
    IsPReduced 2 (normalClosure (Z : Set H)) := by
  let Z := (omegaOneCenterAmbient T).subgroupOf H
  have hRH : R ≤ H := hP ▸ map_subtype_le _
  have hZR : omegaOneCenterAmbient T ≤ R := (omegaCenter_le_baumann T).trans hBR
  have hZT : Z ≤ P := by
    intro z hz
    have hzR : (z : A) ∈ R := hZR hz
    rw [←hP] at hzR
    obtain ⟨p,hp,he⟩ := hzR
    exact H.subtype_injective he ▸ hp
  have hc : Z ≤ centralizer (P : Set H) := by
    intro z hz p hp
    apply Subtype.ext
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 p (hRT (hP ▸ mem_map_of_mem H.subtype hp))
  have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mp hH
  have hZQ : Z ≤ pCore 2 H := fun z hz => hchar
    ((centralizer_le (pCore_isPGroup.le_sylow_of_normal P)) (hc hz))
  let V := normalClosure (Z : Set H)
  have hVQ : V ≤ pCore 2 H := normalClosure_le_normal hZQ
  have hVC : V ≤ centralizer (pCore 2 H : Set H) := normalClosure_le_normal
    (hc.trans (centralizer_le (pCore_isPGroup.le_sylow_of_normal P)))
  let : IsMulCommutative V := le_centralizer_iff_isMulCommutative.mp
    (hVC.trans (centralizer_le hVQ))
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient T) := omegaOneCenterAmbient_elementaryAbelian T
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf (hZR.trans hRH)
  exact isPReduced_normalClosure_of_sylow_central P Z hZT hc
end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
