module

public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalA5SymplecticAlignment
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalSeedMovedModule
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.NaturalStarFieldDegree
public import Theory.Representation.FirstCohomologySymplecticFour.LargeField
public import Theory.Representation.SymplecticFourOrthogonalCover.ParabolicFixed

/-!
# The constrained symplectic cover has no original fixed point

The same natural marking identifies the original normal A₅ seed with a
point or plane parabolic residual over the field of four elements. The
whole original module embeds in the literal moved cover, is fixed by the
complete image two-core, and is fully moved by that residual. The intrinsic
orthogonal-cover splitting theorem therefore kills every globally fixed
original point. No module embedding or parabolic alignment is assumed.

Source: the constrained symplectic exclusion in Aschbacher--Smith C.4.8
and 12.7.5, printed pp.154 and 840.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open Theory.SpecificGroups.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource

private theorem exists_derived_natural_marking {F : BinaryField} (hF : 2 < Nat.card F.Carrier)
    {D : Type*} [Group D] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} (e : ActionEquiv ρ (binarySymplectic F)) :
    ∃ e' : ActionEquiv ρ (binaryNatural (K := F.Carrier)),
      ∀ d, (e'.groupEquiv d).val = e.groupEquiv d := by
  let d : commutator (Sp F.Carrier) ≃* Sp F.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF)).trans
      Subgroup.topEquiv
  refine ⟨⟨e.groupEquiv.trans d.symm,e.linearEquiv,?_⟩,?_⟩
  · intro g v
    change e.linearEquiv (ρ g v) =
      Matrix.mulVec (d.symm (e.groupEquiv g)).val.val (e.linearEquiv v)
    rw [show (d.symm (e.groupEquiv g)).val = e.groupEquiv g from d.apply_symm_apply _]
    exact e.intertwines g v
  · intro g
    exact d.apply_symm_apply _

set_option maxHeartbeats 800000 in
/-- In the genuine symplectic branch of the actual moved section, no
nonidentity element of the original module centralizes the selected component. -/
theorem constrained_normal_a5_symplectic_module_centralizer
    {G : Type*} [Group G] [Finite G] {H M L₀ R V : Subgroup G}
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L₀ R V)
    (hn : (L₀.subgroupOf M).Normal)
    (eA5 : (L₀ ⧸ pCore 2 L₀) ≃* alternatingGroup (Fin 5))
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hout : ¬ J ≤ M.subgroupOf H)
    (hf : generalizedFitting J = pCore 2 J)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation (J.map H.subtype) R).comp
        (offenderSubgroup (starRepresentation (J.map H.subtype) R)).subtype)
      ((starImage (J.map H.subtype) R (J.map H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (J.map H.subtype) R))))
    (hi : IsIrrPlus ((starRepresentation (J.map H.subtype) R).comp
        (offenderSubgroup (starRepresentation (J.map H.subtype) R)).subtype)
      ((starImage (J.map H.subtype) R (J.map H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (J.map H.subtype) R))) c.sectionData.space.toSubmodule)
    (F : BinaryField)
    (a : ActionEquiv (c.sectionData.action.comp
      ((starImage (J.map H.subtype) R (J.map H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (J.map H.subtype) R))).subtype)
      (binarySymplectic F)) :
    V ⊓ centralizer (J.map H.subtype : Set G) = ⊥ := by
  let K := J.map H.subtype
  let ρ := starRepresentation K R
  let O := offenderSubgroup ρ
  let C := starImage K R K
  let s := c.sectionData
  have hCO : C ≤ O := (C27Source.star_moved_section_from_source
    (h.constrained_source_input J hJ hq hout hf)).1
  let eC := subgroupOfEquivOfLe hCO
  let e := eC.symm.trans a.groupEquiv
  have hlarge := C27Source.star_symplectic_degree_gt_one_from_source
    (h.constrained_source_input J hJ hq hout hf) F e
  obtain ⟨hF,g,hg⟩ := h.constrained_normal_a5_symplectic_alignment hn eA5 J hJ hq hout hf
    e F.card_eq hlarge
  obtain ⟨aD,haD⟩ := exists_derived_natural_marking (by omega : 2 < Nat.card F.Carrier) a
  let E := eC.symm.trans aD.groupEquiv
  let q := E.toMonoidHom.comp (toStarImage K R)
  let B := (L₀.subgroupOf K).map q
  let σ := MovedSection.coverAction s aD
  obtain ⟨A,hA,hm,hlift⟩ := h.constrained_normal_seed_moved_module hn eA5 J hJ hq hout hf
    s aD.groupEquiv
  have hmark : (B.map (commutator (Sp F.Carrier)).subtype).map (MulAut.conj g).toMonoidHom =
      (L₀.subgroupOf K).map ((e.trans (MulAut.conj g)).toMonoidHom.comp (toStarImage K R)) := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro k
    change MulAut.conj g ((aD.groupEquiv (eC.symm (toStarImage K R k))).val) =
      MulAut.conj g (a.groupEquiv (eC.symm (toStarImage K R k)))
    rw [haD]
  have hlocal :
      (B.map (commutator (Sp F.Carrier)).subtype).map (MulAut.conj g).toMonoidHom = pointLocal ∨
      (B.map (commutator (Sp F.Carrier)).subtype).map (MulAut.conj g).toMonoidHom = planeLocal := by
    rw [hmark]
    exact hg.imp And.right And.right
  have hp : Representation.OneCohomology.IsCover (MovedSection.coverProjection s aD) :=
    MovedSection.coverProjection_isCover s hi aD
  apply bot_unique
  intro v hv
  obtain ⟨w,hw,he,hfix⟩ := hlift (⟨v,hv.1⟩ : V)
  have hw0 : w = 0 := ParabolicFixed.cover_fixed_eq_zero_of_moved_subspace hF
    (MovedSection.coverProjection s aD) hp B g hlocal A hA hm w hw (hfix hv.2)
  have hh := congrArg (fun z : s.space.toSubmodule =>
    (((z.val.toMul : starV K R) : (K ⊔ R : Subgroup G)) : G)) hw0
  rw [he] at hh
  exact mem_bot.mpr hh

end CFSG.Quasithin.ChapterC.HypothesisC28
