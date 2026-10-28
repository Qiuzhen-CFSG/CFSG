module

public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalSeedMovedModule
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalA5G2Alignment
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.NaturalStarFieldDegree
public import Theory.Representation.G2OrthogonalCover.ParabolicFixed

/-!
# No original central point in the constrained natural G₂ row

The original module lies fully moved in the literal classified cover and
is fixed by the entire two-core of its actual marked A₅ seed image. The
source alignment makes this image a root local residual. The Cayley-cover
calculation then makes this module disjoint from the global fixed space.
Every original point is tracked by its unchanged ambient group element.

Source: Aschbacher--Smith C.4.1 and 12.7.5, printed pp.151 and 840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource

/-- The actual original module has no point centralized by the selected
component in its full natural G₂ row. -/
theorem constrained_normal_a5_g2_fixed_eq_bot
    {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal)
    (eA5 : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hout : ¬ J ≤ M.subgroupOf H)
    (hf : generalizedFitting J = pCore 2 J)
    (s : MovedSection ((starRepresentation (J.map H.subtype) R).comp
      (offenderSubgroup (starRepresentation (J.map H.subtype) R)).subtype)
      ((starImage (J.map H.subtype) R (J.map H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (J.map H.subtype) R))))
    (hi : IsIrrPlus ((starRepresentation (J.map H.subtype) R).comp
      (offenderSubgroup (starRepresentation (J.map H.subtype) R)).subtype)
      ((starImage (J.map H.subtype) R (J.map H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (J.map H.subtype) R))) s.space.toSubmodule)
    (F : BinaryField)
    (e : ActionEquiv (s.action.comp
      ((starImage (J.map H.subtype) R (J.map H.subtype)).subgroupOf
        (offenderSubgroup (starRepresentation (J.map H.subtype) R))).subtype) (binaryG2 F)) :
    V ⊓ centralizer (J.map H.subtype : Set G) = ⊥ := by
  let K := J.map H.subtype
  let ρ := starRepresentation K R
  let O := offenderSubgroup ρ
  let C := starImage K R K
  have hsource := h.constrained_source_input J hJ hq hout hf
  have hCO : C ≤ O := (C27Source.star_moved_section_from_source hsource).1
  let E := (subgroupOfEquivOfLe hCO).symm.trans e.groupEquiv
  have hdeg := C27Source.star_g2_degree_gt_one_from_source hsource F E
  have hF : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact (show 4 = 2 ^ 2 from rfl).trans_le (Nat.pow_le_pow_right (by decide) hdeg)
  obtain ⟨_,g,hg⟩ := h.constrained_normal_a5_g2_alignment hn eA5 J hJ hq hout hf E hF
  obtain ⟨A,hA,hm,hlift⟩ := h.constrained_normal_seed_moved_module
    hn eA5 J hJ hq hout hf s e.groupEquiv
  let σ := s.coverAction e
  let p := s.coverProjection e
  have hp := s.coverProjection_isCover hi e
  let B := (L.subgroupOf K).map (E.toMonoidHom.comp (toStarImage K R))
  have hb : B.map (MulAut.conj g).toMonoidHom = Atlas.G2.LieParabolicSetup.local₁ ∨
      B.map (MulAut.conj g).toMonoidHom = Atlas.G2.LieParabolicSetup.local₂ := hg
  have hd : Disjoint A (Representation.OneCohomology.fixed σ) :=
    Atlas.G2.Natural.OrthogonalCover.ParabolicFixed.cover_moved_subspace_disjoint
      F.Carrier p (by omega) hp B g hb A hA hm
  apply bot_unique
  intro v hv
  obtain ⟨w,hw,he,hfix⟩ := hlift ⟨v,hv.1⟩
  have hz : w = 0 := Submodule.disjoint_def.mp hd w hw (hfix hv.2)
  apply mem_bot.mpr
  rw [hz] at he
  exact he.symm

end CFSG.Quasithin.ChapterC.HypothesisC28
