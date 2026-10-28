module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.ProductExtensions
public import Theory.Representation.BinaryPermutation.FiveCentralExtension
public import Theory.SpecificGroups.Alternating.FiveComponents

/-!
# The symmetric-five product marking on the original moved subgroup

The selected component maps to the literal alternating subgroup of the
specified S5 factor. The three-cycle class-sum section of its actual natural
quotient identifies the alternating moved space before taking any new
quotient. Perfectness transports this space back to the original ambient
module, preserving the action of the full S5 factor.

These coordinates determine the full normalizer action. Its S5 image and
the original Sylow two-subgroup give a surjective action of LT, with the
original component mapping onto A5. This constructs the deleted-module
marking required by 13.1.10(2).

Source: Aschbacher--Smith 13.1.10, pp.871--872, and B.5.6(3a), p.105.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
namespace ProductMarkings
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

/-- The selected component maps to the literal alternating subgroup. -/
theorem five_component_map {A C : Subgroup D} (hC : IsComponent D C) (hCA : C ≤ A)
    (e : A ≃* Equiv.Perm (Fin 5)) :
    (C.subgroupOf A).map e.toMonoidHom = alternatingGroup (Fin 5) := by
  let K := (C.subgroupOf A).map e.toMonoidHom
  have hK : IsComponent (Equiv.Perm (Fin 5)) K := (hC.subgroupOf hCA).map_equiv e
  let : IsQuasisimple K := hK.2
  have hle : K ≤ alternatingGroup (Fin 5) :=
    le_of_isPerfect_of_index_eq_two K _ alternatingGroup.index_eq_two
  have hc := hK.subgroupOf hle
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have ht := (hc.1.eq_bot_or_top_of_isSimpleGroup inferInstance).resolve_left hc.isCComponent.ne_bot
  exact le_antisymm hle (subgroupOf_eq_top.mp ht)

def fiveComponentEquiv {A C : Subgroup D} (hCA : C ≤ A)
    (e : A ≃* Equiv.Perm (Fin 5))
    (he : (C.subgroupOf A).map e.toMonoidHom = alternatingGroup (Fin 5)) :
    C ≃* alternatingGroup (Fin 5) :=
  (subgroupOfEquivOfLe hCA).symm.trans
    (((C.subgroupOf A).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr he))

theorem fiveComponentEquiv_apply {A C : Subgroup D} (hCA : C ≤ A)
    (e : A ≃* Equiv.Perm (Fin 5))
    (he : (C.subgroupOf A).map e.toMonoidHom = alternatingGroup (Fin 5)) (c : C) :
    (fiveComponentEquiv hCA e he c).val = e (inclusion hCA c) := by
  change e (inclusion hCA c) = e (inclusion hCA c)
  rfl

/-- The class-sum section identifies the actual alternating moved subspace,
with the action of every symmetric permutation retained. -/
def fiveMovedEquiv (σ : Representation (ZMod 2) (Equiv.Perm (Fin 5)) V)
    (p : V →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (σ g v) = BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hk : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5), σ g v = v) :
    ActionEquiv (MovedSection.ofNormal σ (alternatingGroup (Fin 5))).space.toRepresentation
      (BinaryPermutation.naturalRepresentation (Fin 5)) := by
  let s := MovedSection.ofNormal σ (alternatingGroup (Fin 5))
  let hex := BinaryPermutation.FiveCentralExtension.exists_moved_section σ p hp he hk
  let f := Classical.choose hex
  have hf := (Classical.choose_spec hex).1
  have hfr := (Classical.choose_spec hex).2.2
  have hr : f.range = s.space.toSubmodule := hfr.trans s.space_eq.symm
  let e : s.space.toSubmodule ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5) := {
    toFun v := p v
    invFun w := ⟨f w, hr ▸ ⟨w,rfl⟩⟩
    left_inv v := by
      apply Subtype.ext
      change f (p (v : V)) = (v : V)
      obtain ⟨w,hw⟩ := (hr.symm ▸ v.property : (v : V) ∈ f.range)
      rw [← hw]
      exact congrArg f (hf w)
    right_inv := hf
    map_add' _ _ := p.map_add _ _
    map_smul' _ _ := p.map_smul _ _ }
  let c := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  exact ⟨MulEquiv.refl _,e.trans c,fun g v =>
    (congrArg c (he g v)).trans (BinaryPermutation.coreEquivNatural_equivariant _ _ g (p v))⟩

/-- Restrict the genuine S5 factor quotient to its actual alternating component.
The projection's kernel is globally fixed; perfectness identifies the moved
space before and after restriction to the original factor space. -/
def twoFactors_fiveAction {C : Subgroup D} [Group.IsPerfect C]
    (d : SourceTwoFactorCase ρ) (s : MovedSection ρ C) (hCA : C ≤ d.first)
    (hm : d.firstSpace.toSubmodule = moved ρ d.first)
    (a : ActionEquiv (((fixed ρ).quotientImage d.firstSpace).toRepresentation.comp d.first.subtype)
      (BinaryPermutation.naturalRepresentation (Fin 5)))
    (hCmap : (C.subgroupOf d.first).map a.groupEquiv.toMonoidHom = alternatingGroup (Fin 5)) :
    MarkedActionEquiv s.space.toRepresentation d.first C
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)) := by
  let W := d.firstSpace
  let e := a.groupEquiv
  let f := d.first.subtype.comp e.symm.toMonoidHom
  let σ := W.toRepresentation.comp f
  let c := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let p := c.symm.toLinearMap.comp (a.linearEquiv.toLinearMap.comp (imageProjection W))
  have hp : Function.Surjective p := c.symm.surjective.comp
    (a.linearEquiv.surjective.comp (imageProjection_surjective W))
  have he (g : Equiv.Perm (Fin 5)) (v : W.toSubmodule) :
      p (σ g v) = BinaryPermutation.coreRepresentation (Fin 5) g (p v) := by
    have hh := a.intertwines (e.symm g) (imageProjection W v)
    change a.linearEquiv (imageProjection W (σ g v)) =
      BinaryPermutation.naturalRepresentation (Fin 5) (e (e.symm g))
        (a.linearEquiv (imageProjection W v)) at hh
    rw [e.apply_symm_apply] at hh
    apply c.injective
    change c (c.symm (a.linearEquiv (imageProjection W (σ g v)))) =
      c (BinaryPermutation.coreRepresentation (Fin 5) g
        (c.symm (a.linearEquiv (imageProjection W v))))
    rw [c.apply_symm_apply,BinaryPermutation.coreEquivNatural_equivariant,c.apply_symm_apply]
    exact hh
  have hk (v : W.toSubmodule) (hv : p v = 0) (g : Equiv.Perm (Fin 5))
      (_hg : g ∈ alternatingGroup (Fin 5)) : σ g v = v := by
    have hv' : imageProjection W v = 0 := by
      apply a.linearEquiv.injective
      apply c.symm.injective
      change c.symm (a.linearEquiv (imageProjection W v)) = 0 at hv
      simpa only [map_zero] using hv
    have hf : (v : V) ∈ ρ.invariants :=
      (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hv')
    exact Subtype.ext (hf (f g))
  let t := MovedSection.ofNormal σ (alternatingGroup (Fin 5))
  let b := fiveMovedEquiv σ p hp he hk
  have hmap : (alternatingGroup (Fin 5)).map f = C := by
    rw [← hCmap,Subgroup.map_map]
    have hfun : f.comp e.toMonoidHom = d.first.subtype := by
      ext g
      exact congrArg Subtype.val (e.symm_apply_apply g)
    rw [hfun,map_subgroupOf_eq_of_le hCA]
  have hmC : moved ρ C ≤ W.toSubmodule := by
    rw [hm]
    apply Submodule.span_mono
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact ⟨g,hCA hg,v,hv,rfl⟩
  have hcomm : subspaceCommutator ρ W.toSubmodule C = moved ρ C :=
    subspaceCommutator_eq_moved_of_contains_moved ρ C W.toSubmodule hmC
  have ht : t.space.toSubmodule.map W.toSubmodule.subtype = s.space.toSubmodule := by
    rw [t.space_eq,s.space_eq,← hcomm]
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,_,rfl⟩
      change ρ (f g) (v : V) - (v : V) ∈ subspaceCommutator ρ W.toSubmodule C
      exact Submodule.subset_span ⟨f g,hmap ▸ Subgroup.mem_map_of_mem f hg,
        v,v.property,rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,hv,rfl⟩
      obtain ⟨k,hk,rfl⟩ := (hmap.symm ▸ hg : g ∈ (alternatingGroup (Fin 5)).map f)
      refine ⟨σ k ⟨v,hv⟩ - ⟨v,hv⟩,?_,rfl⟩
      exact Submodule.subset_span ⟨k,hk,⟨v,hv⟩,Submodule.mem_top,rfl⟩
  let j : t.space.toSubmodule ≃ₗ[ZMod 2] s.space.toSubmodule :=
    (Submodule.equivMapOfInjective W.toSubmodule.subtype W.toSubmodule.subtype_injective
      t.space.toSubmodule).trans (LinearEquiv.ofEq _ _ ht)
  have hj (g : d.first) (v : t.space.toSubmodule) :
      j (t.space.toRepresentation (e g) v) = s.space.toRepresentation g (j v) := by
    apply Subtype.ext
    change ρ (e.symm (e g) : d.first) v.val.val = ρ g v.val.val
    rw [e.symm_apply_apply]
  have hbgroup (g : Equiv.Perm (Fin 5)) : b.groupEquiv g = g := by rfl
  let act : ActionEquiv (s.space.toRepresentation.comp d.first.subtype)
      (BinaryPermutation.naturalRepresentation (Fin 5)) := {
    groupEquiv := e
    linearEquiv := j.symm.trans b.linearEquiv
    intertwines := by
      intro g v
      obtain ⟨w,rfl⟩ := j.surjective v
      change b.linearEquiv (j.symm (s.space.toRepresentation g (j w))) = _
      rw [← hj,j.symm_apply_apply]
      simp only [LinearEquiv.trans_apply,j.symm_apply_apply]
      simpa only [hbgroup] using b.intertwines (e g) w }
  exact ⟨act,hCA,fiveComponentEquiv hCA e hCmap,fun _ => rfl⟩

end ProductMarkings
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A deleted action of the full reduced normalizer induces the literal
surjective S5 action on LT, preserving its alternating component image. -/
def fullSymmetricFiveMarking
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (b : ActionEquiv ((fullMovedSection L).space.toRepresentation.comp
      (NormalizerReducedAction.componentImage L).subtype) (alternatingNatural 5))
    (hfull : let := reducedComponent_normal L
      Function.Surjective (fiveActor b.groupEquiv)) : SymmetricFiveRow T L := by
  let common := CommonMarking.of_source h hmany hL hn hmove
  let := reducedComponent_normal L
  let φ := fiveActor b.groupEquiv
  let f := φ.comp (NormalizerReducedAction.quotient L)
  let q := f.comp (inclusion common.ambient_invariant)
  have hf : Function.Surjective f :=
    hfull.comp (QuotientGroup.mk'_surjective _)
  have hcomp (l : L) : q (inclusion le_sup_left l) =
      (b.groupEquiv (reducedComponentMap L l)).val := by
    change φ (NormalizerReducedAction.quotient L
      (inclusion common.ambient_invariant (inclusion le_sup_left l))) = _
    have he : NormalizerReducedAction.quotient L
        (inclusion common.ambient_invariant (inclusion le_sup_left l)) =
        (reducedComponentMap L l).val := by
      change NormalizerReducedAction.quotient L _ = NormalizerReducedAction.componentMap L l
      rw [NormalizerReducedAction.componentMap_eq]
      rfl
    rw [he]
    exact fiveActor_component b.groupEquiv _
  have hc : (L.subgroupOf (L ⊔ (T : Subgroup G))).map q = alternatingGroup (Fin 5) := by
    apply le_antisymm
    · rintro _ ⟨l,hl,rfl⟩
      have he := hcomp ⟨l,hl⟩
      change q l ∈ alternatingGroup (Fin 5)
      rw [show q l = (b.groupEquiv (reducedComponentMap L ⟨l,hl⟩)).val from he]
      exact (b.groupEquiv _).property
    · intro p hp
      obtain ⟨l,hl⟩ := (b.groupEquiv.surjective.comp (reducedComponentMap_surjective L)) ⟨p,hp⟩
      exact ⟨inclusion le_sup_left l, l.property, (hcomp l).trans (congrArg Subtype.val hl)⟩
  have hTL : (T : Subgroup G) ≤ NormalizerReducedAction.Ambient L :=
    le_sup_right.trans common.ambient_invariant
  let P := (T.subtype hTL).mapSurjective (f := f) hf
  have hP : (P : Subgroup (Equiv.Perm (Fin 5))) ≤ q.range := by
    rintro p ⟨t,ht,rfl⟩
    exact ⟨⟨t, (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right) ht⟩, rfl⟩
  have hq : Function.Surjective q := MonoidHom.range_eq_top.mp
    (five_range_eq_top q.range (hc ▸ map_le_range q _) P hP)
  let e := (MulEquiv.multiplicativeAdditive (normalizerMoved L)).symm.trans
    (fullSectionCoordinates.trans b.linearEquiv).toAddEquiv.toMultiplicative
  refine ⟨common, ⟨common.invariant, q, hq, e, ?_, hc⟩⟩
  intro m v
  have he := fiveActor_equivariant (fullMovedSection L).space.toRepresentation b
    (NormalizerReducedAction.quotient L (inclusion common.ambient_invariant m))
    (fullSectionCoordinates (Additive.ofMul v))
  rw [← fullSectionCoordinates_equivariant] at he
  exact congrArg Multiplicative.ofAdd he

/-- The S5 product quotient constructs the original LT deleted-module row. -/
theorem twoFactors_symmetricFive_marked
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : SourceTwoFactorCase ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype))
    (hle : (NormalizerReducedAction.componentImage L).subgroupOf
      (offenderSubgroup (reducedRepresentation L)) ≤ d.first)
    (hm : d.firstSpace.toSubmodule = moved ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype) d.first)
    (a : ActionEquiv (((fixed ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)).quotientImage d.firstSpace).toRepresentation.comp
      d.first.subtype) (BinaryPermutation.naturalRepresentation (Fin 5))) :
    Nonempty (FourWayMarking.{u,u} T L) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).1
  have hj := componentImage_le_reducedOffender h hL hn hmove
  let C := (NormalizerReducedAction.componentImage L).subgroupOf
    (offenderSubgroup (reducedRepresentation L))
  let : (NormalizerReducedAction.componentImage L).Normal := reducedComponent_normal L
  let : C.Normal := inferInstance
  have hC := reducedOffender_component h hmany hL hn hmove
  let : IsQuasisimple C := hC.2
  let s := MovedSection.ofNormal ((reducedRepresentation L).comp
    (offenderSubgroup (reducedRepresentation L)).subtype) C
  let m := ProductMarkings.twoFactors_fiveAction d s hle hm a
    (ProductMarkings.five_component_map hC hle a.groupEquiv)
  let c := fullSectionSpaceEquiv hj s
  let k := (subgroupOfEquivOfLe hj).symm
  let b : ActionEquiv ((fullMovedSection L).space.toRepresentation.comp
      (NormalizerReducedAction.componentImage L).subtype) (alternatingNatural 5) := {
    groupEquiv := k.trans m.subgroupEquiv
    linearEquiv := c.trans m.action.linearEquiv
    intertwines := by
      intro g v
      have h1 := fullSectionSpaceEquiv_intertwines hj s (k g) v
      have h2 := (ExtensionConsequences.markedRestriction m).intertwines (k g) (c v)
      exact (congrArg m.action.linearEquiv h1).trans h2 }
  have hfull : Function.Surjective (fiveActor b.groupEquiv) := by
    intro p
    obtain ⟨g,rfl⟩ := m.action.groupEquiv.surjective p
    refine ⟨((g : offenderSubgroup (reducedRepresentation L)) : NormalizerReducedAction.Star L),?_⟩
    apply BinaryPermutation.naturalMulAction_injective_of_odd (Fin 5) (by decide)
    apply MulEquiv.ext
    intro v
    obtain ⟨w,hw⟩ := b.linearEquiv.surjective v.toAdd
    have he := fiveActor_equivariant (fullMovedSection L).space.toRepresentation b
      ((g : offenderSubgroup (reducedRepresentation L)) : NormalizerReducedAction.Star L) w
    have h1 := fullSectionSpaceEquiv_intertwines hj s g.val w
    have h2 := m.action.intertwines g (c w)
    have hh := he.symm.trans ((congrArg m.action.linearEquiv h1).trans h2)
    apply Multiplicative.toAdd.injective
    change BinaryPermutation.naturalRepresentation (Fin 5) (fiveActor b.groupEquiv g) v.toAdd =
      BinaryPermutation.naturalRepresentation (Fin 5) (m.action.groupEquiv g) v.toAdd
    change BinaryPermutation.naturalRepresentation (Fin 5) (fiveActor b.groupEquiv g)
      (b.linearEquiv w) = BinaryPermutation.naturalRepresentation (Fin 5)
        (m.action.groupEquiv g) (b.linearEquiv w) at hh
    simpa only [hw] using hh
  exact ⟨.symmetricFive (fullSymmetricFiveMarking h hmany hL hn hmove b hfull)⟩


end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
