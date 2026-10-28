module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.TwoFactorMarking
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.ChiefFactorBound
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.ExceptionalSplitting.Source
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.ActionTransport

/-!
# The exceptional product row on the original moved subgroup

The given upper four-space is first identified with its literal quotient by
fixed vectors. Its central extension has a unique natural noncentral chief
factor. The genuine B.4.8(4) dimension bound and bounded splitting construct
an invariant complement inside the original upper space. The quotient map
then identifies its moved space with the natural three-space.

The selected component equals the SL3(2) factor. Transport to the original
moved subgroup constructs source case (3), with one natural copy. No extension
splitting or dimension assertion remains an extra source hypothesis.

Source: Aschbacher--Smith 13.1.10, pp.871--872; B.5.6(3c), p.105;
B.4.8(3)--(4), pp.91--92.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
namespace ProductMarkings
open ExceptionalExtension.Nonsplit.ExceptionalSplitting
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

def upperRestriction (U : Subrepresentation ρ) (A : Subgroup D) :
    Subrepresentation (ρ.comp A.subtype) where
  toSubmodule := U.toSubmodule
  apply_mem_toSubmodule g _v hv := U.apply_mem_toSubmodule g hv

@[expose] def imageProjection (U : Subrepresentation ρ) :
    U.toSubmodule →ₗ[ZMod 2] ((fixed ρ).quotientImage U).toSubmodule where
  toFun v := ⟨ρ.invariants.mkQ v, ⟨v,v.property,rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem imageProjection_surjective (U : Subrepresentation ρ) :
    Function.Surjective (imageProjection U) := by
  rintro ⟨q,v,hv,rfl⟩
  exact ⟨⟨v,hv⟩,rfl⟩

def upperReducedEquiv (U : Subrepresentation ρ) (A : Subgroup D)
    (hz : Representation.invariants (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) = ⊥) :
    ActionEquiv (reducedAction (upperRestriction U A).toRepresentation)
      (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) := by
  let p := imageProjection U
  have hk : (upperRestriction U A).toRepresentation.invariants = p.ker := by
    ext v
    constructor
    · intro hv
      have hh : p v ∈ Representation.invariants (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) := by
        intro g
        exact congrArg p (hv g)
      rw [hz] at hh
      exact hh
    · intro hv g
      apply Subtype.ext
      have hh : (v : V) ∈ ρ.invariants :=
        (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hv)
      exact hh g
  let f := (upperRestriction U A).toRepresentation.invariants.liftQ p hk.le
  have hf : Function.Bijective f := by
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      intro v hv
      induction v using Submodule.Quotient.induction_on with
      | _ v => exact (Submodule.Quotient.mk_eq_zero _).mpr (hk.symm ▸ hv)
    · intro v
      obtain ⟨w,rfl⟩ := imageProjection_surjective U v
      exact ⟨Submodule.Quotient.mk w,rfl⟩
  refine ⟨MulEquiv.refl _,LinearEquiv.ofBijective f hf,?_⟩
  intro g v
  induction v using Submodule.Quotient.induction_on with | _ v => rfl

/-- An invariant complement inside the original upper space has the very
same fixed quotient, with its original action. -/
def complementUpperEquiv {σ : Representation (ZMod 2) D V}
    (R S : Subrepresentation σ) (hSR : S ≤ R)
    (hc : IsCompl S.toSubmodule σ.invariants) :
    ActionEquiv S.toRepresentation (reducedAction R.toRepresentation) := by
  let f : S.toSubmodule →ₗ[ZMod 2] (R.toSubmodule ⧸ R.toRepresentation.invariants) :=
    R.toRepresentation.invariants.mkQ.comp (Submodule.inclusion hSR)
  have hf : Function.Bijective f := by
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      intro v hv
      have hh : (Submodule.inclusion hSR v) ∈ R.toRepresentation.invariants :=
        (Submodule.Quotient.mk_eq_zero _).mp hv
      apply Subtype.ext
      exact hc.disjoint.le_bot ⟨v.property, fun g => congrArg Subtype.val (hh g)⟩
    · intro q
      induction q using Submodule.Quotient.induction_on with
      | _ v =>
        obtain ⟨s,hs,c,hc',he⟩ := Submodule.mem_sup.mp
          (hc.sup_eq_top.symm ▸ Submodule.mem_top (x := (v : V)))
        refine ⟨⟨s,hs⟩,?_⟩
        apply (Submodule.Quotient.eq _).mpr
        intro g
        apply Subtype.ext
        change σ g (s - (v : V)) = s - (v : V)
        rw [← he]
        simpa only [sub_add_cancel_left, map_neg] using congrArg Neg.neg (hc' g)
  exact ⟨MulEquiv.refl _,LinearEquiv.ofBijective f hf,fun _ _ => rfl⟩

theorem moved_map_of_complement {σ : Representation (ZMod 2) D V}
    (S : Subrepresentation σ) (hs : S.toSubmodule ⊔ σ.invariants = ⊤) :
    (moved S.toRepresentation ⊤).map S.toSubmodule.subtype = moved σ ⊤ := by
  have he := subspaceCommutator_map_embedding σ S.toRepresentation (MonoidHom.id D)
    S.toSubmodule.subtype (fun _ _ => rfl) ⊤ ⊤
  simp only [Submodule.map_top,Submodule.range_subtype,Subgroup.map_id] at he
  rw [← he]
  apply le_antisymm (subspaceCommutator_mono_left σ le_top ⊤)
  apply Submodule.span_le.mpr
  rintro _ ⟨g,_,v,_,rfl⟩
  obtain ⟨s,hs',c,hc,rfl⟩ := Submodule.mem_sup.mp (hs.symm ▸ Submodule.mem_top (x := v))
  rw [map_add,hc g,add_sub_add_right_eq_sub]
  exact Submodule.subset_span ⟨g,Subgroup.mem_top _,s,hs',rfl⟩

/-- B.4.8(4) splits the central attachment to an upper four-space. Its
literal moved space is therefore the natural three-space. -/
theorem centralFour_moved_dimension [Finite D] [FiniteDimensional (ZMod 2) V]
    (s : CentralFourSection ρ) : Module.finrank (ZMod 2) (moved ρ ⊤) = 3 := by
  have hb := smallConstituents_of_applicability
    ChapterB.NaturalExtensions.ChiefFactorBound.earlierB48Four s s.constituentApplicability
  obtain ⟨S,hS,hc⟩ := bounded_complement s s.uniqueNoncentralNaturalFactor hb
  let e := complementUpperEquiv s.upper S hS hc
  have hm : (moved S.toRepresentation ⊤).map e.linearEquiv.toLinearMap =
      s.quotientSource.space.toSubmodule := by
    have hh := subspaceCommutator_map_embedding
      (reducedAction s.upper.toRepresentation) S.toRepresentation e.groupEquiv.symm.toMonoidHom
      e.linearEquiv.toLinearMap (fun g v => by
        simpa using (e.intertwines (e.groupEquiv.symm g) v).symm) ⊤ ⊤
    simpa only [Submodule.map_top,LinearEquiv.range,
      Subgroup.map_top_of_surjective e.groupEquiv.symm.toMonoidHom e.groupEquiv.symm.surjective,
      ← s.quotientSource.space_eq] using hh.symm
  have hd : Module.finrank (ZMod 2) (moved S.toRepresentation ⊤) = 3 := by
    rw [← LinearEquiv.finrank_map_eq e.linearEquiv,hm]
    exact s.quotientSource.natural.linearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2))
  rw [← moved_map_of_complement S hc.sup_eq_top]
  exact (Submodule.equivMapOfInjective S.toSubmodule.subtype
    S.toSubmodule.subtype_injective (moved S.toRepresentation ⊤)).finrank_eq.symm.trans hd

/-- The exceptional factor's original moved space has dimension three. -/
theorem exceptional_moved_dimension [Finite D] [FiniteDimensional (ZMod 2) V]
    (A : Subgroup D) (U : Subrepresentation ρ) (hm : moved ρ A ≤ U.toSubmodule)
    (q : FourDimensionalSource (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype)) :
    Module.finrank (ZMod 2) (moved ρ A) = 3 := by
  let e := upperReducedEquiv U A (four_source_invariants q)
  obtain ⟨q'⟩ := FittingReduction.fourDimensional_transport e q
  let s : CentralFourSection (ρ.comp A.subtype) :=
    ⟨upperRestriction U A,q',by
      change moved (ρ.comp A.subtype) ⊤ ≤ U.toSubmodule
      rw [moved_comp_map,← MonoidHom.range_eq_map,A.range_subtype]
      exact hm⟩
  have hd := centralFour_moved_dimension s
  change Module.finrank (ZMod 2) (moved (ρ.comp A.subtype) ⊤) = 3 at hd
  rwa [moved_comp_map,← MonoidHom.range_eq_map,A.range_subtype] at hd

end ProductMarkings
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The exceptional upper-four-space product row has a natural moved
three-space on the original component, so gives source case (3). -/
theorem twoFactors_exceptional_marked
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : SourceTwoFactorCase ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype))
    (hle : (NormalizerReducedAction.componentImage L).subgroupOf
      (offenderSubgroup (reducedRepresentation L)) ≤ d.first)
    (hm : moved ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype) d.first ≤ d.firstSpace.toSubmodule)
    (q : FourDimensionalSource (((fixed ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)).quotientImage d.firstSpace).toRepresentation.comp
      d.first.subtype)) : Nonempty (FourWayMarking.{u,u} T L) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).1
  let C := (NormalizerReducedAction.componentImage L).subgroupOf
    (offenderSubgroup (reducedRepresentation L))
  let : (NormalizerReducedAction.componentImage L).Normal := reducedComponent_normal L
  let : C.Normal := inferInstance
  have hC := reducedOffender_component h hmany hL hn hmove
  have hCA := ProductMarkings.component_eq_binaryThree hC hle q.natural.groupEquiv
  let s := MovedSection.ofNormal ((reducedRepresentation L).comp
    (offenderSubgroup (reducedRepresentation L)).subtype) C
  have hd : Module.finrank (ZMod 2) (moved ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype) C) = 3 := by
    rw [show C = d.first from hCA]
    exact ProductMarkings.exceptional_moved_dimension d.first d.firstSpace hm q
  let e := (MulEquiv.subgroupCongr hCA).trans q.natural.groupEquiv
  let b := ProductMarkings.threeMovedEquiv s e hd
  exact ⟨.linearThree (repeatedThreeMarking h hmany hL hn hmove s (by decide : 1 ≤ 2)
    (composeAction b (ProductMarkings.oneCopy _)))⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
