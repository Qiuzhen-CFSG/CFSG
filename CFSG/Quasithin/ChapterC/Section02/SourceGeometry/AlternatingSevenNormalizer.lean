module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.MovedNormalizerAction
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.CoreStarNormalizerAction
public import Theory.Representation.BinaryAlternatingSevenControl.InnerIntertwiner

/-!
# Normalizer actions on an exceptional A₇ moved section

For the actual four-dimensional A₇ moved section, every simultaneous
normalizer of the component and radical induces an inner automorphism.
The induced linear intertwiner normalizes A₇ in GL₄(2), where A₇ is
self-normalizing. Equivariance of the original perfect central cover
then gives innerness on the full component core quotient as well.

Source: Aschbacher--Smith C.1.23(2), C.2.7 and the exceptional A₇ row
in 15.2.23, printed pp.130,145--147,1116--1117.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {I X R N : Subgroup G}

/-- Innerness on the literal core quotient, including any central covering kernel. -/
theorem alternatingSeven_four_normalizer_inner
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (hCJ : starImage X R X ≤ offenderSubgroup (starRepresentation X R))
    (s : MovedSection ((starRepresentation X R).comp (offenderSubgroup (starRepresentation X R)).subtype)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))))
    (hf : Function.Injective s.action)
    (e : ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))) ≃*
      alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4)
    (a : G) (hX : a ∈ normalizer (X : Set G)) (hR : a ∈ normalizer (R : Set G)) :
    pCoreNormalizerAction 2 X ⟨a,hX⟩ ∈ MulAut.innerSubgroup (X ⧸ pCore 2 X) := by
  let L := (starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))
  let : Group L := inferInstance
  let σ := (s.action.comp L.subtype).comp e.symm.toMonoidHom
  let β : MulAut L := (subgroupOfEquivOfLe hCJ).trans
    ((starComponentAut X R a hX hR).trans (subgroupOfEquivOfLe hCJ).symm)
  let v := starVectorAut X R a hX hR
  have hv : ∀ l : L, ∀ w, v (((starRepresentation X R).comp
      (offenderSubgroup (starRepresentation X R)).subtype) l w) =
      ((starRepresentation X R).comp (offenderSubgroup (starRepresentation X R)).subtype)
        (β l) (v w) := by
    intro l w
    have hh := starNormalizerAut_intertwines X R a hX hR l.val.val w
    have hc := starComponentAut_coe X R a hX hR (subgroupOfEquivOfLe hCJ l)
    change (starComponentAut X R a hX hR (subgroupOfEquivOfLe hCJ l) : StarQuotient X R) =
      starNormalizerAut X R a hX hR l.val.val at hc
    change v (starRepresentation X R l.val.val w) =
      starRepresentation X R (starComponentAut X R a hX hR (subgroupOfEquivOfLe hCJ l)) (v w)
    rw [hc]
    exact hh
  let E := s.twistedActionEquiv β v hv
  let α : MulAut (alternatingGroup (Fin 7)) := e.symm.trans (β.trans e)
  have he : ∀ g w, E.linearEquiv (σ g w) = σ (α g) (E.linearEquiv w) := by
    intro g w
    simpa only [σ,α,E, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, e.symm_apply_apply] using
      s.twistedActionEquiv_intertwines β v hv (e.symm g) w
  have hσ : Function.Injective σ := hf.comp (Subtype.val_injective.comp e.symm.injective)
  obtain ⟨g,hg⟩ := BinaryAlternatingSevenControl.inner_of_intertwiner σ hσ hd α E.linearEquiv he
  have hb (l : L) : β l = e.symm g * l * (e.symm g)⁻¹ := by
    apply e.injective
    have hh := DFunLike.congr_fun hg (e l)
    change e (β (e.symm (e l))) = g * e l * g⁻¹ at hh
    rw [e.symm_apply_apply] at hh
    rw [e.map_mul, e.map_mul, e.map_inv, e.apply_symm_apply]
    exact hh
  have hstar : starComponentAction X R ⟨a,by exact ⟨hX,hR⟩⟩ ∈
      MulAut.innerSubgroup (starImage X R X) := by
    let η := subgroupOfEquivOfLe hCJ
    let z := η (e.symm g)
    refine ⟨z,?_⟩
    apply MulEquiv.ext
    intro y
    rw [MulAut.conj_apply, starComponentAction_apply]
    have hh := congrArg η (hb (η.symm y))
    change η (η.symm (starComponentAut X R a hX hR (η (η.symm y)))) =
      η (e.symm g * η.symm y * (e.symm g)⁻¹) at hh
    rw [η.apply_symm_apply, η.apply_symm_apply, η.map_mul, η.map_mul,
      η.map_inv, η.apply_symm_apply] at hh
    exact hh.symm
  exact (starComponentAction_inner_iff h ⟨a,by exact ⟨hX,hR⟩⟩).mp hstar

end CFSG.Quasithin.ChapterC.C27Source
