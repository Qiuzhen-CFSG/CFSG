module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.MSRestriction
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The genuine symplectic MS inputs from the A₆ star image

A marking of the actual C.2.7 star component by A₆ identifies the kernel
of K/O₂(K) → A₆ with its center. Thus K/O₂,Z(K), rather than necessarily
K/O₂(K), is A₆. The equivalence retains the literal star quotient map.

With the independently supplied odd-index radical, all three conditions
of C.1.31 now hold on KR. The component has the actual central quotient
Sp₄(2)′, the product is characteristic two, and MS2(a) and MS3 hold for
the original R. No natural-module or whole-core reconstruction is assumed
or concluded. The remaining A₆ block assertion is the symplectic branch
of C.1.32, not a consequence of a constituent marking alone.

Source: Aschbacher--Smith C.1.31--32, pp.135--136, and the final paragraph
of the proof of C.2.7, pp.146--147; MS93 Main Theorem case (2).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC

namespace AlternatingSixMS
universe u
variable {J : Type u} [Group J]

/-- The A₆ specialization of C.1.31, allowing its genuine central cover. -/
structure Input (κ : GroupClass.{u}) (L R : Subgroup J) where
  sqtk : IsSQTK κ J
  fitting : generalizedFitting J = pCore 2 J
  product : ∀ j : J, ∃ l ∈ L, ∃ r ∈ R, l * r = j
  component : L.IsCComponent
  radical : MSOddIndexRadical R
  characteristic : MSCharacteristicCondition R
  quotientEquiv : (L ⧸ centralPreimage (pCore 2 L)) ≃* alternatingGroup (Fin 6)

/-- The quotient in MS1 is literally the derived group of the binary
projective symplectic group, with its quotient taken before the commutator. -/
noncomputable def Input.derivedQuotientEquiv {κ : GroupClass.{u}} {L R : Subgroup J}
    (h : Input κ L R) :
    (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2) ⧸
        center (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :=
  h.quotientEquiv.trans
    Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix.symm
end AlternatingSixMS

namespace C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G]
variable {κ : GroupClass} {H K R M : Subgroup G}

/-- The A₆ map is the original map through the literal star quotient. -/
noncomputable def source_a6_quotientMap (h : Input κ H R M K)
    (e : starImage K R K ≃* alternatingGroup (Fin 6)) :
    (K ⧸ pCore 2 K) →* alternatingGroup (Fin 6) :=
  e.toMonoidHom.comp (coreToStar h.normalizes)

/-- A quasisimple source and the centerless A₆ target identify the exact
comparison kernel. This does not assert that the source center is trivial. -/
theorem source_a6_quotientMap_ker (h : Input κ H R M K)
    (e : starImage K R K ≃* alternatingGroup (Fin 6)) :
    (source_a6_quotientMap h e).ker = center (K ⧸ pCore 2 K) := by
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  have hc := IsQuasisimple.comap_center_of_surjective (source_a6_quotientMap h e)
    (e.surjective.comp (coreToStar_surjective h.normalizes))
  rw [alternatingGroup.center_eq_bot (by simp)] at hc
  exact hc

/-- The central quotient identified through the actual star map. -/
noncomputable def source_a6_centralQuotientEquiv (h : Input κ H R M K)
    (e : starImage K R K ≃* alternatingGroup (Fin 6)) :
    ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* alternatingGroup (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq (source_a6_quotientMap_ker h e).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (source_a6_quotientMap h e)
      (e.surjective.comp (coreToStar_surjective h.normalizes)))

/-- Compatibility retains the specified star marking on each original element. -/
theorem source_a6_centralQuotientEquiv_mk (h : Input κ H R M K)
    (e : starImage K R K ≃* alternatingGroup (Fin 6)) (x : K ⧸ pCore 2 K) :
    source_a6_centralQuotientEquiv h e (QuotientGroup.mk' (center (K ⧸ pCore 2 K)) x) =
      e (coreToStar h.normalizes x) := by rfl

/-- The precise single quotient L/O₂,Z(L) in MS1. -/
noncomputable def source_a6_coreCenterQuotientEquiv (h : Input κ H R M K)
    (e : starImage K R K ≃* alternatingGroup (Fin 6)) :
    (K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6) :=
  (centralPreimageQuotientEquiv (pCore 2 K)).trans (source_a6_centralQuotientEquiv h e)

private noncomputable def centerQuotientCongr {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : (A ⧸ center A) ≃* (B ⧸ center B) := by
  apply QuotientGroup.congr _ _ e
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (centerCongr e ⟨y,hy⟩).property
  · intro hx
    exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩

variable [Finite G]

/-- All original MS hypotheses, on the same KR and R as C.2.7.
The extra premise is exactly the odd-index witness supplied by 14.6.10(5). -/
noncomputable def alternatingSixMSInput_from_source (h : Input κ H R M K)
    (hr : MSOddIndexRadical (R.subgroupOf H))
    (e : starImage K R K ≃* alternatingGroup (Fin 6)) :
    AlternatingSixMS.Input κ (K.subgroupOf (K ⊔ R)) (R.subgroupOf (K ⊔ R)) := by
  let J := K ⊔ R
  let L := K.subgroupOf J
  let : L.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  let eL : L ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let eQ := QuotientGroup.congr (pCore 2 L) (pCore 2 K) eL (pCore_map_iso 2 eL)
  refine {
    sqtk := (source_join_input h).setup.sqtk
    fitting := source_join_fitting h
    product := ?_
    component := (source_join_input h).component.2
    radical := msOddIndexRadical_join_from_source h hr
    characteristic := join_msCharacteristic_from_source h
    quotientEquiv := (centralPreimageQuotientEquiv (pCore 2 L)).trans
      ((centerQuotientCongr eQ).trans (source_a6_centralQuotientEquiv h e)) }
  intro j
  have hg : L ⊔ R.subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  exact mem_sup_of_normal_left.mp (hg.ge (mem_top j))

/-- The existential source consumer needs no choice of an A₆ marking in its input. -/
theorem alternatingSixMSInput_nonempty_from_source (h : Input κ H R M K)
    (hr : MSOddIndexRadical (R.subgroupOf H))
    (he : Nonempty (starImage K R K ≃* alternatingGroup (Fin 6))) :
    Nonempty (AlternatingSixMS.Input κ
      (K.subgroupOf (K ⊔ R)) (R.subgroupOf (K ⊔ R))) := by
  obtain ⟨e⟩ := he
  exact ⟨alternatingSixMSInput_from_source h hr e⟩
end C27Source
end CFSG.Quasithin.ChapterC
