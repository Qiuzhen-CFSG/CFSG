module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSevenExceptional

/-! The actual A7 normalizer image reconstructs the ordinary whole block on
its original component. This reconstruction then proves that the original
core comparison is injective; its possible cubic kernel is not discarded
before reconstruction. The original quotient marking is retained pointwise. -/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal normalizer A7 row is an ordinary whole block, with a pointwise
compatible isomorphism on the full original two-core quotient. -/
theorem PreparedChosenModule.raw_seven_ordinary_marked
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (houtM : ¬L ≤ M)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let R := S ⊓ normalizer (L : Set G)
    let H := L ⊔ R
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let q := QuotientGroup.mk' (centralizer (W : Set H))
    ∀ e : (L.subgroupOf H).map q ≃* alternatingGroup (Fin 7),
      IsAlternatingBlock L 7 ∧
        ∃ t : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7),
          ∀ l : L, (e.symm (t (QuotientGroup.mk' (pCore 2 L) l)) :
            H ⧸ centralizer (W : Set H)) = q (inclusion le_sup_left l) := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (L : Set G)
  let H := L ⊔ R
  let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let I := (L.subgroupOf H).map q
  change ∀ e : I ≃* alternatingGroup (Fin 7), IsAlternatingBlock L 7 ∧ _
  intro e
  have hb := (h.raw_seven_blocks_of_normalizer_image hG T hM hJ hu hZ hZne hL
    hi.quasisimple hi.fitting hi.outside houtM e).resolve_right
      (h.raw_not_exceptional_seven hG T hM hJ hu hZ hZne hL houtM hs hi)
  obtain ⟨f,ec,hf,hcf,_,hec,hker,_⟩ := h.raw_component_normalizer_quotient
    hG T hM hJ hu hZ hZne hL hi.quasisimple hi.fitting hi.outside houtM
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    obtain ⟨_,⟨m⟩,_⟩ := hb.2.2
    let t := m.quotientIso
    apply bot_unique
    intro x hx
    have hh : t x ∈ center (alternatingGroup (Fin 7)) := (centerCongr t ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp)] at hh
    exact t.injective (by simpa using hh)
  have hinj : Function.Injective ec := (MonoidHom.ker_eq_bot_iff ec).mp
    (bot_unique (hker.trans_eq hz))
  let t := (MulEquiv.ofBijective ec ⟨hinj,hec⟩).trans e
  refine ⟨hb,t,?_⟩
  intro l
  change (e.symm (e (ec (QuotientGroup.mk' (pCore 2 L) l))) : H ⧸ C) = _
  rw [e.symm_apply_apply,hcf]
  exact hf l

end CFSG.Quasithin.Chapter15.Section01
