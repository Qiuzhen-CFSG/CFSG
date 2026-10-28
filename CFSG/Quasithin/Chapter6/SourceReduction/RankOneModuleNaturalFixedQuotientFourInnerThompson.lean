module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourOriginal
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson

/-!
# The first Thompson subgroup of the original inner Sylow preimage

For S=(T∩L)O₂(LT), every near-maximum elementary subgroup has image in the
inner Hermitian component. Its near-offender codimension contradicts the
inner bound when s>1. Thus J₁(S) centralizes the actual original module,
including the orthogonal half-degree-two case.

Source: Aschbacher--Smith 6.1.4, printed p.665, using B.2.4 and H.1.1.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n s : ℕ} [NeZero s]
local instance innerThompsonFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance innerThompsonBinaryModule : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The exact inner Sylow preimage has first Thompson subgroup centralizing
the original Hermitian module at every half-degree greater than one. -/
theorem Input.hermitian_inner_thompson_one_centralizes
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hm : IsConjugationModel L W (SL2.BinarySmall.hermitian s)) (hs : 1 < s) :
    ChapterB.thompsonJ (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) 1 ≤
      centralizer (W : Set G) := by
  let J := L ⊔ (T : Subgroup G)
  let U := W.subgroupOf J
  let S := ((T : Subgroup G) ⊓ L) ⊔ J.pCoreIn 2
  let S0 := S.subgroupOf J
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let q := QuotientGroup.mk' (pCore 2 J)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker = centralizer (U : Set J) :=
    (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_core.symm
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let Bq := (L.subgroupOf J).map q
  have hSJ : S ≤ J := sup_le (inf_le_right.trans le_sup_left) (pCoreIn_le 2 J)
  have hQ0 : (J.pCoreIn 2).subgroupOf J = pCore 2 J :=
    comap_map_eq_self_of_injective J.subtype_injective _
  have hUS : U ≤ S0 := by
    intro u hu
    exact mem_sup_right (mem_map_of_mem J.subtype (h.reduced_internal.le_pCore hu))
  have hSinner : S0.map q ≤ Bq := by
    change (S.subgroupOf J).map q ≤ _
    rw [show S = ((T : Subgroup G) ⊓ L) ⊔ J.pCoreIn 2 from rfl,
      subgroupOf_sup (inf_le_right.trans (show L ≤ J from le_sup_left)) (pCoreIn_le 2 J),
      Subgroup.map_sup,hQ0,QuotientGroup.map_mk'_self,sup_bot_eq]
    exact map_mono (subgroupOf_mono _ inf_le_right)
  obtain ⟨hsource,⟨model⟩⟩ := h.hermitian_original_source hm
  apply sSup_le
  intro A hA
  by_contra hmove
  let A0 := A.subgroupOf J
  let Aq := A0.map q
  have hAJ : A ≤ J := hA.1.trans hSJ
  have hAf : A0 ∈ ChapterB.thompsonFamily S0 1 := by
    apply (ChapterB.thompsonFamily_map_iff_of_injective J.subtype J.subtype_injective
      S0 A0 1).mp
    rwa [map_subgroupOf_eq_of_le hAJ,map_subgroupOf_eq_of_le hSJ]
  have hne : Aq ≠ ⊥ := by
    intro hz
    have hc : A0 ≤ centralizer (U : Set J) := hk ▸ (map_eq_bot_iff A0).mp hz
    apply hmove
    intro a ha w hw
    exact congrArg J.subtype (hc (show (⟨a,hAJ ha⟩ : J) ∈ A0 from ha)
      ⟨w,h.reduced.1 hw⟩ hw)
  let : IsElementaryAbelian 2 A0 := hAf.2.1
  have hEA : IsElementaryTwo Aq := ⟨hne,IsElementaryAbelian.map q⟩
  have hnear := ChapterB.near_maximum_action_codimension S0 U hUS q hq hk hAf hne
  have hout := (FourOffender.marked_near_offender_cases hsource model hs Aq hEA hnear).2.1
  exact hout ((map_mono (subgroupOf_mono _ hA.1)).trans hSinner)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
