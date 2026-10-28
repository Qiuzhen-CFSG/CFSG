module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ModuleLift
/-!
# Section centralizers fixing a noncentral part of a short module

The fixed sublayer is invariant under the short group by the three-subgroups
lemma. Short-module irreducibility makes it central or the entire moved
layer. A noncentral fixed sublayer therefore forces fixation of the whole
layer, and two-perfectness lifts this to the whole group.

This supplies the field-four application of C.1.10 in original15.3.18,
retaining the actual fixed subgroup instead of imposing an endomorphism-field
prime exclusion.
-/
public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- An actor fixing the core quotient and the short layer fixes the group. -/
theorem IsShort.centralizes_of_normalizing_coreQuotient_and_blockU
    (X Y : Subgroup G) (hX : IsShort X) (hY : IsPPerfect 2 Y)
    (hn : Y ≤ normalizer (X : Set G))
    (hcore : ⁅Y,X⁆ ≤ X.pCoreIn 2)
    (hU : Y ≤ centralizer ((blockU X).map X.subtype : Set G)) :
    Y ≤ centralizer (X : Set G) := by
  have hcomm : ⁅Y,X⁆ ≤ (blockU X).map X.subtype := by
    apply commutator_le.mpr
    intro y hy x hx
    let a : MulAut X := X.normalizerMonoidHom ⟨y,hn hy⟩
    have ha : ∀ z, a z * z⁻¹ ∈ pCore 2 X := by
      intro z
      obtain ⟨w,hw,he⟩ := hcore (commutator_mem_commutator hy z.property)
      have he' : w = a z * z⁻¹ := Subtype.ext he
      exact he' ▸ hw
    have he := DFunLike.congr_fun (hX.quotient_blockU_aut_eq_one a ha)
      (QuotientGroup.mk' (blockU X) ⟨x,hx⟩)
    rw [quotientAut_apply_mk] at he
    have hm : a ⟨x,hx⟩ * (⟨x,hx⟩ : X)⁻¹ ∈ blockU X := by
      simpa only [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem.mp he)
    exact mem_map.mpr ⟨_,hm,rfl⟩
  have hh := residual_centralizes_of_two_layer Y X ((blockU X).map X.subtype)
    ((pCore_isPGroup.to_le blockU_le_core).map X.subtype) hU hcomm
  simpa only [(pResidual_eq_top_iff 2 Y).mpr hY,
    ← MonoidHom.range_eq_map,range_subtype] using hh

/-- A noncentral fixed sublayer forces a two-perfect section-centralizer actor
of a short group to centralize the whole group. -/
theorem IsShort.centralizes_of_coreQuotient_and_noncentral_fixed
    (X Y E : Subgroup G) (hX : IsShort X) (hY : IsPPerfect 2 Y)
    (hn : Y ≤ normalizer (X : Set G))
    (hcore : ⁅Y,X⁆ ≤ X.pCoreIn 2)
    (hEU : E ≤ (blockU X).map X.subtype)
    (hEY : E ≤ centralizer (Y : Set G))
    (hne : ¬ E ≤ centralizer (X : Set G)) :
    Y ≤ centralizer (X : Set G) := by
  let U := (blockU X).map X.subtype
  let D := U ⊓ centralizer (Y : Set G)
  have hXU : X ≤ normalizer (U : Set G) :=
    X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (blockU X))
  have hcoreU : X.pCoreIn 2 ≤ centralizer (U : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    have hh := congrArg (map X.subtype)
      (commutator_eq_bot_iff_le_centralizer.mpr hX.core_centralizes_blockU)
    simpa only [pCoreIn,U,map_commutator,Subgroup.map_bot] using hh
  have hrot : ⁅⁅X,D⁆,Y⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate
    (by rw [commutator_eq_bot_iff_le_centralizer.mpr (show D ≤ centralizer (Y : Set G) from inf_le_right),commutator_bot_left])
    (commutator_eq_bot_iff_le_centralizer.mpr
      (hcore.trans (hcoreU.trans (centralizer_le (show D ≤ U from inf_le_left)))))
  have hXD : X ≤ normalizer (D : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact le_inf ((commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hXU))
      (commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm D X]))
  have hDX : D ≤ X := inf_le_left.trans (map_subtype_le _)
  let : (D.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer hXD
  have hDU : D.subgroupOf X ≤ blockU X := by
    intro x hx
    obtain ⟨u,hu,he⟩ := hx.1
    exact (Subtype.ext he : u=x) ▸ hu
  have hED : E ≤ D := le_inf hEU hEY
  have hDUeq : D = U := by
    rcases RankOne.ChiProduct.short_normal_layer_dichotomy hX (D.subgroupOf X) hDU with hc | he
    · exfalso
      apply hne
      intro e he x hx
      exact congrArg Subtype.val
        (mem_center_iff.mp (hc (show (⟨e,hDX (hED he)⟩ : X) ∈ D.subgroupOf X from hED he)) ⟨x,hx⟩)
    · have hm := congrArg (map X.subtype) he
      simpa only [map_subgroupOf_eq_of_le hDX] using hm
  apply hX.centralizes_of_normalizing_coreQuotient_and_blockU X Y hY hn hcore
  exact le_centralizer_iff.mp (hDUeq.ge.trans (show D ≤ centralizer (Y : Set G) from inf_le_right))
end CFSG.Quasithin.ChapterC
