module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Quotient
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PPerfectCentralLift

/-!
# Centralizers of the elementary block layer

Self-centralization of F*(X) and the two-layer fixer theorem give
C_X(U(X)) = O₂(X). For C.1.10, an automorphism fixing X/O₂(X) also fixes
X/U(X), by uniqueness of lifts from two-perfect groups through a central
two-group kernel. A two-perfect actor fixing both U(X) and X/U(X) then
fixes X. The Schur-field argument supplying fixation of U(X) remains a
separate obligation.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
C.1.10--11, printed p.124.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement

namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L]

/-- The core commutator has a two-group centralizer whenever F* is the two-core.
This version does not require the other short-group axioms. -/
theorem centralizer_blockU_le_of_fitting [Finite L] (hf : generalizedFitting L = pCore 2 L) :
    centralizer (blockU L : Set L) ≤ pCore 2 L := by
  have hc : centralizer (pCore 2 L : Set L) ≤ pCore 2 L := by
    rw [← hf]
    exact centralizer_generalizedFitting_le L
  have ht := two_layer_le_radical (pCore 2 L) (blockU L) (pCore 2 L)
    (pCore_isPGroup.to_le blockU_le_core)
    (pCore_quotient_pCore_eq_bot (p := 2)) (inf_le_right.trans hc)
  apply le_trans (le_inf le_rfl ?_) ht
  apply le_commutatorPreimage le_top
  exact (commutator_mono le_top le_rfl).trans_eq (commutator_comm _ _)

/-- The elementary layer of a short group has exactly its two-core as centralizer. -/
theorem IsShort.centralizer_blockU (h : IsShort L) :
    centralizer (blockU L : Set L) = pCore 2 L := by
  let := h.finite
  exact le_antisymm (centralizer_blockU_le_of_fitting h.fitting) h.core_centralizes_blockU

/-- An automorphism trivial on X/O₂(X) is already trivial on X/U(X). -/
theorem IsShort.quotient_blockU_aut_eq_one (h : IsShort L) (a : MulAut L)
    (ha : ∀ x, a x * x⁻¹ ∈ pCore 2 L) :
    quotientAut (blockU L) a = 1 := by
  let f := blockCoreProjection (L := L)
  have hc : f.ker ≤ center (L ⧸ blockU L) := by
    rw [blockCoreProjection_ker]
    exact blockU_core_image_le_center
  have hp : IsPGroup 2 f.ker := by
    rw [blockCoreProjection_ker]
    exact pCore_isPGroup.map _
  have he : f.comp (quotientAut (blockU L) a).toMonoidHom = f.comp (MonoidHom.id _) := by
    apply MonoidHom.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (blockU L) q
    change f (quotientAut (blockU L) a (QuotientGroup.mk' (blockU L) x)) =
      f (QuotientGroup.mk' (blockU L) x)
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (pCore 2 L) (a x) = QuotientGroup.mk' (pCore 2 L) x
    exact QuotientGroup.eq_iff_div_mem.mpr (by simpa only [div_eq_mul_inv] using ha x)
  have hh := IsPPerfect.hom_eq_of_comp_eq_of_central_pGroup_kernel (h.quotient_twoPerfect (blockU L)) f hc hp _ _ he
  apply MulEquiv.ext
  intro q
  exact DFunLike.congr_fun hh q

variable {H : Type*} [Group H] [Finite H]

/-- The final group-theoretic step of C.1.10. Its remaining action premise
is pointwise fixation of U(X), which must be supplied by the endomorphism
field argument. The source theorem is not claimed by this conditional result. -/
theorem IsShort.centralizes_of_coreQuotient_and_blockU (X Y : Subgroup H) [X.Normal]
    (hX : IsShort X) (hY : IsPPerfect 2 Y)
    (hcore : ⁅Y, X⁆ ≤ (pCore 2 X).map X.subtype)
    (hU : Y ≤ centralizer ((blockU X).map X.subtype : Set H)) :
    Y ≤ centralizer (X : Set H) := by
  have hcomm : ⁅Y, X⁆ ≤ (blockU X).map X.subtype := by
    apply commutator_le.mpr
    intro y hy x hx
    let a : MulAut X := MulAut.conjNormal y
    have ha : ∀ z, a z * z⁻¹ ∈ pCore 2 X := by
      intro z
      have hz := hcore (commutator_mem_commutator hy z.property)
      obtain ⟨w, hw, he⟩ := hz
      have he' : w = a z * z⁻¹ := Subtype.ext he
      exact he' ▸ hw
    have he := DFunLike.congr_fun (hX.quotient_blockU_aut_eq_one a ha)
      (QuotientGroup.mk' (blockU X) ⟨x, hx⟩)
    rw [quotientAut_apply_mk] at he
    have hm : a ⟨x, hx⟩ * (⟨x, hx⟩ : X)⁻¹ ∈ blockU X := by
      simpa only [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem.mp he)
    exact mem_map.mpr ⟨_, hm, rfl⟩
  have hh := residual_centralizes_of_two_layer Y X ((blockU X).map X.subtype)
    ((pCore_isPGroup.to_le blockU_le_core).map X.subtype) hU hcomm
  simpa only [(pResidual_eq_top_iff 2 Y).mpr hY,
    ← MonoidHom.range_eq_map, range_subtype] using hh
end CFSG.Quasithin.ChapterC
