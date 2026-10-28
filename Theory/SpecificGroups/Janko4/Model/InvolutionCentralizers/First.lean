module

public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Action
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.PlusType
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension

/-!
# The first involution centralizer in the literal J₄ carrier

For C = C_J₄(a), the intrinsic two-core Q is the embedded extraspecial group
of plus type and order 2¹³. Six actual dihedral factors identify Q with the
explicit central product D₈⁶, with each factor's central involution mapping
to a. Its self-centralizing property excludes all ordinary components of C.

The actual conjugation action on Q/Z(Q) identifies the full quotient C/Q
with the certified matrix group 3.M₂₂.2. We assemble both short exact sequences
here, preserving the core embedding, the genuine triple-cover inclusion and
the marked outer action by inversion on its center of order three. The
re-exported `QuotientExtension` normal series Q ≤ R ≤ H ≤ C supplies the
actual sections R/Q ≃ C₃, H/R ≃ M₂₂, H/Q ≃ 3.M₂₂, C/H ≃ C₂ and
C/R ≃ Aut(M₂₂), including relative normality and the quotient maps.

This proves the marked first-centralizer row of Aschbacher–Smith 16.1.5(9),
printed p.1172, and its component exclusion used in 16.1.7, pp.1172–1173.
GLS3 Table 5.3i makes the covering extension 3.M₂₂.2 explicit: the source's
shorthand Aut(M̂₂₂) retains the three-element kernel. No splitting of the
extension over Q is asserted. Involution-class coverage and automorphism
innerness, needed for the other assertions of 16.1.5–6, belong to their
separate assembly owners.
-/

public section

namespace Janko4.InvolutionCentralizers.First

open Subgroup Theory.GroupTheory
open OuterReduction.FixedGenerator.NormalizerSquares
open PlusType QuotientExtension Sporadic.Mathieu

/-- The full first centralizer is an extension of its actual matrix action
group by the explicit central product of six dihedral groups of order eight. -/
noncomputable def plusCentralizerExtension :
    GroupExtension DihedralCentralProductSix.Model centralizer
      TwoCoreLinearModel.actionGroup where
  inl := centralizerExtension.inl.comp literalCorePlusEquiv.toMonoidHom
  rightHom := centralizerExtension.rightHom
  inl_injective := centralizerExtension.inl_injective.comp literalCorePlusEquiv.injective
  range_inl_eq_ker_rightHom := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr literalCorePlusEquiv.surjective,
      ← MonoidHom.range_eq_map]
    exact centralizerExtension.range_inl_eq_ker_rightHom
  rightHom_surjective := centralizerExtension.rightHom_surjective

/-- The kernel model is included through the proved isomorphism with O₂(C). -/
theorem plusCentralizerExtension_inl (q : DihedralCentralProductSix.Model) :
    plusCentralizerExtension.inl q = (literalCorePlusEquiv q : centralizer) :=
  centralizerExtension_inl _

/-- The image of this explicit central product is precisely the intrinsic two-core. -/
theorem plusCentralizerExtension_inl_range :
    plusCentralizerExtension.inl.range = pCore 2 centralizer :=
  plusCentralizerExtension.range_inl_eq_ker_rightHom.trans centralizerProjection_ker

/-- Every dihedral factor's central involution is the original first generator. -/
theorem plusCentralizerExtension_inl_r_two (i : Fin 6) :
    (plusCentralizerExtension.inl
      (QuotientGroup.mk (Pi.mulSingle i (DihedralGroup.r 2))) : Model) = a := by
  rw [plusCentralizerExtension_inl]
  exact literalCorePlusEquiv_r_two_coe i

/-- The full quotient map remains the actual conjugation action on Q/Z(Q). -/
theorem plusCentralizerExtension_rightHom (c : centralizer) :
    (plusCentralizerExtension.rightHom c : TwoCoreLinearModel.Matrix12ˣ) =
      quotientAction (centralizerEquiv c) := by
  change (centralizerExtension.rightHom c : TwoCoreLinearModel.Matrix12ˣ) = _
  rw [centralizerExtension_rightHom]
  exact quotientEquiv_mk c

/-- The full intrinsic quotient C/O₂(C) is the actual triple-cover extension
by C₂. In particular, its order-three covering kernel has not been removed. -/
noncomputable def tripleCoverQuotientExtension :
    GroupExtension M22TripleCover (centralizer ⧸ pCore 2 centralizer)
      (Multiplicative (ZMod 2)) where
  inl := quotientEquiv.symm.toMonoidHom.comp coveringExtension.inl
  rightHom := coveringExtension.rightHom.comp quotientEquiv.toMonoidHom
  inl_injective := quotientEquiv.symm.injective.comp coveringExtension.inl_injective
  range_inl_eq_ker_rightHom := by
    ext q
    change (∃ x, quotientEquiv.symm (coveringExtension.inl x) = q) ↔
      coveringExtension.rightHom (quotientEquiv q) = 1
    rw [← MonoidHom.mem_ker, ← coveringExtension.range_inl_eq_ker_rightHom]
    change (∃ x, quotientEquiv.symm (coveringExtension.inl x) = q) ↔
      ∃ x, coveringExtension.inl x = quotientEquiv q
    simp only [MulEquiv.symm_apply_eq]
  rightHom_surjective := coveringExtension.rightHom_surjective.comp quotientEquiv.surjective

/-- The inclusion is the genuine derived-subgroup inclusion under the full quotient equivalence. -/
theorem tripleCoverQuotientExtension_inl (x : M22TripleCover) :
    quotientEquiv (tripleCoverQuotientExtension.inl x) = coverInclusion x := by
  change quotientEquiv (quotientEquiv.symm (coveringExtension.inl x)) = _
  rw [quotientEquiv.apply_symm_apply, coveringExtension_inl]

/-- The outer quotient map agrees with the actual C/H quotient character. -/
theorem tripleCoverQuotientExtension_rightHom (c : centralizer) :
    tripleCoverQuotientExtension.rightHom (QuotientGroup.mk' (pCore 2 centralizer) c) =
      centralizerOuterCharacter c := by
  change outerCharacter (quotientEquiv (QuotientGroup.mk' (pCore 2 centralizer) c)) =
    outerCharacter (centralizerExtension.rightHom c)
  rw [centralizerExtension_rightHom]

/-- The covering scalar still has order three in the full intrinsic quotient. -/
theorem tripleCoverQuotientExtension_scalar_order :
    orderOf (tripleCoverQuotientExtension.inl M22TripleCover.scalar) = 3 := by
  rw [orderOf_injective tripleCoverQuotientExtension.inl
    tripleCoverQuotientExtension.inl_injective, M22TripleCover.scalar_order]

/-- The marked outer coset acts nontrivially on the center of the triple cover,
by inversion, inside the full intrinsic quotient extension. -/
theorem tripleCoverQuotientExtension_inverts_scalar :
    tripleCoverQuotientExtension.conjAct
      (QuotientGroup.mk' (pCore 2 centralizer) markedOuter) M22TripleCover.scalar =
        M22TripleCover.scalar⁻¹ := by
  apply tripleCoverQuotientExtension.inl_injective
  rw [GroupExtension.inl_conjAct_comm, map_inv]
  apply quotientEquiv.injective
  rw [map_mul, map_mul, map_inv, map_inv, tripleCoverQuotientExtension_inl]
  have ho : quotientEquiv (QuotientGroup.mk' (pCore 2 centralizer) markedOuter) =
      outerElement := (centralizerExtension_rightHom _).symm.trans markedOuter_projection
  rw [ho]
  exact outerElement_conj_scalar

end Janko4.InvolutionCentralizers.First
