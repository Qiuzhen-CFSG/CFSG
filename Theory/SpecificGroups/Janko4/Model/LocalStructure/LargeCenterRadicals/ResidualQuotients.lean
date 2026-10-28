module
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.PointOrbitCardinality
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.Mathieu.M24.Properties.Simplicity
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction
public import Theory.Representation.PSL3Two.SmallModules
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Normal residuals exclude the three simple large-center J₄ quotients

For a normal subgroup B of M, its intrinsic two-core is the restriction of
O₂(M). The literal quotient map identifies B/O₂(B) with a normal image in
M/O₂(M). If the ambient quotient is simple and this image is nontrivial, the
image is the whole quotient. Its order therefore equals the ambient quotient
order. The orders 168 and 6048 exclude SL₅(2), M₂₄ and A₈.

These are the normal-image endpoints needed for the three large-center rows of
An--O'Brien--Wilson, LMS J. Comput. Math. 6 (2003), Table 1, p.124. Global native
radical coverage from Section 4, p.122, is not asserted here. Concrete group
facts retain their imported ATLAS attribution; see LICENSES/ATLAS.txt.
-/

public section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals

/-! The normality hypothesis is used at the literal subgroup level.  We expose
the restriction identity and the quotient map before applying simplicity; this
keeps the source argument from silently replacing the intrinsic core by an
ambient subgroup of matching order. -/

/-- The intrinsic two-core of a whole-normal residual is the restriction of
the ambient two-core. -/
theorem normal_residual_pCore_eq_restriction
    {M : Type*} [Group M] (B : Subgroup M) [B.Normal] :
    pCore 2 B = (pCore 2 M).comap B.subtype :=
  pCore_eq_comap_of_normal 2 B

/-- After embedding back into the ambient group, the intrinsic core is the
literal intersection with the ambient core. -/
theorem normal_residual_pCore_map_eq_inf
    {M : Type*} [Group M] (B : Subgroup M) [B.Normal] :
    (pCore 2 B).map B.subtype = B ⊓ pCore 2 M := by
  rw [normal_residual_pCore_eq_restriction, map_comap_eq]
  simp

/-- The literal quotient map identifies a whole-normal residual modulo its
intrinsic core with its image in the ambient core quotient. -/
noncomputable def normal_residual_quotient_equiv_image
    {M : Type*} [Group M] (B : Subgroup M) [B.Normal] :
    B ⧸ pCore 2 B ≃* B.map (QuotientGroup.mk' (pCore 2 M)) :=
  coreQuotientEquivImage 2 B

private theorem normal_core_quotient_card {M Q : Type*} [Group M] [Group Q]
    [Finite M] [IsSimpleGroup Q] (B : Subgroup M) [B.Normal]
    (hne : Nat.card (B ⧸ pCore 2 B) ≠ 1)
    (e : (M ⧸ pCore 2 M) ≃* Q) :
    Nat.card (B ⧸ pCore 2 B) = Nat.card Q := by
  let q := QuotientGroup.mk' (pCore 2 M)
  let I := B.map q
  let : I.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup (M ⧸ pCore 2 M) := e.isSimpleGroup
  have hi : Nat.card (B ⧸ pCore 2 B) = Nat.card I :=
    Nat.card_congr (normal_residual_quotient_equiv_image B).toEquiv
  rcases (inferInstance : I.Normal).eq_bot_or_eq_top with hz | ht
  · exact (hne (hi.trans (hz ▸ card_bot))).elim
  · rw [ht, card_top] at hi
    exact hi.trans (Nat.card_congr e.toEquiv)

private theorem sl5_simple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  exact (BinaryLinear.OuterCyclic.projectiveEquivSL (n := 5) (by decide)).symm.isSimpleGroup

/-- A normal full-core residual of either source order excludes all three
simple quotients in the large-center part of the published J₄ table. -/
theorem normal_residual_excludes_three_quotients
    {M : Type*} [Group M] [Finite M] (B : Subgroup M) [B.Normal]
    (hc : Nat.card (B ⧸ pCore 2 B) = 168 ∨ Nat.card (B ⧸ pCore 2 B) = 6048) :
    ¬ (Nonempty ((M ⧸ pCore 2 M) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
       Nonempty ((M ⧸ pCore 2 M) ≃* Sporadic.Mathieu.M24) ∨
       Nonempty ((M ⧸ pCore 2 M) ≃* alternatingGroup (Fin 8))) := by
  have hne : Nat.card (B ⧸ pCore 2 B) ≠ 1 := by rcases hc with h | h <;> omega
  intro he
  rcases he with he | he | he <;> obtain ⟨e⟩ := he
  · let := sl5_simple
    have hh := normal_core_quotient_card B hne e
    rw [Representation.SL5ExteriorSquare.card_specialLinearFive] at hh
    rcases hc with h | h <;> omega
  · let := Sporadic.Mathieu.m24_isSimpleGroup
    have hh := normal_core_quotient_card B hne e
    rw [Sporadic.Mathieu.m24_order] at hh
    rcases hc with h | h <;> omega
  · let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    have hh := normal_core_quotient_card B hne e
    have h8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [h8] at hh
    rcases hc with h | h <;> omega

/-- An actual U₃(3) marking of a normal residual excludes each of the three
large-center quotient rows, using its full intrinsic two-core. -/
theorem unitary_normal_residual_quotients_excluded
    {M : Type*} [Group M] [Finite M] (B : Subgroup M) [B.Normal]
    (e : (B ⧸ pCore 2 B) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ¬ (Nonempty ((M ⧸ pCore 2 M) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
       Nonempty ((M ⧸ pCore 2 M) ≃* Sporadic.Mathieu.M24) ∨
       Nonempty ((M ⧸ pCore 2 M) ≃* alternatingGroup (Fin 8))) :=
  normal_residual_excludes_three_quotients B (Or.inr
    ((Nat.card_congr e.toEquiv).trans Atlas.G2.LieAutomorphismExtensions.card_binaryDerived))

/-- The same exclusion for an actual SL₃(2) marking of a normal residual. -/
theorem binaryThree_normal_residual_quotients_excluded
    {M : Type*} [Group M] [Finite M] (B : Subgroup M) [B.Normal]
    (e : (B ⧸ pCore 2 B) ≃* BinaryLinearThree.Group) :
    ¬ (Nonempty ((M ⧸ pCore 2 M) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
       Nonempty ((M ⧸ pCore 2 M) ≃* Sporadic.Mathieu.M24) ∨
       Nonempty ((M ⧸ pCore 2 M) ≃* alternatingGroup (Fin 8))) :=
  normal_residual_excludes_three_quotients B (Or.inl
    ((Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_SL))

end Janko4.LocalStructure.LargeCenterRadicals
