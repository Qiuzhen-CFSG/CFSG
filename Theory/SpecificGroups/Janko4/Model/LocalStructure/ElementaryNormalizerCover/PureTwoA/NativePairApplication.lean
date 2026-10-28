module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePairCentralizer

/-!
# The native pure-pair branch in the original ambient group

The full centralizer of the marked pure pair is contained in max1. Transporting
that fact by one ambient conjugator positions every elementary overgroup and
its whole centralizer in the same local subgroup. If the extension has trivial
Mathieu image, kernel uniqueness controls its whole normalizer. The maximal
TWO-local and arbitrary-radical applications preserve that conjugator and the
literal normalizer and two-core maps.

This closes the trivial-image extension branch. No identification of arbitrary
printed MOG coordinates, nontrivial-image sextet classification, or exhaustive
pure-first cover is assumed here. Source: Kleidman--Wilson (1988), Section 2.1,
pp.488--489, using the independent native pair census for the centralizer.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePair
open LinearFive InvolutionCentralizers.Second
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel
set_option backward.isDefEq.respectTransparency true

private theorem map_conj_cancel (A : Subgroup Model) (g : Model) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Model := by ext x; simp [mul_assoc]
  rw [he,map_id]

/-- One literal pair conjugator positions the full centralizer of any overgroup. -/
theorem marked_extension_centralizer (X : Subgroup Model) (g : Model)
    (hpair : nativePair.map (MulAut.conj g).toMonoidHom ≤ X) :
    centralizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom := by
  have h := map_mono (f := (MulAut.conj g).toMonoidHom) centralizer_le_max1
  rw [map_centralizer_equiv] at h
  exact (centralizer_le hpair).trans h

/-- Arbitrary-rank elementary extensions stay inside the same native Mathieu local. -/
theorem marked_elementary_extension (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (g : Model) (hpair : nativePair.map (MulAut.conj g).toMonoidHom ≤ X) :
    X ≤ max1.map (MulAut.conj g).toMonoidHom ∧
    centralizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom := by
  have hc := marked_extension_centralizer X g hpair
  exact ⟨X.le_centralizer.trans hc,hc⟩

/-- Kernel uniqueness gives whole-normalizer containment for the trivial-image extension. -/
theorem marked_kernel_extension_normalizer (X : Subgroup Model) (g : Model)
    (hpair : nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (hkernel : X ≤ embeddedKernel.map (MulAut.conj g).toMonoidHom) :
    normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom := by
  let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
  have hPY : nativePair ≤ Y := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hpair
    rwa [map_conj_cancel] at hh
  have hYE : Y ≤ embeddedKernel := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hkernel
    rwa [map_conj_cancel] at hh
  have hc : centralizer (Y : Set Model) ≤ max1 :=
    (centralizer_le hPY).trans centralizer_le_max1
  have hn := map_mono (f := (MulAut.conj g).toMonoidHom)
    (normalizer_le_mathieu_of_kernel_and_centralizer Y hYE hc)
  rw [map_equiv_normalizer_eq] at hn
  have hY : Y.map (MulAut.conj g).toMonoidHom = X := by
    simpa only [inv_inv] using map_conj_cancel X g⁻¹
  rwa [hY] at hn

/-- Maximality among two-locals turns the same containment into the actual max1 equality. -/
theorem marked_kernel_extension_maximal (X : Subgroup Model) (g : Model)
    (hpair : nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (hkernel : X ≤ embeddedKernel.map (MulAut.conj g).toMonoidHom)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    normalizer (X : Set Model) = max1.map (MulAut.conj g).toMonoidHom :=
  hmax.eq_of_le (embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj g))
    (marked_kernel_extension_normalizer X g hpair hkernel)

/-- The literal arbitrary-radical application of the marked pure-pair branch. -/
theorem marked_kernel_extension_radical (P X : Subgroup Model) (hP : P.IsPRadical 2)
    (g : Model) (hpair : nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (hkernel : X ≤ embeddedKernel.map (MulAut.conj g).toMonoidHom)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    let L := max1.map (MulAut.conj g).toMonoidHom
    IsTwoLocal L ∧ normalizer (P : Set Model) ≤ L ∧ P ≤ L ∧
      (normalizer (P.subgroupOf L : Set L)).map L.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf L).IsPRadical 2 ∧
      (normalizer (P.subgroupOf L : Set L)).pCoreIn 2 = P.subgroupOf L ∧
      ((normalizer (P.subgroupOf L : Set L)).pCoreIn 2).map L.subtype = P := by
  let L := max1.map (MulAut.conj g).toMonoidHom
  have hNL : normalizer (P : Set Model) ≤ L :=
    hNX.trans (marked_kernel_extension_normalizer X g hpair hkernel)
  have hPL := P.le_normalizer.trans hNL
  have hNN := hNL.trans L.le_normalizer
  have hc := hP.normalizer_core_subgroupOf L hPL hNN
  refine ⟨embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj g),hNL,hPL,?_,
    hP.subgroupOf_of_normalizer_normalizes L hPL hNN,hc,?_⟩
  · rw [← subgroupOf_normalizer_eq hPL,map_subgroupOf_eq_of_le hNL]
  · rw [hc,map_subgroupOf_eq_of_le hPL]

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePair
