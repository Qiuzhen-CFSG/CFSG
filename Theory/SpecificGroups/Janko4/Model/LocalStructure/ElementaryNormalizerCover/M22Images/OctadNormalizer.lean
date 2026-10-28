module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.HexadLift
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NativeFNormalizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.Orthogonal

/-!
# Whole-normalizer coverage for the first M22 lift

The literal first M22 inverse image is a conjugate of the native octad
pullback Q. The native orthogonality calculation places every zero-form
elementary subgroup of Q in E or one of the two actual F occurrences.
The proved E-uniqueness and F-occurrence normalizer arguments then place
its whole normalizer in a Mathieu or linear-five local, including when
the second-class witness has not been positioned in E.

The last reductions remove this first lift from the mixed zero-form
source cases. The sextet and exceptional E8 lifts remain explicit
subgroup-placement alternatives, with no claim to normalizer coverage.
The maximal-two-local and radical consumers retain literal conjugators,
local normalizer images and both intrinsic and embedded normalizer cores.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988),
Proposition 2.2.2(i)--(ii) and Proposition 2.2.3, pp.490--491.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover
open LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB

/-- Zero intrinsic form is preserved by any actual ambient group equivalence. -/
theorem intrinsicForm_zero_map (X Y : Subgroup Model)
    [IsElementaryAbelian 2 X] [IsElementaryAbelian 2 Y]
    (e : Model ≃* Model) (he : X.map e.toMonoidHom = Y)
    (hzero : intrinsicElementaryForm X = 0) : intrinsicElementaryForm Y = 0 := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  have hu : (u.toMul : Model) ∈ X.map e.toMonoidHom := he.symm ▸ u.toMul.property
  have hv : (v.toMul : Model) ∈ X.map e.toMonoidHom := he.symm ▸ v.toMul.property
  obtain ⟨x,hx,hxu⟩ := hu
  obtain ⟨y,hy,hyv⟩ := hv
  change outerValue u.toMul v.toMul = 0
  rw [← hxu,← hyv]
  change outerValue (e x) (e y) = 0
  rw [outerValue_equiv]
  exact congrArg (fun B : LinearMap.BilinForm (ZMod 2) (Additive X) =>
    B (Additive.ofMul ⟨x,hx⟩) (Additive.ofMul ⟨y,hy⟩)) hzero

private theorem conjugate_comp (X : Subgroup Model) (g h : Model) :
    (X.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      X.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem conjugate_one (X : Subgroup Model) :
    X.map (MulAut.conj (1 : Model)).toMonoidHom = X :=
  mem_normalizer_iff_map_conj_eq.mp (normalizer (X : Set Model)).one_mem

/-- The first source lift has actual E/F placement after arbitrary ambient
conjugation. The only possible F conjugators are the original one and its
product with the native kernel seed. -/
theorem zero_form_octad_placement (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (g : Model) (hXQ : X ≤ LinearFive.Q.map (MulAut.conj g).toMonoidHom)
    (hzero : intrinsicElementaryForm X = 0) :
    X ≤ embeddedKernel.map (MulAut.conj g).toMonoidHom ∨
      X ≤ nativeF.map (MulAut.conj g).toMonoidHom ∨
      X ≤ nativeF.map (MulAut.conj (g*LinearFive.Geometry.seed)).toMonoidHom := by
  let e := MulAut.conj g⁻¹
  let Y := X.map e.toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hYQ : Y ≤ LinearFive.Q := by
    have hm := map_mono (f := e.toMonoidHom) hXQ
    change Y ≤ (LinearFive.Q.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom at hm
    rwa [conjugate_comp,inv_mul_cancel,conjugate_one] at hm
  have hYzero := intrinsicForm_zero_map X Y e rfl hzero
  have hback : Y.map (MulAut.conj g).toMonoidHom = X := by
    change (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X
    rw [conjugate_comp,mul_inv_cancel,conjugate_one]
  rcases LinearFive.Geometry.zero_form_Q_placement Y hYQ hYzero with h | h | h
  · exact Or.inl (hback ▸ map_mono h)
  · exact Or.inr (Or.inl (hback ▸ map_mono h))
  · have hm := map_mono (f := (MulAut.conj g).toMonoidHom) h
    change Y.map (MulAut.conj g).toMonoidHom ≤
      (nativeF.map (MulAut.conj LinearFive.Geometry.seed).toMonoidHom).map
        (MulAut.conj g).toMonoidHom at hm
    rw [hback,conjugate_comp] at hm
    exact Or.inr (Or.inr hm)

/-- The E normalizer argument transported through the literal ambient
conjugator, without positioning the second-class witness in the original E. -/
theorem kernel_conjugate_nonfirst_normalizer_cover (X : Subgroup Model) (g : Model)
    (hXE : X ≤ embeddedKernel.map (MulAut.conj g).toMonoidHom)
    (t : Model) (htX : t ∈ X) (ht2 : orderOf t = 2) (hnt : ¬ IsConj a t) :
    normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom := by
  let e := MulAut.conj g⁻¹
  let Y := X.map e.toMonoidHom
  have hYE : Y ≤ embeddedKernel := by
    have hm := map_mono (f := e.toMonoidHom) hXE
    change Y ≤ (embeddedKernel.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom at hm
    rwa [conjugate_comp,inv_mul_cancel,conjugate_one] at hm
  have hnte : ¬ IsConj a (e t) := by
    intro h
    exact hnt (h.trans (isConj_iff.mpr ⟨g,by simp [e,mul_assoc]⟩))
  have hn := normalizer_le_mathieu_of_nonfirst_kernel_involution Y hYE
    (e t) (mem_map_of_mem _ htX) ((e.orderOf_eq t).trans ht2) hnte
  have hback : Y.map (MulAut.conj g).toMonoidHom = X := by
    change (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X
    rw [conjugate_comp,mul_inv_cancel,conjugate_one]
  have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hn
  rwa [map_equiv_normalizer_eq,hback] at hm

/-- Whole-normalizer coverage for the zero-form octad branch. The second-class
member belongs to X itself; no position in the chosen E is assumed. -/
theorem zero_form_octad_normalizer_cover (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (g : Model) (hXQ : X ≤ LinearFive.Q.map (MulAut.conj g).toMonoidHom)
    (hzero : intrinsicElementaryForm X = 0)
    (t : Model) (htX : t ∈ X) (ht2 : orderOf t = 2) (hnt : ¬ IsConj a t) :
    ∃ k : Model,
      normalizer (X : Set Model) ≤ LinearFive.M_F.map (MulAut.conj k).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj k).toMonoidHom := by
  rcases zero_form_octad_placement X g hXQ hzero with h | h | h
  · exact ⟨g,Or.inr (kernel_conjugate_nonfirst_normalizer_cover X g h t htX ht2 hnt)⟩
  · exact nativeF_conjugate_nonfirst_normalizer_cover X g h t htX ht2 hnt
  · exact nativeF_conjugate_nonfirst_normalizer_cover X _ h t htX ht2 hnt

namespace M22Images
open Sporadic.Mathieu MathieuCode M22ChapterH

/-- The first literal residual lift now supplies whole-normalizer coverage.
Both its M22 marking and its J4 conjugator are retained through the Q comparison. -/
theorem hexadLift_normalizer_cover (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (g : Model) (hX : X ≤ (residualLift (m22InnerHexadKernel m22SourceOctad)).map
      (MulAut.conj g).toMonoidHom) (hzero : intrinsicElementaryForm X = 0)
    (t : Model) (htX : t ∈ X) (ht2 : orderOf t = 2) (hnt : ¬ IsConj a t) :
    ∃ k : Model,
      normalizer (X : Set Model) ≤ LinearFive.M_F.map (MulAut.conj k).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨s,hs⟩ := hexadLift_eq_Q_conjugate
  rw [hs,conjugate_comp] at hX
  exact zero_form_octad_normalizer_cover X _ hX hzero t htX ht2 hnt

/-- Removing the first source lift leaves only the sextet and exceptional E8
subgroup-placement cases. The first two alternatives already cover N(X). -/
theorem zero_form_nonpure_normalizer_or_residual
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    ∃ g : Model,
      normalizer (X : Set Model) ≤ LinearFive.M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom ∨
      X ≤ (residualLift Sextet.innerTranslations).map (MulAut.conj g).toMonoidHom ∨
      X ≤ (residualLift (smallContainer 0)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨t,ht,ht2,hnt,_⟩ := nonpure_contains_second X hn
  obtain ⟨g,h | h | h⟩ := zero_form_nonpure_octad_cases X hzero hn
  · obtain ⟨k,hk | hk⟩ := zero_form_octad_normalizer_cover X g h hzero t ht ht2 hnt
    · exact ⟨k,Or.inl hk⟩
    · exact ⟨k,Or.inr (Or.inl hk)⟩
  · exact ⟨g,Or.inr (Or.inr (Or.inl h))⟩
  · exact ⟨g,Or.inr (Or.inr (Or.inr h))⟩

/-- At a maximal two-local, the first M22 lift gives equality with one of
the two named native locals. -/
theorem maximal_twoLocal_of_hexadLift
    (X H : Subgroup Model) [IsElementaryAbelian 2 X]
    (g : Model) (hX : X ≤ (residualLift (m22InnerHexadKernel m22SourceOctad)).map
      (MulAut.conj g).toMonoidHom) (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hH : IsMaximalTwoLocal H) (hHX : H = normalizer (X : Set Model)) :
    ∃ k : Model, H = LinearFive.M_F.map (MulAut.conj k).toMonoidHom ∨
      H = max1.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨t,ht,ht2,hnt,_⟩ := nonpure_contains_second X hn
  obtain ⟨k,h | h⟩ := hexadLift_normalizer_cover X g hX hzero t ht ht2 hnt
  · exact ⟨k,Or.inl (hH.eq_of_le (nativeF_generated_isTwoLocal.map_equiv (MulAut.conj k))
      (hHX ▸ h))⟩
  · exact ⟨k,Or.inr (hH.eq_of_le (embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj k))
      (hHX ▸ h))⟩

/-- The first M22 lift applied to the original radical subgroup. The whole
normalizer is covered, and the local normalizer and its full core retain
the original ambient inclusion maps. -/
theorem radical_local_of_hexadLift
    (P X : Subgroup Model) [IsElementaryAbelian 2 X] (hP : P.IsPRadical 2)
    (g : Model) (hX : X ≤ (residualLift (m22InnerHexadKernel m22SourceOctad)).map
      (MulAut.conj g).toMonoidHom) (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ (k : Model) (H : Subgroup Model), IsTwoLocal H ∧
      (H = LinearFive.M_F.map (MulAut.conj k).toMonoidHom ∨
        H = max1.map (MulAut.conj k).toMonoidHom) ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  obtain ⟨t,ht,ht2,hnt,_⟩ := nonpure_contains_second X hn
  obtain ⟨k,hk⟩ := hexadLift_normalizer_cover X g hX hzero t ht ht2 hnt
  obtain ⟨H,hH,hrow,hNH⟩ : ∃ H : Subgroup Model, IsTwoLocal H ∧
      (H = LinearFive.M_F.map (MulAut.conj k).toMonoidHom ∨
        H = max1.map (MulAut.conj k).toMonoidHom) ∧ normalizer (P : Set Model) ≤ H := by
    rcases hk with h | h
    · exact ⟨_,nativeF_generated_isTwoLocal.map_equiv (MulAut.conj k),Or.inl rfl,hNX.trans h⟩
    · exact ⟨_,embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj k),Or.inr rfl,hNX.trans h⟩
  have hPH := P.le_normalizer.trans hNH
  have hN := hNH.trans H.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf H hPH hN
  refine ⟨k,H,hH,hrow,hNH,hPH,?_,hP.subgroupOf_of_normalizer_normalizes H hPH hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hNH]
  · rw [hcore,map_subgroupOf_eq_of_le hPH]

end M22Images
end Janko4.LocalStructure.ElementaryNormalizerCover
