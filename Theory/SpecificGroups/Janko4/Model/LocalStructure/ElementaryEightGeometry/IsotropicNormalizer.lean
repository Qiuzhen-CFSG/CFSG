module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Application

/-!
# Normalizer applications of the native isotropic sixteen

Conjugation transports invariance from the native (b) eight through the fusion
word and the literal selected-row corrections. Maximal two-local and radical
arguments then take place in the zero-form sixteen normalizer, retaining the
original normalizer and local core maps.
Source: Kleidman--Wilson (1988), Corollary 2.3.6, printed p.493.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Subgroup Theory.GroupTheory Cardinality KernelCount QuotientCount.Image
open SylowCore SylowCore.Transport LargeCenterRadicals.OuterHalf
open scoped IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup
local notation "L" => SylowCore.Local
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four

variable (hInv : normalizer (nativeEight 0 : Set Model) ≤
  normalizer (isotropicSubgroup : Set Model))
include hInv

/-- Invariance transports through an actual ambient conjugation. -/
theorem conjugateIsotropic_normalizer_le (g : Model) :
    normalizer ((nativeEight 0).map (MulAut.conj g).toMonoidHom : Set Model) ≤
      normalizer (conjugateIsotropic g : Set Model) := by
  have h := map_mono (f := (MulAut.conj g).toMonoidHom) hInv
  rwa [map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,
    map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective] at h

/-- The certified fusion word supplies the invariant sixteen in the common eight. -/
theorem fusedIsotropic_normalizer_le :
    normalizer (nativeEight 1 : Set Model) ≤
      normalizer (conjugateIsotropic nativeFusion : Set Model) := by
  simpa only [nativeFusion_eight] using conjugateIsotropic_normalizer_le hInv nativeFusion

omit hInv in
private theorem conjugation_comp' (a b : Model) :
    (MulAut.conj (a*b)).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
  ext x
  simp only [MulEquiv.coe_toMonoidHom,MonoidHom.comp_apply,MulAut.conj_apply,mul_inv_rev,mul_assoc]

omit hInv in
/-- The selected witness is the literal inverse-conjugation image of the fused sixteen. -/
theorem conjugateIsotropic_pullback (g : Model) :
    conjugateIsotropic (g⁻¹ * nativeFusion) =
      (conjugateIsotropic nativeFusion).map (MulAut.conj g⁻¹).toMonoidHom := by
  simp only [conjugateIsotropic,Subgroup.map_map,conjugation_comp']

omit hInv in
private theorem fused_eight_pullback (C : Subgroup Model) (g : Model)
    (hg : C.map (MulAut.conj g).toMonoidHom = nativeEight 1) :
    C = (nativeEight 0).map (MulAut.conj (g⁻¹ * nativeFusion)).toMonoidHom := by
  have hinv : (MulAut.conj g⁻¹).toMonoidHom = (MulAut.conj g).symm.toMonoidHom := by
    ext x
    simp
  have hback : (nativeEight 1).map (MulAut.conj g⁻¹).toMonoidHom = C := by
    rw [hinv]
    exact (Subgroup.map_symm_eq_iff_map_eq (K := C) (H := nativeEight 1)
      (e := MulAut.conj g)).mpr hg
  rw [conjugation_comp',←Subgroup.map_map,nativeFusion_eight,hback]

/-- The exact pullback sixteen is invariant under the full centralizer normalizer. -/
theorem isotropic_pullback_properties (C : Subgroup Model) (g : Model)
    (hg : C.map (MulAut.conj g).toMonoidHom = nativeEight 1) :
    let Y := conjugateIsotropic (g⁻¹ * nativeFusion)
    Y ≤ C ∧ Y ≠ ⊥ ∧ Nat.card Y = 16 ∧ intrinsicElementaryForm Y = 0 ∧
      normalizer (C : Set Model) ≤ normalizer (Y : Set Model) := by
  dsimp only
  have hC := fused_eight_pullback C g hg
  have hc := conjugateIsotropic_card (g⁻¹ * nativeFusion)
  refine ⟨?_,?_,hc,conjugateIsotropic_form_zero _,?_⟩
  · rw [hC]
    exact conjugateIsotropic_le _
  · intro he
    rw [he,card_bot] at hc
    contradiction
  · rw [hC]
    exact conjugateIsotropic_normalizer_le hInv _

/-- The two selected unprimed rows retain the bounded correction and fusion word. -/
theorem selected_row_isotropic_normalizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXL : X ≤ L) (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide))) :
    ∃ k : Fin 2048, (k = 0 ∨ k = Sections.twist r) ∧
      let g := rowFusion r * ((nativeMask k.val : L) : Model)
      let Y := conjugateIsotropic (g⁻¹ * nativeFusion)
      Y ≤ centralizer (X : Set Model) ∧ Y ≠ ⊥ ∧ Nat.card Y = 16 ∧
      intrinsicElementaryForm Y = 0 ∧
      normalizer (centralizer (X : Set Model) : Set Model) ≤ normalizer (Y : Set Model) ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) := by
  obtain ⟨k,hk,hg⟩ := selected_row_fused_centralizer X hXL hs r hrow
  obtain ⟨hY,hne,hc,hf,hN⟩ := isotropic_pullback_properties hInv _ _ hg
  exact ⟨k,hk,hY,hne,hc,hf,hN,(normalizer_le_normalizer_centralizer X).trans hN⟩

/-- The selected primed row uses its original bounded native-kernel conjugator. -/
theorem selected_primed_isotropic_normalizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXL : X ≤ L) (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (hrow : (X.subgroupOf L).map π = pairRowImage 3) :
    ∃ k : Fin 2048, (k = 0 ∨ k = 16) ∧
      let g : Model := ((nativeMask k.val : L) : Model)
      let Y := conjugateIsotropic (g⁻¹ * nativeFusion)
      Y ≤ centralizer (X : Set Model) ∧ Y ≠ ⊥ ∧ Nat.card Y = 16 ∧
      intrinsicElementaryForm Y = 0 ∧
      normalizer (centralizer (X : Set Model) : Set Model) ≤ normalizer (Y : Set Model) ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) := by
  obtain ⟨k,hk,hg⟩ := Sections.primed_ambient_centralizer_conjugacy X hXL hs hrow
  obtain ⟨hY,hne,hc,hf,hN⟩ := isotropic_pullback_properties hInv _ _ hg
  exact ⟨k,hk,hY,hne,hc,hf,hN,(normalizer_le_normalizer_centralizer X).trans hN⟩

/-- At a maximal two-local the zero-form sixteen has the entire original normalizer. -/
theorem selected_row_isotropic_maximal_normalizer (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide)))
    (hM : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ k : Fin 2048, (k = 0 ∨ k = Sections.twist r) ∧
      let g := rowFusion r * ((nativeMask k.val : L) : Model)
      let Y := conjugateIsotropic (g⁻¹ * nativeFusion)
      Y ≤ centralizer (X : Set Model) ∧ Y ≠ ⊥ ∧ Nat.card Y = 16 ∧
      intrinsicElementaryForm Y = 0 ∧ normalizer (X : Set Model) = normalizer (Y : Set Model) := by
  obtain ⟨k,hk,hY,hne,hc,hf,_,hN⟩ := selected_row_isotropic_normalizer hInv X hXL hs r hrow
  refine ⟨k,hk,hY,hne,hc,hf,?_⟩
  exact hM.eq_of_le ⟨_,hne,IsElementaryAbelian.isPGroup 2 _,rfl⟩ hN

/-- The same maximal-two-local equality for the selected primed row. -/
theorem selected_primed_isotropic_maximal_normalizer (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (hrow : (X.subgroupOf L).map π = pairRowImage 3)
    (hM : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ k : Fin 2048, (k = 0 ∨ k = 16) ∧
      let g : Model := ((nativeMask k.val : L) : Model)
      let Y := conjugateIsotropic (g⁻¹ * nativeFusion)
      Y ≤ centralizer (X : Set Model) ∧ Y ≠ ⊥ ∧ Nat.card Y = 16 ∧
      intrinsicElementaryForm Y = 0 ∧ normalizer (X : Set Model) = normalizer (Y : Set Model) := by
  obtain ⟨k,hk,hY,hne,hc,hf,_,hN⟩ := selected_primed_isotropic_normalizer hInv X hXL hs hrow
  refine ⟨k,hk,hY,hne,hc,hf,?_⟩
  exact hM.eq_of_le ⟨_,hne,IsElementaryAbelian.isPGroup 2 _,rfl⟩ hN

omit hInv in
private theorem isotropic_radical_restriction (P Y : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 Y] (hne : Y ≠ ⊥)
    (hNY : normalizer (P : Set Model) ≤ normalizer (Y : Set Model)) :
    let M := normalizer (Y : Set Model)
    Y ≤ P ∧ IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  let M := normalizer (Y : Set Model)
  have hPM : P ≤ M := P.le_normalizer.trans hNY
  have hYP : Y ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
    P Y hP.isPGroup (IsElementaryAbelian.isPGroup 2 Y) hP.2.le hNY
  have hN := hNY.trans M.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf M hPM hN
  refine ⟨hYP,⟨Y,hne,IsElementaryAbelian.isPGroup 2 Y,rfl⟩,hNY,hPM,?_,
    hP.subgroupOf_of_normalizer_normalizes M hPM hN,hcore,?_⟩
  · rw [←subgroupOf_normalizer_eq hPM,map_subgroupOf_eq_of_le hNY]
  · rw [hcore,map_subgroupOf_eq_of_le hPM]

/-- Radical restriction for either unprimed row preserves both literal local-core maps. -/
theorem selected_row_isotropic_radical_restriction (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide)))
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ k : Fin 2048, (k = 0 ∨ k = Sections.twist r) ∧
      let g := rowFusion r * ((nativeMask k.val : L) : Model)
      let Y := conjugateIsotropic (g⁻¹ * nativeFusion)
      let M := normalizer (Y : Set Model)
      Y ≤ centralizer (X : Set Model) ∧ Y ≠ ⊥ ∧ Nat.card Y = 16 ∧
      intrinsicElementaryForm Y = 0 ∧
      Y ≤ P ∧ IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  obtain ⟨k,hk,hY,hne,hc,hf,_,hN⟩ := selected_row_isotropic_normalizer hInv X hXL hs r hrow
  exact ⟨k,hk,hY,hne,hc,hf,isotropic_radical_restriction P _ hP hne (hNX.trans hN)⟩

/-- Radical restriction for the primed row retains its own correction and the same core maps. -/
theorem selected_primed_isotropic_radical_restriction (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (hrow : (X.subgroupOf L).map π = pairRowImage 3)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ k : Fin 2048, (k = 0 ∨ k = 16) ∧
      let g : Model := ((nativeMask k.val : L) : Model)
      let Y := conjugateIsotropic (g⁻¹ * nativeFusion)
      let M := normalizer (Y : Set Model)
      Y ≤ centralizer (X : Set Model) ∧ Y ≠ ⊥ ∧ Nat.card Y = 16 ∧
      intrinsicElementaryForm Y = 0 ∧
      Y ≤ P ∧ IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  obtain ⟨k,hk,hY,hne,hc,hf,_,hN⟩ := selected_primed_isotropic_normalizer hInv X hXL hs hrow
  exact ⟨k,hk,hY,hne,hc,hf,isotropic_radical_restriction P _ hP hne (hNX.trans hN)⟩

end Janko4.LocalStructure.ElementaryEightGeometry
