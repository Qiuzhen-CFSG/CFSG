module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Isotropic
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Fusion.Geometry
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Sections.Native
public import Theory.ElementaryAbelian.Injective
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.PrimedCentralizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Nondegenerate
public import Theory.GroupTheory.PRadical.NormalizerRestriction
public import Theory.GroupTheory.MaximalTwoLocalElementary
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.PairKernel
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Lifts
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.NativeSubgroups
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.NativeObstruction

/-!
# Native quotient-row application interface

The source row groups are applied through the actual max1 quotient map. This
leaf records the literal inverse image, exact kernel fixed spaces, full
ambient centralizers of arbitrary elementary lifts of both unprimed rows
and the primed (d) row, their intrinsic nondegeneracy, explicit fusion, and
the signed-pair obstruction. The whole-normalizer enlargement, maximal
two-local equality at the centralizer stage, and arbitrary-radical restriction
retain the original inclusion and local-core maps. The bounded native kernel
corrections classify the selected lifts; exhaustive row selection belongs to
the cover. The native zero-form sixteen and its transported selected-row
witnesses are constructed; whole-normalizer invariance remains to be proved.
Source: Kleidman--Wilson (1988), Figures 1/2 and Propositions 2.3.4--2.3.5,
printed pp.486, 490, 492--493.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Cardinality Cardinality.QuotientCount.Image
open Janko4.LocalStructure.SylowCore Janko4.LocalStructure.SylowCore.Transport
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

abbrev Local := Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four
abbrev Kernel := Cardinality.localKernel matrixA_mul_self matrixB_pow_four
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four

/-- The genuine inverse image of a selected Figure 2 quotient row. -/
@[expose] def rowLift (r : Fin 4) : Subgroup Model :=
  ((rowImage r).comap π).map Local.subtype

theorem rowImage_comap_map (r : Fin 4) :
    ((rowImage r).comap π).map π = rowImage r := by
  exact map_comap_eq_self_of_surjective (starProjection_surjective _ _) _

/-- Restriction of the ambient inverse image recovers precisely the selected row. -/
theorem rowLift_image (r : Fin 4) :
    ((rowLift r).subgroupOf Local).map π = rowImage r := by
  have hs : (rowLift r).subgroupOf Local = (rowImage r).comap π := by
    change (((rowImage r).comap π).map Local.subtype).comap Local.subtype = _
    exact comap_map_eq_self_of_injective Subtype.val_injective _
  rw [hs]
  exact rowImage_comap_map r

/-- The genuine inverse image with the Figure 1 pair permutation retained. -/
@[expose] def pairRowLift (r : Fin 4) : Subgroup Model :=
  ((pairRowImage r).comap π).map Local.subtype

theorem pairRowLift_image (r : Fin 4) :
    ((pairRowLift r).subgroupOf Local).map π = pairRowImage r := by
  have hs : (pairRowLift r).subgroupOf Local = (pairRowImage r).comap π := by
    change (((pairRowImage r).comap π).map Local.subtype).comap Local.subtype = _
    exact comap_map_eq_self_of_injective Subtype.val_injective _
  rw [hs]
  exact map_comap_eq_self_of_surjective (starProjection_surjective _ _) _

/-- For an arbitrary native subgroup with a selected whole image, the finite
equation characterizes membership in its FULL ambient centralizer on the kernel. -/
theorem pairRow_mask_mem_ambient_centralizer_iff
    (X : Subgroup Model) (hXL : X ≤ Local) (r : Fin 4)
    (hrow : (X.subgroupOf Local).map π = pairRowImage r) (m : Fin 2048) :
    (((maskEquiv matrixA_mul_self matrixB_pow_four m : Kernel) : Local) : Model) ∈
      centralizer (X : Set Model) ↔ fixedTest (unprimedRow r) m := by
  rw [← mask_mem_pairRow_centralizer_iff (X.subgroupOf Local) r hrow]
  constructor
  · intro h a ha
    apply Subtype.ext
    exact h a ha
  · intro h x hx
    exact congrArg (fun a : Local => (a : Model)) (h ⟨x,hXL hx⟩ hx)

/-- Exact fixed-space sizes for the four source rows. -/
theorem rowImage_fixed_masks (r : Fin 4) :
    Nat.card (fixedMasks r) = if r.val < 2 then 16 else 32 := by
  fin_cases r
  · exact fixedMasks0_card
  · exact fixedMasks1_card
  · exact fixedMasks2_card
  · exact fixedMasks3_card

end Janko4.LocalStructure.ElementaryEightGeometry

set_option backward.isDefEq.respectTransparency true
public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Subgroup Cardinality KernelCount QuotientCount.Image SylowCore SylowCore.Transport
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY basis
local notation "L" => SylowCore.Local
local notation "E" => localKernel matrixA_mul_self matrixB_pow_four
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four

/-- The full ambient centralizer intersects the original kernel in precisely
 the fixed subgroup used to construct the native elementary eight. -/
theorem nativeEight_kernel_centralizer (r : Fin 2) :
    centralizer (nativeEight r : Set Model) ⊓ (E).map (L).subtype =
      (centralKernel r).map (L).subtype := by
  ext g
  constructor
  · rintro ⟨hg, ⟨k,hk,rfl⟩⟩
    refine ⟨k,?_,rfl⟩
    refine ⟨⟨k,hk⟩,?_,rfl⟩
    intro a ha
    apply Subtype.ext
    exact hg a (mem_map_of_mem (L).subtype ((show liftClosure r ≤ localEight r from le_sup_left) ha))
  · rintro ⟨k,hk,rfl⟩
    refine ⟨?_,mem_map_of_mem (L).subtype (centralKernel_le_kernel r hk)⟩
    exact (nativeEight r).le_centralizer
      (mem_map_of_mem (L).subtype ((show centralKernel r ≤ localEight r from le_sup_right) hk))

theorem nativeEight_kernel_centralizer_card (r : Fin 2) :
    Nat.card (centralizer (nativeEight r : Set Model) ⊓ (E).map (L).subtype : Subgroup Model) = 16 := by
  rw [nativeEight_kernel_centralizer, card_map_of_injective (L).subtype_injective,
    centralKernel_card]

/-- The signed-pair obstruction in the literal restricted quotient of an
 arbitrary ambient elementary subgroup. -/
theorem ambient_elementary_excludes_b_rows (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hp : (twistedPairLift : Model) ∈ X) (r : Fin 4) (hr : r = 0 ∨ r = 2)
    (hrow : (X.subgroupOf L).map π = pairRowImage r) : False := by
  let : IsElementaryAbelian 2 (X.subgroupOf L) := IsElementaryAbelian.subgroupOf hXL
  exact elementary_image_ne_b_rows (X.subgroupOf L) hp r hr hrow

end Janko4.LocalStructure.ElementaryEightGeometry

public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Subgroup Theory.GroupTheory Cardinality KernelCount QuotientCount.Image SylowCore SylowCore.Transport
open scoped IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup
local notation "L" => SylowCore.Local
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four

/-- Literal whole-normalizer enlargement for the two displayed native rows. -/
theorem markedNativeRow_normalizer_le (r : Fin 2) :
    normalizer (markedNativeRow r : Set Model) ≤ normalizer (nativeEight r : Set Model) := by
  rw [← markedNativeRow_centralizer]
  exact normalizer_le_normalizer_centralizer _

/-- The signed primed row enlarges to the same full elementary-eight normalizer. -/
theorem primedNativeRow_normalizer_le :
    normalizer (primedNativeRow : Set Model) ≤ normalizer (nativeEight 1 : Set Model) := by
  rw [← primedNativeRow_centralizer]
  exact normalizer_le_normalizer_centralizer _

/-- At a maximal two-local, the selected full centralizer preserves the
original normalizer. The subsequent zero-form reduction still needs an
invariant isotropic subgroup of this calculated elementary eight. -/
theorem selected_row_maximal_normalizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXL : X ≤ L) (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide)))
    (hM : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    normalizer (X : Set Model) = normalizer (centralizer (X : Set Model) : Set Model) := by
  let C := centralizer (X : Set Model)
  let : IsElementaryAbelian 2 C := selected_ambient_centralizer_elementary X hXL hs r hrow
  have hC : C ≠ ⊥ := by
    intro he
    have hc := selected_ambient_centralizer_card X hXL hs r hrow
    change Nat.card C = 256 at hc
    rw [he, card_bot] at hc
    contradiction
  exact hM.eq_of_le ⟨C,hC,IsElementaryAbelian.isPGroup 2 C,rfl⟩
    (normalizer_le_normalizer_centralizer X)

/-- Restriction of an arbitrary radical to the calculated eight normalizer
preserves the entire original normalizer and both literal local-core maps.
This is the centralizer enlargement stage, before the isotropic reduction. -/
theorem selected_row_radical_restriction (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide)))
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    let C := centralizer (X : Set Model)
    let M := normalizer (C : Set Model)
    C ≤ P ∧ IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  dsimp only
  let C := centralizer (X : Set Model)
  let M := normalizer (C : Set Model)
  let : IsElementaryAbelian 2 C := selected_ambient_centralizer_elementary X hXL hs r hrow
  have hC : C ≠ ⊥ := by
    intro he
    have hc := selected_ambient_centralizer_card X hXL hs r hrow
    change Nat.card C = 256 at hc
    rw [he, card_bot] at hc
    contradiction
  have hNM : normalizer (P : Set Model) ≤ M :=
    hNX.trans (normalizer_le_normalizer_centralizer X)
  have hPM := P.le_normalizer.trans hNM
  have hCP : C ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
    P C hP.isPGroup (IsElementaryAbelian.isPGroup 2 C) hP.2.le hNM
  have hN := hNM.trans M.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf M hPM hN
  refine ⟨hCP,⟨C,hC,IsElementaryAbelian.isPGroup 2 C,rfl⟩,hNM,hPM,?_,
    hP.subgroupOf_of_normalizer_normalizes M hPM hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPM,map_subgroupOf_eq_of_le hNM]
  · rw [hcore,map_subgroupOf_eq_of_le hPM]

/-- The displayed-row centralizer calculation transports by the literal
ambient conjugation map. -/
theorem markedNativeRow_conjugate_centralizer (r : Fin 2) (g : Model) :
    centralizer ((markedNativeRow r).map (MulAut.conj g).toMonoidHom : Set Model) =
      (nativeEight r).map (MulAut.conj g).toMonoidHom := by
  exact (map_centralizer_equiv (markedNativeRow r : Set Model) (MulAut.conj g)).symm.trans
    (congrArg (fun C : Subgroup Model => C.map (MulAut.conj g).toMonoidHom)
      (markedNativeRow_centralizer r))

theorem primedNativeRow_conjugate_centralizer (g : Model) :
    centralizer (primedNativeRow.map (MulAut.conj g).toMonoidHom : Set Model) =
      (nativeEight 1).map (MulAut.conj g).toMonoidHom := by
  exact (map_centralizer_equiv (primedNativeRow : Set Model) (MulAut.conj g)).symm.trans
    (congrArg (fun C : Subgroup Model => C.map (MulAut.conj g).toMonoidHom)
      primedNativeRow_centralizer)

theorem markedNativeRow_conjugate_normalizer_le (r : Fin 2) (g : Model) :
    normalizer ((markedNativeRow r).map (MulAut.conj g).toMonoidHom : Set Model) ≤
      normalizer ((nativeEight r).map (MulAut.conj g).toMonoidHom : Set Model) := by
  rw [← markedNativeRow_conjugate_centralizer]
  exact normalizer_le_normalizer_centralizer _

theorem primedNativeRow_conjugate_normalizer_le (g : Model) :
    normalizer (primedNativeRow.map (MulAut.conj g).toMonoidHom : Set Model) ≤
      normalizer ((nativeEight 1).map (MulAut.conj g).toMonoidHom : Set Model) := by
  rw [← primedNativeRow_conjugate_centralizer]
  exact normalizer_le_normalizer_centralizer _

/-- All elementary-eight properties of the full centralizer of a displayed
unprimed row, with the intrinsic form and ambient centralizer conventions. -/
theorem markedNativeRow_centralizer_properties (r : Fin 2) :
    ∃ _h : IsElementaryAbelian 2 (centralizer (markedNativeRow r : Set Model)),
      Nat.card (centralizer (markedNativeRow r : Set Model)) = 256 ∧
      (LargeCenterRadicals.OuterHalf.intrinsicElementaryForm
        (centralizer (markedNativeRow r : Set Model))).Nondegenerate ∧
      centralizer (centralizer (markedNativeRow r : Set Model) : Set Model) =
        centralizer (markedNativeRow r : Set Model) := by
  rw [markedNativeRow_centralizer]
  exact ⟨inferInstance,nativeEight_card r,nativeEight_nondegenerate r,nativeEight_self_centralizing r⟩

theorem primedNativeRow_centralizer_properties :
    ∃ _h : IsElementaryAbelian 2 (centralizer (primedNativeRow : Set Model)),
      Nat.card (centralizer (primedNativeRow : Set Model)) = 256 ∧
      (LargeCenterRadicals.OuterHalf.intrinsicElementaryForm
        (centralizer (primedNativeRow : Set Model))).Nondegenerate ∧
      centralizer (centralizer (primedNativeRow : Set Model) : Set Model) =
        centralizer (primedNativeRow : Set Model) := by
  rw [primedNativeRow_centralizer]
  exact ⟨inferInstance,nativeEight_card 1,nativeEight_nondegenerate 1,nativeEight_self_centralizing 1⟩


/-- The specified signed primed row and both unprimed rows have a common
native centralizer representative under the displayed conjugators. -/
theorem markedNativeRow_fused_centralizer (r : Fin 2) :
    centralizer ((markedNativeRow r).map (MulAut.conj (rowFusion r)).toMonoidHom : Set Model) =
      nativeEight 1 := by
  rw [markedNativeRow_conjugate_centralizer,rowFusion_eight]

private theorem conjugation_comp (a b : Model) :
    (MulAut.conj (a * b)).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
  ext x
  simp only [MulEquiv.coe_toMonoidHom,MonoidHom.comp_apply,MulAut.conj_apply,mul_inv_rev,mul_assoc]

/-- Arbitrary elementary lifts of either whole unprimed quotient row have
the same native centralizer conjugacy class. The conjugator keeps both the
bounded source-marking correction and the certified fusion word. -/
theorem selected_row_fused_centralizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXL : X ≤ L) (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide))) :
    ∃ k : Fin 2048, (k = 0 ∨ k = Sections.twist r) ∧
      (centralizer (X : Set Model)).map
        (MulAut.conj (rowFusion r * ((nativeMask k.val : L) : Model))).toMonoidHom = nativeEight 1 := by
  obtain ⟨k,hk,he⟩ := Sections.ambient_centralizer_conjugacy X hXL hs r hrow
  refine ⟨k,hk,?_⟩
  rw [conjugation_comp,← Subgroup.map_map,he,rowFusion_eight]

/-- The literal image of the whole original normalizer lies in the common
native eight normalizer, with no generator-level normalizer assumption. -/
theorem selected_row_fused_normalizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXL : X ≤ L) (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide))) :
    ∃ k : Fin 2048, (k = 0 ∨ k = Sections.twist r) ∧
      let g := rowFusion r * ((nativeMask k.val : L) : Model)
      (centralizer (X : Set Model)).map (MulAut.conj g).toMonoidHom = nativeEight 1 ∧
      (normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom ≤
        normalizer (nativeEight 1 : Set Model) := by
  obtain ⟨k,hk,he⟩ := selected_row_fused_centralizer X hXL hs r hrow
  refine ⟨k,hk,he,?_⟩
  have h := Subgroup.map_mono (f := (MulAut.conj
    (rowFusion r * ((nativeMask k.val : L) : Model))).toMonoidHom)
    (normalizer_le_normalizer_centralizer X)
  rwa [map_normalizer_eq_of_bijective (centralizer (X : Set Model)) (MulAut.conj _).bijective,he] at h

/-- At an actual maximal two-local the entire original normalizer, after
the same explicit conjugation, equals the common native eight normalizer. -/
theorem selected_row_fused_maximal_normalizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXL : X ≤ L) (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide)))
    (hM : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ k : Fin 2048, (k = 0 ∨ k = Sections.twist r) ∧
      (normalizer (X : Set Model)).map
        (MulAut.conj (rowFusion r * ((nativeMask k.val : L) : Model))).toMonoidHom =
          normalizer (nativeEight 1 : Set Model) := by
  obtain ⟨k,hk,he⟩ := selected_row_fused_centralizer X hXL hs r hrow
  refine ⟨k,hk,?_⟩
  rw [selected_row_maximal_normalizer X hXL hs r hrow hM,
    map_normalizer_eq_of_bijective _ (MulAut.conj _).bijective,he]

private theorem nondegenerate_of_conjugate_eight
    (C : Subgroup Model) [IsElementaryAbelian 2 C] (r : Fin 2) (g : Model)
    (hg : C.map (MulAut.conj g).toMonoidHom = nativeEight r) :
    (LargeCenterRadicals.OuterHalf.intrinsicElementaryForm C).Nondegenerate := by
  let f : C ≃* nativeEight r :=
    (C.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hg)
  have hf (x : C) : (f x : Model) = MulAut.conj g x := rfl
  have ht := LargeCenterRadicals.OuterHalf.intrinsicElementaryForm_equiv C
    (nativeEight r) (MulAut.conj g) f hf
  have hsep : (LargeCenterRadicals.OuterHalf.intrinsicElementaryForm C).SeparatingLeft := by
    intro x hx
    have hz : Additive.ofMul (f x.toMul) = 0 := by
      apply (nativeEight_nondegenerate r).1
      intro y
      have h := ht x (Additive.ofMul (f.symm y.toMul))
      simpa only [toMul_ofMul,MulEquiv.apply_symm_apply,ofMul_toMul] using
        h.trans (hx _)
    apply Additive.toMul.injective
    apply f.injective
    change f x.toMul = f 1
    exact (congrArg Additive.toMul hz).trans (map_one f).symm
  refine ⟨hsep,?_⟩
  intro y hy
  apply hsep y
  intro x
  rw [(LargeCenterRadicals.OuterHalf.intrinsicElementaryForm_isSymm C).eq]
  exact hy x

/-- Nondegeneracy for every selected unprimed source row follows from the
native lift classification, rather than from a supplied choice of form. -/
theorem selected_row_centralizer_nondegenerate (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXL : X ≤ L) (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide))) :
    letI := selected_ambient_centralizer_elementary X hXL hs r hrow
    (LargeCenterRadicals.OuterHalf.intrinsicElementaryForm
      (centralizer (X : Set Model))).Nondegenerate := by
  let := selected_ambient_centralizer_elementary X hXL hs r hrow
  obtain ⟨k,_,he⟩ := Sections.ambient_centralizer_conjugacy X hXL hs r hrow
  exact nondegenerate_of_conjugate_eight _ r _ he

/-- Arbitrary radical restriction keeps the original normalizer, placement
and local core maps; the containing local is now identified with the common
native eight normalizer by the actual source-row conjugator. -/
theorem selected_row_fused_radical_restriction (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide)))
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ k : Fin 2048, (k = 0 ∨ k = Sections.twist r) ∧
      let C := centralizer (X : Set Model)
      let M := normalizer (C : Set Model)
      let g := rowFusion r * ((nativeMask k.val : L) : Model)
      M.map (MulAut.conj g).toMonoidHom = normalizer (nativeEight 1 : Set Model) ∧
      C ≤ P ∧ IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  obtain ⟨k,hk,he⟩ := selected_row_fused_centralizer X hXL hs r hrow
  refine ⟨k,hk,?_,selected_row_radical_restriction P X hP hXL hs r hrow hNX⟩
  rw [map_normalizer_eq_of_bijective _ (MulAut.conj _).bijective,he]

/-- An arbitrary elementary lift of the literal primed image has an elementary
full ambient centralizer. This uses the native lift equations, without an
assumption about the centralizer. -/
theorem selected_primed_centralizer_elementary (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (hrow : (X.subgroupOf L).map π = pairRowImage 3) :
    IsElementaryAbelian 2 (centralizer (X : Set Model)) := by
  obtain ⟨k,_,he⟩ := Sections.primed_ambient_centralizer_conjugacy X hXL hs hrow
  let g : Model := ((nativeMask k.val : L) : Model)
  let f : centralizer (X : Set Model) ≃* nativeEight 1 :=
    ((centralizer (X : Set Model)).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
        (MulEquiv.subgroupCongr he)
  exact IsElementaryAbelian.of_injective f.toMonoidHom f.injective

theorem selected_primed_centralizer_card (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (hrow : (X.subgroupOf L).map π = pairRowImage 3) :
    Nat.card (centralizer (X : Set Model)) = 256 := by
  obtain ⟨k,_,he⟩ := Sections.primed_ambient_centralizer_conjugacy X hXL hs hrow
  rw [← card_map_of_injective
    (K := centralizer (X : Set Model))
    (f := (MulAut.conj ((nativeMask k.val : L) : Model)).toMonoidHom)
    (MulAut.conj ((nativeMask k.val : L) : Model)).injective, he, nativeEight_card]

theorem selected_primed_centralizer_nondegenerate (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (hrow : (X.subgroupOf L).map π = pairRowImage 3) :
    letI := selected_primed_centralizer_elementary X hXL hs hrow
    (LargeCenterRadicals.OuterHalf.intrinsicElementaryForm
      (centralizer (X : Set Model))).Nondegenerate := by
  let := selected_primed_centralizer_elementary X hXL hs hrow
  obtain ⟨k,_,he⟩ := Sections.primed_ambient_centralizer_conjugacy X hXL hs hrow
  exact nondegenerate_of_conjugate_eight _ 1 _ he

theorem selected_primed_centralizer_self_centralizing (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (hrow : (X.subgroupOf L).map π = pairRowImage 3) :
    centralizer (centralizer (X : Set Model) : Set Model) = centralizer (X : Set Model) := by
  let := selected_primed_centralizer_elementary X hXL hs hrow
  exact le_antisymm (centralizer_le X.le_centralizer) (centralizer _).le_centralizer

/-- The complete primed-row normalizer embeds into the common eight normalizer
under the same bounded native kernel conjugation. -/
theorem selected_primed_fused_normalizer (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (hrow : (X.subgroupOf L).map π = pairRowImage 3) :
    ∃ k : Fin 2048, (k = 0 ∨ k = 16) ∧
      let g : Model := ((nativeMask k.val : L) : Model)
      (centralizer (X : Set Model)).map (MulAut.conj g).toMonoidHom = nativeEight 1 ∧
      (normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom ≤
        normalizer (nativeEight 1 : Set Model) := by
  obtain ⟨k,hk,he⟩ := Sections.primed_ambient_centralizer_conjugacy X hXL hs hrow
  refine ⟨k,hk,he,?_⟩
  have h := Subgroup.map_mono (f :=
    (MulAut.conj ((nativeMask k.val : L) : Model)).toMonoidHom)
    (normalizer_le_normalizer_centralizer X)
  rwa [map_normalizer_eq_of_bijective (centralizer (X : Set Model)) (MulAut.conj _).bijective,he] at h

/-- Maximal two-local equality for the arbitrary selected primed row. -/
theorem selected_primed_maximal_normalizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXL : X ≤ L) (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (hrow : (X.subgroupOf L).map π = pairRowImage 3)
    (hM : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    normalizer (X : Set Model) = normalizer (centralizer (X : Set Model) : Set Model) := by
  let C := centralizer (X : Set Model)
  let : IsElementaryAbelian 2 C := selected_primed_centralizer_elementary X hXL hs hrow
  have hC : C ≠ ⊥ := by
    intro he
    have hc := selected_primed_centralizer_card X hXL hs hrow
    change Nat.card C = 256 at hc
    rw [he, card_bot] at hc
    contradiction
  exact hM.eq_of_le ⟨C,hC,IsElementaryAbelian.isPGroup 2 C,rfl⟩
    (normalizer_le_normalizer_centralizer X)

/-- Restriction of an arbitrary radical to the calculated eight normalizer
preserves the entire original normalizer and both literal local-core maps.
This is the centralizer enlargement stage, before the isotropic reduction. -/
theorem selected_primed_radical_restriction (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (hrow : (X.subgroupOf L).map π = pairRowImage 3)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    let C := centralizer (X : Set Model)
    let M := normalizer (C : Set Model)
    C ≤ P ∧ IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  dsimp only
  let C := centralizer (X : Set Model)
  let M := normalizer (C : Set Model)
  let : IsElementaryAbelian 2 C := selected_primed_centralizer_elementary X hXL hs hrow
  have hC : C ≠ ⊥ := by
    intro he
    have hc := selected_primed_centralizer_card X hXL hs hrow
    change Nat.card C = 256 at hc
    rw [he, card_bot] at hc
    contradiction
  have hNM : normalizer (P : Set Model) ≤ M :=
    hNX.trans (normalizer_le_normalizer_centralizer X)
  have hPM := P.le_normalizer.trans hNM
  have hCP : C ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
    P C hP.isPGroup (IsElementaryAbelian.isPGroup 2 C) hP.2.le hNM
  have hN := hNM.trans M.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf M hPM hN
  refine ⟨hCP,⟨C,hC,IsElementaryAbelian.isPGroup 2 C,rfl⟩,hNM,hPM,?_,
    hP.subgroupOf_of_normalizer_normalizes M hPM hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPM,map_subgroupOf_eq_of_le hNM]
  · rw [hcore,map_subgroupOf_eq_of_le hPM]


/-- A concrete nontrivial zero-form sixteen in each selected unprimed full
centralizer, obtained with the same literal correction and fusion maps.
Its invariance under the whole normalizer is still a separate calculation. -/
theorem selected_row_zero_form_sixteen (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide))) :
    ∃ Y : Subgroup Model, Y ≤ centralizer (X : Set Model) ∧ Y ≠ ⊥ ∧
      ∃ _h : IsElementaryAbelian 2 Y, Nat.card Y = 16 ∧
        LargeCenterRadicals.OuterHalf.intrinsicElementaryForm Y = 0 := by
  obtain ⟨k,_,he⟩ := selected_row_fused_centralizer X hXL hs r hrow
  exact exists_zero_form_of_fused_eight _ _ he

/-- The same native zero-form sixteen for an arbitrary lift of the primed
selected image, retaining its full ambient centralizer. -/
theorem selected_primed_zero_form_sixteen (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (hrow : (X.subgroupOf L).map π = pairRowImage 3) :
    ∃ Y : Subgroup Model, Y ≤ centralizer (X : Set Model) ∧ Y ≠ ⊥ ∧
      ∃ _h : IsElementaryAbelian 2 Y, Nat.card Y = 16 ∧
        LargeCenterRadicals.OuterHalf.intrinsicElementaryForm Y = 0 := by
  obtain ⟨k,_,he⟩ := Sections.primed_ambient_centralizer_conjugacy X hXL hs hrow
  exact exists_zero_form_of_fused_eight _ _ he

end Janko4.LocalStructure.ElementaryEightGeometry
