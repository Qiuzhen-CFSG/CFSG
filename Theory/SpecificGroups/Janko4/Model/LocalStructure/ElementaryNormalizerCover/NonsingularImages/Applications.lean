module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.NonsingularPositioning
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularCApplication
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Application
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.PairCharacter

/-!
# Normalizer applications of exhaustive exact-row selection

The five exact rows discharge the literal source premises of the existing
(c)/(c′) zero-form enlargement and the (b)/(d)/(d′) eight-centralizer results.
Every positioned elementary group therefore either has image in the box,
admits a nontrivial zero-form normalizer enlargement, or has its whole
centralizer fused to the common native elementary group of order 256.
All transports use the original ambient conjugator and `starHom`.

The maximal TWO-local and radical consumers preserve full normalizers and
literal restricted core maps. The box geometry and the invariant isotropic
subgroup of the eight-normalizer remain necessary for the final four-local
cover; these alternatives do not assume those remaining conclusions.
Source: Kleidman--Wilson (1988), Lemma 2.3.1 and Propositions 2.3.3--2.3.5.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages
open Cardinality.QuotientCount.Image
open ElementaryEightGeometry hiding Local
open InvolutionCentralizers.Second
open LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

private theorem conj_comp (a b : Model) :
    (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a*b)).toMonoidHom := by
  ext x
  simp [mul_assoc]

private theorem undo_conj (X : Subgroup Model) (g : Model) :
    (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X := by
  rw [map_map,conj_comp,mul_inv_cancel,map_one]
  change X.map (MonoidHom.id _) = X
  exact map_id X

private theorem exact_row_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXL : X ≤ Local) (hs : (seed : Model) ∈ X) (k : Fin 5)
    (hrow : (X.subgroupOf Local).map starHom = Refinement.exactRow k) :
    (∃ Z : Subgroup Model, Z ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 Z,
      intrinsicElementaryForm Z = 0 ∧ normalizer (X : Set Model) ≤ normalizer (Z : Set Model)) ∨
    (∃ g : Model, (centralizer (X : Set Model)).map (MulAut.conj g).toMonoidHom = nativeEight 1 ∧
      (normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom ≤
        normalizer (nativeEight 1 : Set Model)) := by
  have hwhole (r : Fin 2)
      (h : (X.subgroupOf Local).map starHom = pairRowImage (r.castLE (by decide))) :
      ∃ g : Model, (centralizer (X : Set Model)).map (MulAut.conj g).toMonoidHom = nativeEight 1 ∧
        (normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom ≤
          normalizer (nativeEight 1 : Set Model) := by
    obtain ⟨j,_,hc,hn⟩ := selected_row_fused_normalizer X hXL hs r
      (by simpa only [ElementaryEightGeometry.starHom_eq] using h)
    exact ⟨_,hc,hn⟩
  have hc (h : (X.subgroupOf Local).map starHom = NonsingularC.wholeImage ∨
      (X.subgroupOf Local).map starHom = NonsingularC.primedImage) :
      ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 Z,
        intrinsicElementaryForm Z = 0 ∧ normalizer (X : Set Model) ≤ normalizer (Z : Set Model) := by
    obtain ⟨_,hne,hzero,hn⟩ := NonsingularC.source_zeroWitness X hs h
    exact ⟨NonsingularC.zeroWitness X,hne,inferInstance,hzero,hn⟩
  fin_cases k
  · exact Or.inr (hwhole 0 hrow)
  · exact Or.inl (hc (Or.inl hrow))
  · exact Or.inr (hwhole 1 hrow)
  · exact Or.inl (hc (Or.inr hrow))
  · change (X.subgroupOf Local).map starHom = pairRowImage 3 at hrow
    obtain ⟨j,_,he,hn⟩ := selected_primed_fused_normalizer X hXL hs
      (by simpa only [ElementaryEightGeometry.starHom_eq] using hrow)
    exact Or.inr ⟨_,he,hn⟩

/-- Exhaustive normalizer reduction at the original seed/pair boundary.
The first alternative retains the actual box-positioning conjugator; the other
two alternatives already refer to the original whole ambient normalizer. -/
theorem source_normalizer_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hp : pairPermutation ∈ (X.subgroupOf Local).map starHom) :
    (∃ g : localCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧ pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
        (Y.subgroupOf Local).map starHom ≤ boxImage) ∨
    (∃ Z : Subgroup Model, Z ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 Z,
      intrinsicElementaryForm Z = 0 ∧ normalizer (X : Set Model) ≤ normalizer (Z : Set Model)) ∨
    (∃ g : Model, (centralizer (X : Set Model)).map (MulAut.conj g).toMonoidHom = nativeEight 1 ∧
      (normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom ≤
        normalizer (nativeEight 1 : Set Model)) := by
  obtain ⟨g,_,hYL,hys,hyp,hrow,hc,hn⟩ := source_exact_row_positioning X hs hp
  let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  rcases hrow with hbox | ⟨k,hk⟩
  · exact Or.inl ⟨g,hYL,hys,hyp,hbox⟩
  right
  rcases exact_row_reduction Y hYL hys k hk with ⟨Z,hZ,hZe,hzero,hNZ⟩ | ⟨u,hCu,hNu⟩
  · let : IsElementaryAbelian 2 Z := hZe
    let W := Z.map (MulAut.conj (g.val : Model)).toMonoidHom
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
    have hW : W ≠ ⊥ := fun h => hZ
      ((map_eq_bot_iff_of_injective Z (MulAut.conj (g.val : Model)).injective).mp h)
    refine Or.inl ⟨W,hW,inferInstance,
      intrinsicForm_zero_map Z W (MulAut.conj (g.val : Model)) rfl hzero,?_⟩
    have h := map_mono (f := (MulAut.conj (g.val : Model)).toMonoidHom) hNZ
    rw [hn,undo_conj] at h
    rwa [map_equiv_normalizer_eq] at h
  · refine Or.inr ⟨u * (g.val : Model)⁻¹,?_,?_⟩
    · rwa [hc,map_map,conj_comp] at hCu
    · rwa [hn,map_map,conj_comp] at hNu

/-- A maximal TWO-local in a selected source row is a box normalizer,
a native E/F normalizer, a pure-2A normalizer, or a conjugate of the common
eight-normalizer. The last alternative still needs invariant isotropic geometry. -/
theorem source_maximal_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hp : pairPermutation ∈ (X.subgroupOf Local).map starHom)
    (hM : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    (∃ g : localCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧ pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
        (Y.subgroupOf Local).map starHom ≤ boxImage) ∨
    (∃ g : Model, normalizer (X : Set Model) = LinearFive.M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) = max1.map (MulAut.conj g).toMonoidHom) ∨
    (∃ Z : Subgroup Model, Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧
      normalizer (X : Set Model) = normalizer (Z : Set Model) ∧ ∀ z ∈ Z, z ≠ 1 → IsConj a z) ∨
    (∃ g : Model, normalizer (X : Set Model) =
      (normalizer (nativeEight 1 : Set Model)).map (MulAut.conj g).toMonoidHom) := by
  rcases source_normalizer_reduction X hs hp with hbox | ⟨Z,hZ,hZe,hzero,hNZ⟩ | ⟨g,_,hNg⟩
  · exact Or.inl hbox
  · let : IsElementaryAbelian 2 Z := hZe
    have he := hM.eq_of_le ⟨Z,hZ,IsElementaryAbelian.isPGroup 2 Z,rfl⟩ hNZ
    by_cases hpure : ∀ z ∈ Z, z ≠ 1 → IsConj a z
    · exact Or.inr (Or.inr (Or.inl ⟨Z,hZ,hZe,he,hpure⟩))
    rcases M22Images.ZeroFormMaximal.maximal_mixed_zero_form Z _ hzero hpure hM he with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · have hE : nativeEight 1 ≠ ⊥ := by
      intro h
      have hc := nativeEight_card 1
      rw [h,card_bot] at hc
      contradiction
    have hlocal : IsTwoLocal (normalizer (nativeEight 1 : Set Model)) :=
      ⟨nativeEight 1,hE,IsElementaryAbelian.isPGroup 2 _,rfl⟩
    have hle := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hNg
    have hid : ((normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom = normalizer (X : Set Model) := by
      simpa only [inv_inv] using undo_conj (normalizer (X : Set Model)) g⁻¹
    rw [hid] at hle
    exact Or.inr (Or.inr (Or.inr ⟨g⁻¹,hM.eq_of_le (hlocal.map_equiv (MulAut.conj g⁻¹)) hle⟩))

/-- Radical restriction after exhaustive row selection. Both possible
containing normalizers have their literal local core maps, and their
nontrivial elementary witness is contained in the same original radical. -/
theorem source_radical_restriction (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hs : (seed : Model) ∈ X)
    (hp : pairPermutation ∈ (X.subgroupOf Local).map starHom)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    (∃ g : localCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧ pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
        (Y.subgroupOf Local).map starHom ≤ boxImage) ∨
    (∃ Z : Subgroup Model, ∃ _ : IsElementaryAbelian 2 Z,
      let H := normalizer (Z : Set Model)
      Z ≠ ⊥ ∧ Z ≤ P ∧
      (intrinsicElementaryForm Z = 0 ∨ ∃ g : Model,
        Z.map (MulAut.conj g).toMonoidHom = nativeEight 1) ∧
      IsTwoLocal H ∧ normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P) := by
  have restrict (Z : Subgroup Model) [IsElementaryAbelian 2 Z] (hZ : Z ≠ ⊥)
      (ht : intrinsicElementaryForm Z = 0 ∨ ∃ g : Model,
        Z.map (MulAut.conj g).toMonoidHom = nativeEight 1)
      (hn : normalizer (P : Set Model) ≤ normalizer (Z : Set Model)) :
      Z ≤ P ∧ (intrinsicElementaryForm Z = 0 ∨ ∃ g : Model,
        Z.map (MulAut.conj g).toMonoidHom = nativeEight 1) ∧
        IsTwoLocal (normalizer (Z : Set Model)) := by
    exact ⟨le_of_normalizer_le_normalizer_of_pCore_normalizer_le P Z hP.isPGroup
      (IsElementaryAbelian.isPGroup 2 Z) hP.2.le hn,ht,
      ⟨Z,hZ,IsElementaryAbelian.isPGroup 2 Z,rfl⟩⟩
  rcases source_normalizer_reduction X hs hp with hbox | ⟨Z,hZ,hZe,hzero,hn⟩ | ⟨g,hC,hN⟩
  · exact Or.inl hbox
  all_goals
    right
  · let : IsElementaryAbelian 2 Z := hZe
    have hNZ := hNX.trans hn
    obtain ⟨hZP,ht,hlocal⟩ := restrict Z hZ (Or.inl hzero) hNZ
    let H := normalizer (Z : Set Model)
    have hPH : P ≤ H := P.le_normalizer.trans hNZ
    have hnn := hNZ.trans H.le_normalizer
    have hc := hP.normalizer_core_subgroupOf H hPH hnn
    refine ⟨Z,inferInstance,hZ,hZP,ht,hlocal,hNZ,hPH,?_,
      hP.subgroupOf_of_normalizer_normalizes H hPH hnn,hc,?_⟩
    · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hNZ]
    · rw [hc,map_subgroupOf_eq_of_le hPH]
  · let C := centralizer (X : Set Model)
    let f : C ≃* nativeEight 1 :=
      (C.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
        (MulEquiv.subgroupCongr hC)
    let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective f.toMonoidHom f.injective
    have hCne : C ≠ ⊥ := by
      intro he
      change C.map _ = _ at hC
      rw [he,Subgroup.map_bot] at hC
      have hc := nativeEight_card 1
      rw [← hC,card_bot] at hc
      contradiction
    have hNC : normalizer (P : Set Model) ≤ normalizer (C : Set Model) :=
      hNX.trans (normalizer_le_normalizer_centralizer X)
    obtain ⟨hCP,ht,hlocal⟩ := restrict C hCne (Or.inr ⟨g,hC⟩) hNC
    let H := normalizer (C : Set Model)
    have hPH : P ≤ H := P.le_normalizer.trans hNC
    have hnn := hNC.trans H.le_normalizer
    have hc := hP.normalizer_core_subgroupOf H hPH hnn
    refine ⟨C,inferInstance,hCne,hCP,ht,hlocal,hNC,hPH,?_,
      hP.subgroupOf_of_normalizer_normalizes H hPH hnn,hc,?_⟩
    · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hNC]
    · rw [hc,map_subgroupOf_eq_of_le hPH]

/-- Source-wide normalizer reduction for a nontrivial nonsingular group.
The only geometric alternatives left are the actual fixed-point-free outer
pair, the box image, and the common eight-normalizer; the (c)/(c′) rows have
already supplied a nontrivial zero-form enlargement of the original N(X). -/
theorem nonsingular_normalizer_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hX : X ≠ ⊥) (hform : (intrinsicElementaryForm X).Nondegenerate) :
    (∃ g : Model,
      let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧
        ((∃ z : Local, (z : Model) ∈ Y ∧ orderOf (starHom z) = 2 ∧
            ∀ x : Fin 24, (starHom z).val x ≠ x) ∨
          (pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
            (Y.subgroupOf Local).map starHom ≤ boxImage))) ∨
    (∃ Z : Subgroup Model, Z ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 Z,
      intrinsicElementaryForm Z = 0 ∧ normalizer (X : Set Model) ≤ normalizer (Z : Set Model)) ∨
    (∃ g : Model, (centralizer (X : Set Model)).map (MulAut.conj g).toMonoidHom = nativeEight 1 ∧
      (normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom ≤
        normalizer (nativeEight 1 : Set Model)) := by
  obtain ⟨g,hYL,hys,hrow,hc,hn⟩ := nonsingular_source_positioning X hX hform
  let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  rcases hrow with hfree | ⟨hp,hbox | ⟨k,hk⟩⟩
  · exact Or.inl ⟨g,hYL,hys,Or.inl hfree⟩
  · exact Or.inl ⟨g,hYL,hys,Or.inr ⟨hp,hbox⟩⟩
  right
  rcases exact_row_reduction Y hYL hys k hk with ⟨Z,hZ,hZe,hzero,hNZ⟩ | ⟨u,hCu,hNu⟩
  · let : IsElementaryAbelian 2 Z := hZe
    let W := Z.map (MulAut.conj g).toMonoidHom
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
    have hW : W ≠ ⊥ := fun h => hZ
      ((map_eq_bot_iff_of_injective Z (MulAut.conj g).injective).mp h)
    refine Or.inl ⟨W,hW,inferInstance,intrinsicForm_zero_map Z W (MulAut.conj g) rfl hzero,?_⟩
    have h := map_mono (f := (MulAut.conj g).toMonoidHom) hNZ
    rw [hn,undo_conj] at h
    rwa [map_equiv_normalizer_eq] at h
  · refine Or.inr ⟨u * g⁻¹,?_,?_⟩
    · rwa [hc,map_map,conj_comp] at hCu
    · rwa [hn,map_map,conj_comp] at hNu

end Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages
