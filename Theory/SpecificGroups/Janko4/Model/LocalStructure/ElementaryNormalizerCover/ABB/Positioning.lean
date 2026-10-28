module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ABB.Enlargement
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.PairIdentification
public import Theory.Mathieu.M24.ChapterHStabilizers.PairInvolutions
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.Applications

/-!
# Fixed-point-free ABB(3) positioning and enlargement

The fixed-point-free outer involution can be conjugated inside the marked
seed-pair stabilizer to the canonical Figure 2(c) product. The full ambient
centralizer and normalizer are transported by the same literal conjugator.
The canonical octad-incidence calculation then supplies a nontrivial
zero-form subgroup normalized by the whole original normalizer. This is the
weak ABB(3) enlargement used before the remaining pure-2A and box cases.

Source: Kleidman--Wilson (1988), Section 2.3, printed pp.492--493. The
M24 pair-class transport, star relabelling, kernel labels and literal
normalizer maps are inherited from the certified native model.
-/

set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open scoped Pointwise IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ABB
open Cardinality QuotientCount.Image KernelCount
open LinearFive InvolutionCentralizers.Second ElementaryEightGeometry
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open LargeCenterRadicals.OuterHalf M22Images.KernelAction
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis
private theorem pair_class (q : starPairStabilizer) (hq : orderOf q.val = 2)
    (hfree : ∀ i : Fin 24, q.val.val i ≠ i) :
    IsConj (Sporadic.Mathieu.M24ChapterHStabilizers.pairRepresentative false)
      (starPairEquivNative q) := by
  let u := starPairEquivNative q
  have hno (i : Fin 24) : u.val.val i ≠ i := by
    obtain ⟨j,rfl⟩ := pairMarking.surjective i
    intro he
    have h := markedStarEquiv_apply q.val j
    change u.val.val (pairMarking j) = pairMarking (q.val.val j) at h
    exact hfree j (pairMarking.injective (h.symm.trans he))
  have ho : u.val ∉ MathieuCode.m22PointwisePairStabilizer := by
    intro hp
    exact hno 0 hp.1
  have hclass : IsConj M24InvolutionCentralizers.involution2B u.val := by
    have horder : orderOf u.val = 2 := (markedStarEquiv.orderOf_eq q.val).trans hq
    rcases M24InvolutionCentralizers.involution_classes u.val horder with h | h
    · have hB := M24ChapterHStabilizers.class2A_fixed_octad h
      have hn : (M24ChapterHStabilizers.fixedPoints u.val).Nonempty :=
        Finset.card_pos.mp (by rw [m24Blocks_card _ hB]; decide)
      obtain ⟨i,hi⟩ := hn
      exact (hno i ((M24ChapterHStabilizers.mem_fixedPoints _ _).mp hi)).elim
    · exact h
  exact M24ChapterHStabilizers.pair_fusion_of_ambient false u ho hclass

/-- Every fixed-point-free involution preserving the seed pair is conjugate
to the canonical ABB pair inside its original marked pair stabilizer. -/
theorem free_pair_positioning (q : starPairStabilizer) (hq : orderOf q.val = 2)
    (hfree : ∀ i : Fin 24, q.val.val i ≠ i) :
    ∃ g : starPairStabilizer, MulAut.conj g.val freePair = q.val := by
  have hp : freePair ∈ starPairStabilizer := by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro i hi
    have hi' : i = 0 ∨ i = 1 := by simpa [starPair] using hi
    rcases hi' with rfl | rfl <;> change _ ∈ ({0,1} : Finset (Fin 24)) <;> decide +kernel
  let p : starPairStabilizer := ⟨freePair,hp⟩
  have hp2 : orderOf p.val = 2 := orderOf_eq_prime freePair_square (by
    intro h
    have he := congrArg (fun x : StarGroup => x.val 0) h
    exact freePair_fixed_free 0 he)
  have he : IsConj p q := by
    have hh := starPairEquivNative.symm.toMonoidHom.map_isConj
      ((pair_class p hp2 freePair_fixed_free).symm.trans (pair_class q hq hfree))
    simpa only [MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply] using hh
  obtain ⟨g,hg⟩ := isConj_iff.mp he
  exact ⟨g,congrArg Subtype.val hg⟩

/-- Position the entire elementary group while keeping its original second
involution and all full centralizer/normalizer conjugation maps. -/
theorem source_free_pair_positioning (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (z : InvolutionCentralizers.Second.Local) (hz : (z : Model) ∈ X)
    (hfree : ∀ i : Fin 24, (starHom z).val i ≠ i) :
    ∃ g : localCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
      Y ≤ InvolutionCentralizers.Second.Local ∧ (seed : Model) ∈ Y ∧
      freePair ∈ (Y.subgroupOf InvolutionCentralizers.Second.Local).map starHom ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)⁻¹).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)⁻¹).toMonoidHom := by
  have hXL : X ≤ InvolutionCentralizers.Second.Local := X.le_centralizer.trans
    ((centralizer_le (Set.singleton_subset_iff.mpr hs)).trans ambient_le_max1)
  have hzc : z ∈ localCentralizer := by
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact congrArg (fun a : X => (a : Model)) (mul_comm (⟨z,hz⟩ : X) ⟨seed,hs⟩)
  have hpair : starHom z ∈ starPairStabilizer := (mem_localCentralizer_iff_star z).mp hzc
  have hz2 : z ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : Model) hz)
  have hq2 : orderOf (starHom z) = 2 := orderOf_eq_prime (by rw [← map_pow,hz2,map_one]) (by
    intro he
    exact hfree 0 (congrArg (fun p : StarGroup => p.val 0) he))
  obtain ⟨u,hu⟩ := free_pair_positioning ⟨starHom z,hpair⟩ hq2 hfree
  obtain ⟨g,hg⟩ := toStarPair_surjective u
  have hg' : starHom g.val = u.val := congrArg Subtype.val hg
  let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
  refine ⟨g,?_,?_,?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using
      InvolutionCentralizers.Second.Local.mul_mem (InvolutionCentralizers.Second.Local.mul_mem (InvolutionCentralizers.Second.Local.inv_mem g.val.property) (hXL hx)) g.val.property
  · have hc := congrArg (fun a : InvolutionCentralizers.Second.Local => (a : Model))
      (mem_centralizer_singleton_iff.mp g.property)
    have he : MulAut.conj (g.val : Model)⁻¹ (seed : Model) = seed := by
      change (g.val : Model) * (seed : Model) = (seed : Model) * g.val at hc
      change (g.val : Model)⁻¹ * seed * ((g.val : Model)⁻¹)⁻¹ = _
      rw [inv_inv,mul_assoc,← hc,inv_mul_cancel_left]
    exact he ▸ mem_map_of_mem (MulAut.conj (g.val : Model)⁻¹).toMonoidHom hs
  · let z' : InvolutionCentralizers.Second.Local := g.val⁻¹ * z * g.val
    have hz' : (z' : Model) ∈ Y := mem_map.mpr ⟨z,hz,by simp [z',mul_assoc]⟩
    have he : starHom z' = freePair := by
      dsimp only [z']
      have hu' : (MulAut.conj (u : StarGroup)) freePair =
          starHom z := by simpa only [Subtype.coe_mk] using hu
      rw [map_mul,map_mul,map_inv,hg',← hu']
      simp [mul_assoc]
    exact he ▸ mem_map_of_mem starHom (show z' ∈ Y.subgroupOf InvolutionCentralizers.Second.Local from hz')
  · exact (map_centralizer_equiv (X : Set Model) (MulAut.conj (g.val : Model)⁻¹)).symm
  · exact (map_equiv_normalizer_eq X (MulAut.conj (g.val : Model)⁻¹)).symm

/-- Every fixed-point-free outer image yields a nontrivial zero-form witness
invariant under the whole elementary normalizer, in its original position. -/
theorem free_image_zero_enlargement (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (z : InvolutionCentralizers.Second.Local) (hz : (z : Model) ∈ X)
    (hfree : ∀ i : Fin 24, (starHom z).val i ≠ i) :
    ∃ W : Subgroup Model, W ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 W,
      intrinsicElementaryForm W = 0 ∧
      normalizer (X : Set Model) ≤ normalizer (W : Set Model) := by
  obtain ⟨g,hYL,hys,hq,hc,hn⟩ := source_free_pair_positioning X hs z hz hfree
  let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  obtain ⟨hW,hzero,hNW⟩ := source_zeroWitness Y hys hq
  let W := (NonsingularC.zeroWitness Y).map (MulAut.conj (g.val : Model)).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hne : W ≠ ⊥ := fun he => hW
    ((map_eq_bot_iff_of_injective _ (MulAut.conj (g.val : Model)).injective).mp he)
  refine ⟨W,hne,inferInstance,
    intrinsicForm_zero_map _ W (MulAut.conj (g.val : Model)) rfl hzero,?_⟩
  have ht := map_mono (f := (MulAut.conj (g.val : Model)).toMonoidHom) hNW
  rw [hn,map_map] at ht
  have he : (MulAut.conj (g.val : Model)).toMonoidHom.comp
      (MulAut.conj (g.val : Model)⁻¹).toMonoidHom = MonoidHom.id Model := by
    ext x
    simp [mul_assoc]
  rw [he,map_id,map_equiv_normalizer_eq] at ht
  exact ht

/-- The ABB enlargement discharges the fixed-point-free alternative in the
arbitrary nonsingular normalizer reduction. The remaining geometric inputs
are precisely the box image and the fixed native eight-normalizer. -/
theorem nonsingular_normalizer_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hX : X ≠ ⊥) (hform : (intrinsicElementaryForm X).Nondegenerate) :
    (∃ g : Model,
      let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
      Y ≤ InvolutionCentralizers.Second.Local ∧ (seed : Model) ∈ Y ∧
        pairPermutation ∈ (Y.subgroupOf InvolutionCentralizers.Second.Local).map starHom ∧
        (Y.subgroupOf InvolutionCentralizers.Second.Local).map starHom ≤ NonsingularImages.boxImage) ∨
    (∃ Z : Subgroup Model, Z ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 Z,
      intrinsicElementaryForm Z = 0 ∧ normalizer (X : Set Model) ≤ normalizer (Z : Set Model)) ∨
    (∃ g : Model, (centralizer (X : Set Model)).map (MulAut.conj g).toMonoidHom = nativeEight 1 ∧
      (normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom ≤
        normalizer (nativeEight 1 : Set Model)) := by
  rcases NonsingularImages.nonsingular_normalizer_reduction X hX hform with
    ⟨g,hYL,hys,hfree | hbox⟩ | hother
  · obtain ⟨z,hz,_,hfree⟩ := hfree
    let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
    let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
    obtain ⟨Z,hZ,hZe,hzero,hNZ⟩ := free_image_zero_enlargement Y hys z hz hfree
    let : IsElementaryAbelian 2 Z := hZe
    let W := Z.map (MulAut.conj g).toMonoidHom
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
    have hW : W ≠ ⊥ := fun h => hZ
      ((map_eq_bot_iff_of_injective Z (MulAut.conj g).injective).mp h)
    refine Or.inr (Or.inl ⟨W,hW,inferInstance,intrinsicForm_zero_map Z W (MulAut.conj g) rfl hzero,?_⟩)
    have ht := map_mono (f := (MulAut.conj g).toMonoidHom) hNZ
    rw [map_equiv_normalizer_eq] at ht
    have he : Y.map (MulAut.conj g).toMonoidHom = X := by
      rw [map_map]
      have hf : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
          MonoidHom.id Model := by ext x; simp [mul_assoc]
      rw [hf,map_id]
    rw [he, map_equiv_normalizer_eq] at ht
    exact ht
  · exact Or.inl ⟨g,hYL,hys,hbox⟩
  · exact Or.inr hother


end Janko4.LocalStructure.ElementaryNormalizerCover.ABB
