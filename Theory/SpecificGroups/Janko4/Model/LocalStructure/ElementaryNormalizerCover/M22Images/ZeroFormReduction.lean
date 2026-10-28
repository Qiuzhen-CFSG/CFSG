module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.SextetEnlargement

/-!
# Eliminating every sextet kernel size from the zero-form reduction

Choose, in the finite native group, a maximal zero-form elementary overgroup
whose normalizer contains the original normalizer. The canonical enlargement
of `SextetEnlargement` forces the tetrad involution into any sextet representative
of this chosen group. The checked native shears then give a pure-2A subgroup
preserved by its entire normalizer. Thus the exhaustive M22 image theorem
leaves only E/F normalizer coverage, the pure-2A branch, or the exceptional
order-sixteen lift. All coordinate changes use the original residual inclusion
and quotient, and the exceptional image and seed-line intersection stay literal.

No maximality premise is supplied to the exported reduction: finite maximal
choice constructs it here. The exceptional centralizer and its strict normalizer
enlargement, and the pure-2A normalizer classification, are still necessary to
finish Proposition 2.2.3. For groups larger than sixteen the exceptional branch
is impossible; the actual maximal-TWO-local and arbitrary-radical applications
retain full local normalizer and embedded two-core identities.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Proposition
2.2.3, p.491. This is a canonical-enlargement variant of its sextet reducibility
step, using the previously certified native Mathieu action and kernel shears.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.ZeroFormReduction
open Cardinality LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open M23Geometry SextetKernel SextetCentralizer SextetEnlargement
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

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

private def Saturated (X : Subgroup Model) : Prop :=
  ∀ (Z : Subgroup Model) (_ : IsElementaryAbelian 2 Z), X ≤ Z →
    intrinsicElementaryForm Z = 0 →
    normalizer (X : Set Model) ≤ normalizer (Z : Set Model) → Z ≤ X

private theorem exists_saturated (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0) :
    ∃ Y : Subgroup Model, X ≤ Y ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∃ _ : IsElementaryAbelian 2 Y, intrinsicElementaryForm Y = 0 ∧ Saturated Y := by
  let p : Subgroup Model → Prop := fun Y =>
    normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∃ _ : IsElementaryAbelian 2 Y, intrinsicElementaryForm Y = 0
  obtain ⟨Y,hXY,hY,hmax⟩ := Finite.exists_le_maximal (p := p)
    (show p X from ⟨le_rfl,inferInstance,hzero⟩)
  obtain ⟨hN,hYe,hzY⟩ := hY
  refine ⟨Y,hXY,hN,hYe,hzY,?_⟩
  intro Z hZe hYZ hzZ hNZ
  exact hmax ⟨hN.trans hNZ,hZe,hzZ⟩ hYZ

private theorem saturated_conjugate (X : Subgroup Model) (hX : Saturated X) (g : Model) :
    Saturated (X.map (MulAut.conj g).toMonoidHom) := by
  intro Z hZe hXZ hzZ hNZ
  let := hZe
  let Z0 := Z.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Z0 := IsElementaryAbelian.map _
  have hX0 : X ≤ Z0 := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hXZ
    rwa [conjugate_comp,inv_mul_cancel,conjugate_one] at hh
  have hN0 : normalizer (X : Set Model) ≤ normalizer (Z0 : Set Model) := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hNZ
    rwa [map_equiv_normalizer_eq,map_equiv_normalizer_eq,
      conjugate_comp,inv_mul_cancel,conjugate_one] at hh
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom)
    (hX Z0 inferInstance hX0 (intrinsicForm_zero_map Z Z0 (MulAut.conj g⁻¹) rfl hzZ) hN0)
  change (Z.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom ≤ _ at hh
  rwa [conjugate_comp,mul_inv_cancel,conjugate_one] at hh

private theorem pure_transfer (X Y : Subgroup Model) (g : Model)
    (hback : Y.map (MulAut.conj g).toMonoidHom = X)
    (hp : ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ Z ≤ Y ∧ IsElementaryAbelian 2 Z ∧
      normalizer (Y : Set Model) ≤ normalizer (Z : Set Model) ∧
      ∀ z ∈ Z, z ≠ 1 → IsConj a z) :
    ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ Z ≤ X ∧ IsElementaryAbelian 2 Z ∧
      normalizer (X : Set Model) ≤ normalizer (Z : Set Model) ∧
      ∀ z ∈ Z, z ≠ 1 → IsConj a z := by
  obtain ⟨Z,hZ,hZY,hZe,hNZ,hpure⟩ := hp
  let := hZe
  let Z0 := Z.map (MulAut.conj g).toMonoidHom
  have hZ0 : Z0 ≠ ⊥ := fun he => hZ
    ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp he)
  have hZ0X : Z0 ≤ X := hback ▸ map_mono hZY
  have hN : normalizer (X : Set Model) ≤ normalizer (Z0 : Set Model) := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hNZ
    rwa [map_equiv_normalizer_eq,map_equiv_normalizer_eq,hback] at hh
  refine ⟨Z0,hZ0,hZ0X,IsElementaryAbelian.map _,hN,?_⟩
  rintro z ⟨u,hu,rfl⟩ hz
  have hu1 : u ≠ 1 := by intro he; apply hz; rw [he,map_one]
  exact (hpure u hu hu1).trans (isConj_iff.mpr ⟨g,rfl⟩)

private theorem marked_saturated_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXM : X ≤ M) (himage : (X.subgroupOf M).map projection ≤ imageGroup)
    (hzero : intrinsicElementaryForm X = 0) (hsat : Saturated X)
    (t : Model) (htX : t ∈ X) (htE : t ∈ E) (ht2 : orderOf t = 2)
    (hnt : ¬ IsConj a t) :
    (∃ g : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom) ∨
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y ≤ X ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj a y) := by
  rcases SextetImages.subgroup_octad_or_pair ((X.subgroupOf M).map projection) himage with
      ⟨i,hi⟩ | ⟨k,hk⟩
  · exact Or.inl (mathieu_octad_image_normalizer_cover X hXM (SextetImages.octad i)
      hi hzero t htX ht2 hnt)
  · have ht1 : t ≠ 1 := by intro he; rw [he,orderOf_one] at ht2; contradiction
    have hCM : centralizer (X : Set Model) ≤ M :=
      (centralizer_le (Set.singleton_subset_iff.mpr htX)).trans
        (kernel_nonfirst_centralizer_le_max1 t htE ht1 hnt)
    rcases pure_or_larger X hXM himage k hk hCM hzero with h | ⟨hlt,hz,hn⟩
    · exact Or.inr h
    · exact (not_le_of_gt hlt (hsat _ inferInstance hlt.le hz hn)).elim

private theorem sextet_saturated_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0) (hseed : (seed : Model) ∈ X)
    (hsat : Saturated X) (n : residual)
    (hX : X ≤ (residualLift M22ChapterH.Sextet.innerTranslations).map
      (MulAut.conj (residualInclusion n)).toMonoidHom) :
    (∃ g : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom) ∨
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y ≤ X ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj a y) := by
  let g := residualInclusion n
  let A := X.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hA : A ≤ residualLift M22ChapterH.Sextet.innerTranslations := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hX
    rwa [conjugate_comp,inv_mul_cancel,conjugate_one] at hh
  obtain ⟨s,hYM,hYi⟩ := sextetLift_coordinates A hA
  let Y := A.map (MulAut.conj (s : Model)).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  let c : M := s * (residualToMathieu n)⁻¹
  have hc : (c : Model) = (s : Model) * g⁻¹ := by
    change (s : Model) * (residualToMathieu n : Model)⁻¹ = _
    rw [residualToMathieu_val]
  have hY : Y = X.map (MulAut.conj (c : Model)).toMonoidHom := by
    change (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj (s : Model)).toMonoidHom = _
    rw [conjugate_comp,hc]
  have hback : Y.map (MulAut.conj (c : Model)⁻¹).toMonoidHom = X := by
    rw [hY,conjugate_comp,inv_mul_cancel,conjugate_one]
  have hzY := intrinsicForm_zero_map X Y (MulAut.conj (c : Model)) hY.symm hzero
  have hsatY : Saturated Y := hY.symm ▸ saturated_conjugate X hsat c
  let t := (MulAut.conj (c : Model)) (seed : Model)
  have htY : t ∈ Y := hY.symm ▸ mem_map_of_mem (MulAut.conj (c : Model)).toMonoidHom hseed
  have hE : E.map (MulAut.conj (c : Model)).toMonoidHom = E := by
    apply mem_normalizer_iff_map_conj_eq.mp
    rw [embedded_localKernel_normalizer_eq_max1]
    exact c.property
  have hseedE : (seed : Model) ∈ E := by
    simpa only [show kernelValue 1 = seed from Simplicity.Max1Fusion.KernelOrbits.maskValue_one _ _]
      using kernelValue_mem_E 1
  have htE : t ∈ E := hE ▸ mem_map_of_mem (MulAut.conj (c : Model)).toMonoidHom hseedE
  have hnt : ¬ IsConj a t := by
    intro h
    exact first_not_isConj_second (h.trans (isConj_iff.mpr ⟨(c : Model)⁻¹,by simp [t,mul_assoc]⟩))
  rcases marked_saturated_reduction Y hYM hYi hzY hsatY t htY htE
      (((MulAut.conj (c : Model)).orderOf_eq _).trans seed_order) hnt with ⟨k,hk⟩ | hp
  · left
    refine ⟨(c : Model)⁻¹*k,?_⟩
    have transfer (H : Subgroup Model)
        (h : normalizer (Y : Set Model) ≤ H.map (MulAut.conj k).toMonoidHom) :
        normalizer (X : Set Model) ≤ H.map (MulAut.conj ((c : Model)⁻¹*k)).toMonoidHom := by
      have hh := map_mono (f := (MulAut.conj (c : Model)⁻¹).toMonoidHom) h
      rwa [map_equiv_normalizer_eq,hback,conjugate_comp] at hh
    exact hk.imp (transfer _) (transfer _)
  · exact Or.inr (pure_transfer X Y (c : Model)⁻¹ hback hp)

/-- The complete seeded zero-form image reduction has no remaining sextet
case or lower bound on the kernel intersection. The exceptional alternative
retains its literal residual maps and the original seed-line intersection. -/
theorem zero_form_seed_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0) (hseed : (seed : Model) ∈ X) :
    (∃ g : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom) ∨
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj a y) ∨
    (∃ Y : Subgroup Model, X ≤ Y ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∃ _ : IsElementaryAbelian 2 Y, intrinsicElementaryForm Y = 0 ∧
      Nat.card Y = 16 ∧ Y ⊓ embeddedKernel = zpowers (seed : Model) ∧
      ∃ n : residual,
        Y ≤ (residualLift (smallContainer 0)).map (MulAut.conj (residualInclusion n)).toMonoidHom ∧
        (Y.comap residualInclusion).map residualProjection =
          (smallContainer 0).map (MulAut.conj (residualProjection n)).toMonoidHom) := by
  obtain ⟨Y,hXY,hNY,hYe,hzY,hsat⟩ := exists_saturated X hzero
  let := hYe
  have hseedY := hXY hseed
  have hcases :
      (∃ g : Model,
        normalizer (Y : Set Model) ≤ M_F.map (MulAut.conj g).toMonoidHom ∨
        normalizer (Y : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom) ∨
      (∃ Z : Subgroup Model, Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧
        normalizer (Y : Set Model) ≤ normalizer (Z : Set Model) ∧
        ∀ z ∈ Z, z ≠ 1 → IsConj a z) ∨
      (Nat.card Y = 16 ∧ Y ⊓ embeddedKernel = zpowers (seed : Model) ∧
        ∃ n : residual, Y ≤ (residualLift (smallContainer 0)).map
          (MulAut.conj (residualInclusion n)).toMonoidHom ∧
        (Y.comap residualInclusion).map residualProjection =
          (smallContainer 0).map (MulAut.conj (residualProjection n)).toMonoidHom) := by
    rcases zero_form_seed_normalizer_or_exceptional Y hzY hseedY with h | ⟨n,hn⟩ | h
    · exact Or.inl h
    · rcases sextet_saturated_reduction Y hzY hseedY hsat n hn with h | ⟨Z,hZ,_,hZe,hNZ,hp⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨Z,hZ,hZe,hNZ,hp⟩)
    · exact Or.inr (Or.inr h)
  rcases hcases with ⟨g,hg⟩ | ⟨Z,hZ,hZe,hNZ,hp⟩ | he
  · exact Or.inl ⟨g,hg.imp (hNY.trans) (hNY.trans)⟩
  · exact Or.inr (Or.inl ⟨Z,hZ,hZe,hNY.trans hNZ,hp⟩)
  · exact Or.inr (Or.inr ⟨Y,hXY,hNY,hYe,hzY,he⟩)


/-- Move any actual second-class seed to the native one, retaining the
conjugator, exceptional lift and literal residual quotient. No kernel-size
assumption or remaining sextet alternative occurs. -/
theorem mixed_zero_form_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    (∃ g : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom) ∨
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj a y) ∨
    (∃ (g : Model) (Y : Subgroup Model), X ≤ Y.map (MulAut.conj g).toMonoidHom ∧
      normalizer (X : Set Model) ≤ normalizer (Y.map (MulAut.conj g).toMonoidHom : Set Model) ∧
      ∃ _ : IsElementaryAbelian 2 Y, intrinsicElementaryForm Y = 0 ∧
      Nat.card Y = 16 ∧ Y ⊓ embeddedKernel = zpowers (seed : Model) ∧
      ∃ n : residual,
        Y ≤ (residualLift (smallContainer 0)).map (MulAut.conj (residualInclusion n)).toMonoidHom ∧
        (Y.comap residualInclusion).map residualProjection =
          (smallContainer 0).map (MulAut.conj (residualProjection n)).toMonoidHom) := by
  obtain ⟨t,ht,_,_,htclass⟩ := nonpure_contains_second X hn
  have hsclass : IsConj (seed : Model) ((a * b * a * b * b)^5) :=
    ((OuterReduction.involution_isConj_of_max1_odd_index
      OuterReduction.max1_odd_index_unconditional seed_order).resolve_left
      Cardinality.LocalInvolutionCensus.not_isConj_z_t).symm
  obtain ⟨g,hg⟩ := isConj_iff.mp (hsclass.trans htclass)
  let A := X.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hseed : (seed : Model) ∈ A := by
    have he : (MulAut.conj g⁻¹) t = (seed : Model) := by
      rw [← hg]
      simp [mul_assoc]
    exact he ▸ mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom ht
  have hzeroA := intrinsicForm_zero_map X A (MulAut.conj g⁻¹) rfl hzero
  have hback : A.map (MulAut.conj g).toMonoidHom = X := by
    change (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X
    rw [conjugate_comp,mul_inv_cancel,conjugate_one]
  rcases zero_form_seed_reduction A hzeroA hseed with ⟨k,hk⟩ | ⟨Y,hY,hYe,hNY,hpure⟩ |
      ⟨Y,hAY,hNY,hYe,hzY,hYcard,hYker,n,hlift,himage⟩
  · left
    refine ⟨g*k,?_⟩
    have transfer (H : Subgroup Model)
        (h : normalizer (A : Set Model) ≤ H.map (MulAut.conj k).toMonoidHom) :
        normalizer (X : Set Model) ≤ H.map (MulAut.conj (g*k)).toMonoidHom := by
      have hh := map_mono (f := (MulAut.conj g).toMonoidHom) h
      rwa [map_equiv_normalizer_eq,hback,conjugate_comp] at hh
    exact hk.imp (transfer _) (transfer _)
  · right; left
    let := hYe
    let Y0 := Y.map (MulAut.conj g).toMonoidHom
    have hY0 : Y0 ≠ ⊥ := fun he => hY
      ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp he)
    have hN : normalizer (X : Set Model) ≤ normalizer (Y0 : Set Model) := by
      have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hNY
      rwa [map_equiv_normalizer_eq,map_equiv_normalizer_eq,hback] at hh
    refine ⟨Y0,hY0,IsElementaryAbelian.map _,hN,?_⟩
    rintro z ⟨u,hu,rfl⟩ hz
    have hu1 : u ≠ 1 := by intro he; apply hz; rw [he,map_one]
    exact (hpure u hu hu1).trans (isConj_iff.mpr ⟨g,rfl⟩)
  · right; right
    have hXY : X ≤ Y.map (MulAut.conj g).toMonoidHom := hback ▸ map_mono hAY
    have hN : normalizer (X : Set Model) ≤
        normalizer (Y.map (MulAut.conj g).toMonoidHom : Set Model) := by
      have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hNY
      rwa [map_equiv_normalizer_eq,map_equiv_normalizer_eq,hback] at hh
    exact ⟨g,Y,hXY,hN,hYe,hzY,hYcard,hYker,n,hlift,himage⟩

/-- Every mixed zero-form group of order greater than sixteen has whole
normalizer coverage in E/F or a nontrivial pure-2A normalizer. -/
theorem mixed_zero_form_of_card_gt16 (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) (hcard : 16 < Nat.card X) :
    (∃ g : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom) ∨
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj a y) := by
  rcases mixed_zero_form_reduction X hzero hn with h | h | ⟨g,Y,hXY,_,hYe,_,hc,_⟩
  · exact Or.inl h
  · exact Or.inr h
  · have hh := card_le_of_le hXY
    rw [card_map_of_injective (MulAut.conj g).injective,hc] at hh
    omega

/-- At maximal TWO-local level, the entire normalizer is preserved in this
source reduction; subgroup-coatom maximality is not used. -/
theorem maximal_mixed_zero_form_of_card_gt16 (X H : Subgroup Model)
    [IsElementaryAbelian 2 X] (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) (hcard : 16 < Nat.card X)
    (hH : IsMaximalTwoLocal H) (hHX : H = normalizer (X : Set Model)) :
    (∃ g : Model, H = M_F.map (MulAut.conj g).toMonoidHom ∨
      H = max1.map (MulAut.conj g).toMonoidHom) ∨
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ IsElementaryAbelian 2 Y ∧
      H = normalizer (Y : Set Model) ∧ ∀ y ∈ Y, y ≠ 1 → IsConj a y) := by
  rcases mixed_zero_form_of_card_gt16 X hzero hn hcard with ⟨g,hg | hg⟩ | ⟨Y,hY,hYe,hNY,hp⟩
  · exact Or.inl ⟨g,Or.inl (hH.eq_of_le
      (nativeF_generated_isTwoLocal.map_equiv (MulAut.conj g)) (hHX ▸ hg))⟩
  · exact Or.inl ⟨g,Or.inr (hH.eq_of_le
      (embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj g)) (hHX ▸ hg))⟩
  · let := hYe
    exact Or.inr ⟨Y,hY,hYe,hH.eq_of_le ⟨Y,hY,IsElementaryAbelian.isPGroup 2 Y,rfl⟩
      (hHX ▸ hNY),hp⟩

/-- The literal arbitrary-radical consumer of the smaller-kernel reduction.
The selected pure subgroup, when needed, belongs to the original radical,
and both the local full normalizer and its two-core use the actual inclusion. -/
theorem radical_mixed_zero_form_of_card_gt16 (P X : Subgroup Model)
    (hP : P.IsPRadical 2) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) (hcard : 16 < Nat.card X)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ H : Subgroup Model, IsTwoLocal H ∧
      ((∃ g : Model, H = M_F.map (MulAut.conj g).toMonoidHom ∨
        H = max1.map (MulAut.conj g).toMonoidHom) ∨
        ∃ Y : Subgroup Model, Y ≠ ⊥ ∧ IsElementaryAbelian 2 Y ∧ Y ≤ P ∧
          (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧ H = normalizer (Y : Set Model)) ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  have rows : ∃ H : Subgroup Model, IsTwoLocal H ∧
      ((∃ g : Model, H = M_F.map (MulAut.conj g).toMonoidHom ∨
        H = max1.map (MulAut.conj g).toMonoidHom) ∨
        ∃ Y : Subgroup Model, Y ≠ ⊥ ∧ IsElementaryAbelian 2 Y ∧ Y ≤ P ∧
          (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧ H = normalizer (Y : Set Model)) ∧
      normalizer (P : Set Model) ≤ H := by
    rcases mixed_zero_form_of_card_gt16 X hzero hn hcard with ⟨g,hg | hg⟩ | ⟨Y,hY,hYe,hNY,hp⟩
    · exact ⟨_,nativeF_generated_isTwoLocal.map_equiv (MulAut.conj g),
        Or.inl ⟨g,Or.inl rfl⟩,hNX.trans hg⟩
    · exact ⟨_,embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj g),
        Or.inl ⟨g,Or.inr rfl⟩,hNX.trans hg⟩
    · let := hYe
      have hN := hNX.trans hNY
      have hYP : Y ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
        P Y hP.isPGroup (IsElementaryAbelian.isPGroup 2 Y) hP.2.le hN
      exact ⟨_,⟨Y,hY,IsElementaryAbelian.isPGroup 2 Y,rfl⟩,
        Or.inr ⟨Y,hY,hYe,hYP,hp,rfl⟩,hN⟩
  obtain ⟨H,hH,hrow,hNH⟩ := rows
  have hPH := P.le_normalizer.trans hNH
  have hN := hNH.trans H.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf H hPH hN
  refine ⟨H,hH,hrow,hNH,hPH,?_,hP.subgroupOf_of_normalizer_normalizes H hPH hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hNH]
  · rw [hcore,map_subgroupOf_eq_of_le hPH]

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.ZeroFormReduction
