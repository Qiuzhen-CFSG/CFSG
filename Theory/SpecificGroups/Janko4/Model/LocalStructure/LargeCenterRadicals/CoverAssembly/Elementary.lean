module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.CoverAssembly
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxPair
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxApplication
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxResidualApplication
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxResidualSmall
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxPurePair
public import Theory.GroupTheory.QuasithinBasic

/-!
# Assembly from the remaining native elementary normalizers

The zero-form classification and exhaustive nonsingular box reduction reduce
an arbitrary maximal two-local to the two explicit geometric inputs below.
All four final rows remain literal subgroups of the matrix model. The same
ambient conjugator transports nonsingularity, maximality and the whole
normalizer. The cyclic box image needs a geometric input only for pure-second
four-groups: `BoxPair` already places its mixed four-groups.
`BoxResidualApplication` and `BoxResidualSmall` discharge residual images one
through seven. The strongest assembly therefore requires only pure-first
normalizers and the pure-second four-group with cyclic box image.

This is a conditional assembly theorem, not a proof of the two remaining
inputs. Pure-first normalizers and residual-box normalizers must be supplied
before `MaximalTwoLocalCover` or its radical exclusions become unconditional.
Source: Kleidman--Wilson (1988), Sections 2.1--2.3, pp.488--493.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.LargeCenterRadicals
open ElementaryNormalizerCover OuterHalf
open InvolutionCentralizers.Second
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

/-- Placement in exactly the four literal rows of the maximal-two-local cover. -/
abbrev NativeLocalPlacement (M : Subgroup Model) : Prop :=
  ∃ g : Model,
    M = max1.map (MulAut.conj g).toMonoidHom ∨
    M = sourceSubgroup.map (MulAut.conj g).toMonoidHom ∨
    M = LinearFive.fullNormalizer.map (MulAut.conj g).toMonoidHom ∨
    M = SymmetricLinear.max4Subgroup.map (MulAut.conj g).toMonoidHom

private theorem map_conj_mul (A : Subgroup Model) (g k : Model) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*k)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem undo_conj (A : Subgroup Model) (g : Model) :
    (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
  rw [map_conj_mul,mul_inv_cancel]
  have he : (MulAut.conj (1 : Model)).toMonoidHom = MonoidHom.id Model := by ext x; simp
  rw [he,map_id]

/-- The same four native rows are stable under actual ambient conjugation. -/
theorem NativeLocalPlacement.map_conj {M : Subgroup Model}
    (hM : NativeLocalPlacement M) (g : Model) :
    NativeLocalPlacement (M.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨k,hk | hk | hk | hk⟩ := hM
  · exact ⟨g*k,Or.inl (by rw [hk,map_conj_mul])⟩
  · exact ⟨g*k,Or.inr (Or.inl (by rw [hk,map_conj_mul]))⟩
  · exact ⟨g*k,Or.inr (Or.inr (Or.inl (by rw [hk,map_conj_mul])))⟩
  · exact ⟨g*k,Or.inr (Or.inr (Or.inr (by rw [hk,map_conj_mul])))⟩

private theorem nonsingular_map (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hns : (intrinsicElementaryForm X).Nondegenerate) (e : Model ≃* Model)
    (Y : Subgroup Model) [IsElementaryAbelian 2 Y] (he : X.map e.toMonoidHom = Y) :
    (intrinsicElementaryForm Y).Nondegenerate := by
  apply (formRadical_eq_bot_iff Y).mp
  apply eq_bot_iff.mpr
  intro y hy
  obtain ⟨x,hx,rfl⟩ := he ▸ hy.1
  have hxrad : x ∈ formRadical X := by
    refine ⟨hx,?_⟩
    intro z hz
    have hh := hy.2 (e z) (he ▸ mem_map_of_mem e.toMonoidHom hz)
    change outerValue (e x) (e z) = 0 at hh
    rwa [outerValue_equiv] at hh
  have hx1 : x = 1 := mem_bot.mp (((formRadical_eq_bot_iff X).mpr hns) ▸ hxrad)
  exact mem_bot.mpr (by rw [hx1,map_one])

private theorem native_ef (M : Subgroup Model)
    (h : ∃ g : Model, M = LinearFive.M_F.map (MulAut.conj g).toMonoidHom ∨
      M = max1.map (MulAut.conj g).toMonoidHom) : NativeLocalPlacement M := by
  obtain ⟨g,hg | hg⟩ := h
  · exact ⟨g,Or.inr (Or.inr (Or.inl (by rwa [LinearFive.M_F_eq_fullNormalizer] at hg)))⟩
  · exact ⟨g,Or.inl hg⟩

private theorem native_of_zero_enlargement
    (hpure : ∀ (X : Subgroup Model) [IsElementaryAbelian 2 X], X ≠ ⊥ →
      (∀ x ∈ X, x ≠ 1 → IsConj a x) →
      IsMaximalTwoLocal (normalizer (X : Set Model)) →
      NativeLocalPlacement (normalizer (X : Set Model)))
    (M : Subgroup Model) (hmax : IsMaximalTwoLocal M)
    (Z : Subgroup Model) [IsElementaryAbelian 2 Z] (hZ : Z ≠ ⊥)
    (hzero : intrinsicElementaryForm Z = 0)
    (hN : M ≤ normalizer (Z : Set Model)) : NativeLocalPlacement M := by
  have he : M = normalizer (Z : Set Model) :=
    hmax.eq_of_le ⟨Z,hZ,IsElementaryAbelian.isPGroup 2 Z,rfl⟩ hN
  by_cases hp : ∀ z ∈ Z, z ≠ 1 → IsConj a z
  · exact he ▸ hpure Z hZ hp (he ▸ hmax)
  · rcases M22Images.ZeroFormMaximal.maximal_mixed_zero_form Z M hzero hp hmax he with
      hef | ⟨W,hW,hWe,hMW,hpureW⟩
    · exact native_ef M hef
    · let : IsElementaryAbelian 2 W := hWe
      exact hMW ▸ hpure W hW hpureW (hMW ▸ hmax)

/-- Exact final assembly from the two remaining geometric families. In the
cyclic box image, the residual premise is needed only for a pure-second
four-group; the mixed four-groups have already been placed. -/
theorem maximalTwoLocalCover_of_pure_and_residual_box
    (hpure : ∀ (X : Subgroup Model) [IsElementaryAbelian 2 X], X ≠ ⊥ →
      (∀ x ∈ X, x ≠ 1 → IsConj a x) →
      IsMaximalTwoLocal (normalizer (X : Set Model)) →
      NativeLocalPlacement (normalizer (X : Set Model)))
    (hbox : ∀ (X : Subgroup Model) [IsElementaryAbelian 2 X],
      (seed : Model) ∈ X → (intrinsicElementaryForm X).Nondegenerate →
      IsMaximalTwoLocal (normalizer (X : Set Model)) → ∀ r : Fin 8,
      (X.subgroupOf Local).map starHom = BoxImages.residualImage r →
      (r = 0 → Nat.card X = 4 ∧ ¬ ∃ x ∈ X, IsConj a x) →
      NativeLocalPlacement (normalizer (X : Set Model))) : MaximalTwoLocalCover := by
  intro M hM
  change NativeLocalPlacement M
  rcases M22Images.ZeroFormMaximal.maximal_twoLocal_remaining_cases M hM with
    hef | ⟨X,hX,hXe,hMX,hp | hns⟩
  · exact native_ef M hef
  · let : IsElementaryAbelian 2 X := hXe
    exact hMX ▸ hpure X hX hp (hMX ▸ hM)
  · let : IsElementaryAbelian 2 X := hXe
    have hNX : IsMaximalTwoLocal (normalizer (X : Set Model)) := hMX ▸ hM
    rcases BoxImages.maximal_nonsingular_local_reduction X hX hns hNX with
      ⟨g,r,hYL,hys,hp,hr⟩ | hef | ⟨Z,hZ,hZe,hNZ,hpureZ⟩
    · let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
      let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
      have hYns : (intrinsicElementaryForm Y).Nondegenerate :=
        nonsingular_map X hns (MulAut.conj g⁻¹) Y rfl
      have hNY : IsMaximalTwoLocal (normalizer (Y : Set Model)) := by
        rw [← map_equiv_normalizer_eq]
        exact isMaximalTwoLocal_map (MulAut.conj g⁻¹) hNX
      have hplace : NativeLocalPlacement (normalizer (Y : Set Model)) := by
        by_cases hzero : r = 0
        · subst r
          by_cases hfirst : ∃ x ∈ Y, IsConj a x
          · obtain ⟨k,hk | hk⟩ := BoxPair.source_pair_mixed_native Y hys hYns hr hNY hfirst
            · exact ⟨k,Or.inl hk⟩
            · exact ⟨k,Or.inr (Or.inl hk)⟩
          · obtain ⟨_,_,_,_,hcard⟩ := BoxPair.source_pair_eq Y hys hYns hr
            exact hbox Y hys hYns hNY 0 hr (fun _ => ⟨hcard,hfirst⟩)
        · exact hbox Y hys hYns hNY r hr (fun h => (hzero h).elim)
      have ht := hplace.map_conj g
      rw [map_equiv_normalizer_eq,undo_conj] at ht
      exact hMX ▸ ht
    · exact hMX ▸ native_ef _ hef
    · let : IsElementaryAbelian 2 Z := hZe
      exact hMX ▸ hNZ ▸ hpure Z hZ hpureZ (hNZ ▸ hNX)

/-- The four order-eight residual images are discharged by canonical central
enlargement. Only residual images zero through three remain as box inputs. -/
theorem maximalTwoLocalCover_of_pure_and_small_box
    (hpure : ∀ (X : Subgroup Model) [IsElementaryAbelian 2 X], X ≠ ⊥ →
      (∀ x ∈ X, x ≠ 1 → IsConj a x) →
      IsMaximalTwoLocal (normalizer (X : Set Model)) →
      NativeLocalPlacement (normalizer (X : Set Model)))
    (hbox : ∀ (X : Subgroup Model) [IsElementaryAbelian 2 X],
      (seed : Model) ∈ X → (intrinsicElementaryForm X).Nondegenerate →
      IsMaximalTwoLocal (normalizer (X : Set Model)) → ∀ r : Fin 4,
      (X.subgroupOf Local).map starHom = BoxImages.residualImage (r.castLE (by decide)) →
      (r = 0 → Nat.card X = 4 ∧ ¬ ∃ x ∈ X, IsConj a x) →
      NativeLocalPlacement (normalizer (X : Set Model))) : MaximalTwoLocalCover := by
  apply maximalTwoLocalCover_of_pure_and_residual_box hpure
  intro X hXe hs hns hmax r hrow hsmall
  have close (k : Fin 4)
      (hk : (X.subgroupOf Local).map starHom = BoxImages.residualImage (BoxResidual.largeRow k)) :
      NativeLocalPlacement (normalizer (X : Set Model)) := by
    obtain ⟨Z,hZ,hZe,hzero,hN⟩ := BoxResidual.large_row_zero_enlargement X hs k hk
    let : IsElementaryAbelian 2 Z := hZe
    exact native_of_zero_enlargement hpure _ hmax Z hZ hzero hN
  fin_cases r
  · exact hbox X hs hns hmax 0 hrow (fun _ => hsmall rfl)
  · exact hbox X hs hns hmax 1 hrow (by intro h; cases h)
  · exact hbox X hs hns hmax 2 hrow (by intro h; cases h)
  · exact hbox X hs hns hmax 3 hrow (by intro h; cases h)
  · exact close 0 hrow
  · exact close 1 hrow
  · exact close 2 hrow
  · exact close 3 hrow


/-- All noncyclic residual box images are discharged. The only box premise
left is the pure-second four-group over the original pair permutation. -/
theorem maximalTwoLocalCover_of_pure_and_second_four
    (hpure : ∀ (X : Subgroup Model) [IsElementaryAbelian 2 X], X ≠ ⊥ →
      (∀ x ∈ X, x ≠ 1 → IsConj a x) →
      IsMaximalTwoLocal (normalizer (X : Set Model)) →
      NativeLocalPlacement (normalizer (X : Set Model)))
    (hpair : ∀ (X : Subgroup Model) [IsElementaryAbelian 2 X],
      (seed : Model) ∈ X → (intrinsicElementaryForm X).Nondegenerate →
      IsMaximalTwoLocal (normalizer (X : Set Model)) →
      (X.subgroupOf Local).map starHom = BoxImages.residualImage 0 →
      Nat.card X = 4 → (¬ ∃ x ∈ X, IsConj a x) →
      NativeLocalPlacement (normalizer (X : Set Model))) : MaximalTwoLocalCover := by
  apply maximalTwoLocalCover_of_pure_and_small_box hpure
  intro X hXe hs hns hmax r hrow hzero
  have close (k : Fin 3)
      (hk : (X.subgroupOf Local).map starHom = BoxImages.residualImage (BoxResidual.smallRow k)) :
      NativeLocalPlacement (normalizer (X : Set Model)) := by
    obtain ⟨hZ,hform,hN⟩ := BoxResidual.small_row_zeroWitness X hs k hk
    exact native_of_zero_enlargement hpure _ hmax (BoxResidual.coreZeroWitness X) hZ hform hN
  fin_cases r
  · exact hpair X hs hns hmax hrow (hzero rfl).1 (hzero rfl).2
  · exact close 0 hrow
  · exact close 1 hrow
  · exact close 2 hrow

/- The pure-second row-zero branch is now covered by the canonical two-core
radical witness as well; only pure-first normalizers remain conditional. -/
theorem maximalTwoLocalCover_of_pure_first
    (hpure : ∀ (X : Subgroup Model) [IsElementaryAbelian 2 X], X ≠ ⊥ →
      (∀ x ∈ X, x ≠ 1 → IsConj a x) →
      IsMaximalTwoLocal (normalizer (X : Set Model)) →
      NativeLocalPlacement (normalizer (X : Set Model))) : MaximalTwoLocalCover := by
  apply maximalTwoLocalCover_of_pure_and_second_four hpure
  intro X hXe hs hns hmax hrow _ _
  let : IsElementaryAbelian 2 X := hXe
  obtain ⟨hZ,hzero,hN⟩ := BoxPurePair.source_zeroWitness X hs hrow
  exact native_of_zero_enlargement hpure _ hmax (BoxResidual.coreZeroWitness X) hZ hzero hN

end Janko4.LocalStructure.LargeCenterRadicals
