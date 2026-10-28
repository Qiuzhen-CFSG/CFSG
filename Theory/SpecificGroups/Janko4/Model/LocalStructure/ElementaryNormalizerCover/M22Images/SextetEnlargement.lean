module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.SextetShears

/-!
# Canonical zero-form enlargement in the sextet case

The central omega of C(X) centralizes each of the three pair elements joining
one vertex of the fixed tetrad to the others. The actual star action therefore
fixes all four vertices individually. The inner-half character calculation
then puts their tetrad involution in the intrinsic form radical of this central
omega, even when the original kernel intersection is smaller than eight.

Adjoining this radical to X preserves elementary-abelianness, zero intrinsic
form, the full centralizer, and normalization by the whole N(X). Consequently
the native sextet configuration either admits the checked pure-2A shear
reduction, or has a strictly larger zero-form witness. Finite maximal choice
can eliminate the latter case; no extraspecial-core placement is assumed.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Proposition
2.2.3, p.491, central-involution enlargement before the reducibility argument.
The finite pair-label checks use the imported ATLAS kernel coordinates and
native Mathieu marking, with their original attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.SextetEnlargement
open Cardinality QuotientCount.Image KernelCount
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open M23Geometry FusionCertificate ElementarySylow SextetKernel SextetCentralizer
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

private def point : Fin 4 → Fin 24 := ![5,8,13,14]
private theorem pair_labels : ∀ i : Fin 3, ∀ a b : Fin 24,
    pairLabel a b = pairLabel (point 0) (point i.succ) →
      (a = point 0 ∧ b = point i.succ) ∨ (a = point i.succ ∧ b = point 0) := by
  decide +kernel

private theorem image_fixes (i : Fin 16) (j : Fin 4) :
    StarOrderCertificate.relabel.symm
      (CommonFour.extendPoint (pointTable (candidateIndex 0 i))
        (StarOrderCertificate.relabel (point j))) = point j := by
  revert i j
  decide +kernel

private theorem star_fixes (x : M) (hx : projection x ∈ imageGroup) (j : Fin 4) :
    (starHom x).val (point j) = point j := by
  obtain ⟨p,⟨i,hi⟩,hp⟩ := hx
  have he : projection x = imageElement i := by
    rw [imageElement,show sylowElement (candidateIndex 0 i) = p from Subtype.ext hi]
    exact hp.symm
  exact (KernelAction.star_points x _ he _).trans (image_fixes i j)

private theorem pair_centralizes (X : Subgroup Model) (hXM : X ≤ M)
    (himage : (X.subgroupOf M).map projection ≤ imageGroup) (i : Fin 3) :
    (kernelValue (pairLabel (point 0) (point i.succ)) : Model) ∈
      centralizer (X : Set Model) := by
  intro x hx
  let x0 : M := ⟨x,hXM hx⟩
  have hp : projection x0 ∈ imageGroup :=
    himage (mem_map_of_mem projection (show x0 ∈ X.subgroupOf M from hx))
  have he := congrArg Subtype.val (starHom_pair x0 (point 0) (point i.succ))
  rw [star_fixes x0 hp 0,star_fixes x0 hp i.succ] at he
  exact congrArg (fun x : M => (x : Model)) (mul_inv_eq_iff_eq_mul.mp he)

/-- Central elements of C(X) fix the four tetrad points individually. -/
private theorem omega_fixes (X : Subgroup Model) (hXM : X ≤ M)
    (himage : (X.subgroupOf M).map projection ≤ imageGroup)
    (w : M) (hw : (w : Model) ∈ omegaCenterIn (centralizer (X : Set Model))) :
    ∀ j : Fin 4, (starHom w).val (point j) = point j := by
  have hp (i : Fin 3) :
      pairLabel ((starHom w).val (point 0)) ((starHom w).val (point i.succ)) =
        pairLabel (point 0) (point i.succ) := by
    have hc : Commute w (kernelValue (pairLabel (point 0) (point i.succ))) := by
      apply Subtype.ext
      exact (((mem_omegaCenterIn_iff _ _).mp hw).2.1 _
        (pair_centralizes X hXM himage i)).symm
    have he := congrArg Subtype.val (starHom_pair w (point 0) (point i.succ))
    change w * kernelValue (pairLabel (point 0) (point i.succ)) * w⁻¹ =
      kernelValue (pairLabel ((starHom w).val (point 0)) ((starHom w).val (point i.succ))) at he
    rw [hc.eq,mul_assoc,mul_inv_cancel,mul_one] at he
    exact kernelValue_injective (pairLabel_lt _ _) (pairLabel_lt _ _) he.symm
  have h0 : (starHom w).val (point 0) = point 0 := by
    rcases pair_labels 0 _ _ (hp 0) with h | h
    · exact h.1
    · rcases pair_labels 1 _ _ (hp 1) with h' | h'
      · exact h'.1
      · exact (show (point (1 : Fin 3).succ) ≠ point (0 : Fin 3).succ from by decide)
          (h'.1.symm.trans h.1) |>.elim
  have hs (i : Fin 3) : (starHom w).val (point i.succ) = point i.succ := by
    rcases pair_labels i _ _ (hp i) with h | h
    · exact h.2
    · have hn : point 0 ≠ point i.succ := by fin_cases i <;> decide
      exact (hn (h0.symm.trans h.1)).elim
  intro j
  fin_cases j
  · exact h0
  · exact hs 0
  · exact hs 1
  · exact hs 2

private theorem elementary_order (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (x : Model) (hx : x ∈ X) (hx1 : x ≠ 1) : orderOf x = 2 :=
  (Nat.prime_two.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx))).resolve_left
      (by simpa using hx1)

/-- The actual tetrad involution lies in the form radical of the canonical
central-omega enlargement, even when it does not belong to X. -/
theorem centralInvolution_mem_radical (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXM : X ≤ M) (himage : (X.subgroupOf M).map projection ≤ imageGroup)
    (k : Fin 30)
    (hpair : ∀ d : Fin 2, imageElement (nonOctadPair k d) ∈ (X.subgroupOf M).map projection)
    (hCM : centralizer (X : Set Model) ≤ M) :
    centralInvolution ∈ formRadical (omegaCenterIn (centralizer (X : Set Model))) := by
  let W := omegaCenterIn (centralizer (X : Set Model))
  have htW : centralInvolution ∈ W := centralInvolution_mem_omega X k hpair hCM
  refine ⟨htW,?_⟩
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1,outerValue_one_right]
  let w0 : M := ⟨w,hCM (map_subtype_le _ hw)⟩
  have hw2 := elementary_order W w hw hw1
  have hf := omega_fixes X hXM himage w0 hw
  let R := (solvableResidual (centralizer ({w} : Set Model))).map
    (centralizer ({w} : Set Model)).subtype
  have hi (i : Fin 3) : (kernelValue (pairLabel (point 0) (point i.succ)) : Model) ∈ R := by
    have hn : point 0 ≠ point i.succ := by fin_cases i <;> decide
    have hp := KernelAction.inner_of_star_fixed w0 _ _ hn (hf 0) (hf i.succ)
    have hc : Commute (kernelValue (pairLabel (point 0) (point i.succ)) : Model) w :=
      (mem_centralizer_singleton_iff.mp (map_subtype_le _ hp)).symm
    exact (innerRelated_symm _ _ (KernelAction.pair_order _ _ hn) hw2 hc).mp hp
  have ht : InnerRelated w centralInvolution := by
    have hh := R.mul_mem (hi 0) (R.mul_mem (hi 1) (hi 2))
    change ((kernelValue 135 * (kernelValue 633 * kernelValue 945) : M) : Model) ∈ R at hh
    rw [← kernelValue_xor,← kernelValue_xor] at hh
    exact hh
  have hc : Commute w centralInvolution := (mem_centralizer_singleton_iff.mp
    (map_subtype_le _ ht)).symm
  exact (outerValue_eq_zero_iff _ _ centralInvolution_ne_one).mpr
    ((innerRelated_symm _ _ hw2 centralInvolution_order hc).mp ht)


/-- Adjoin the intrinsic form radical of the canonical central omega. -/
@[expose] def zeroExtension (X : Subgroup Model) : Subgroup Model :=
  X ⊔ formRadical (omegaCenterIn (centralizer (X : Set Model)))

theorem le_zeroExtension (X : Subgroup Model) : X ≤ zeroExtension X := le_sup_left

theorem zeroExtension_le_omega (X : Subgroup Model) [IsElementaryAbelian 2 X] :
    zeroExtension X ≤ omegaCenterIn (centralizer (X : Set Model)) :=
  sup_le (elementary_le_centralizer_omegaCenter X) (formRadical_le _)

instance zeroExtension_elementary (X : Subgroup Model) [IsElementaryAbelian 2 X] :
    IsElementaryAbelian 2 (zeroExtension X) :=
  IsElementaryAbelian.of_injective (inclusion (zeroExtension_le_omega X)) (inclusion_injective _)

theorem zeroExtension_normalizer (X : Subgroup Model) :
    normalizer (X : Set Model) ≤ normalizer (zeroExtension X : Set Model) :=
  normalizer_le_normalizer_sup_of_normalizer_le_left
    ((normalizer_le_centralizer_omegaCenter_normalizer X).trans
      (normalizer_le_formRadical_normalizer _))

theorem zeroExtension_centralizer (X : Subgroup Model) [IsElementaryAbelian 2 X] :
    centralizer (zeroExtension X : Set Model) = centralizer (X : Set Model) := by
  apply le_antisymm (centralizer_le (le_zeroExtension X))
  rw [← centralizer_omegaCenter_centralizer_eq X]
  exact centralizer_le (zeroExtension_le_omega X)

/-- The extension still has zero intrinsic form. -/
theorem zeroExtension_form (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0) : intrinsicElementaryForm (zeroExtension X) = 0 := by
  let W := omegaCenterIn (centralizer (X : Set Model))
  let R := formRadical W
  have hXW : X ≤ W := elementary_le_centralizer_omegaCenter X
  have hRW : R ≤ W := formRadical_le W
  have hKW : zeroExtension X ≤ W := zeroExtension_le_omega X
  have hs (u v : Model) (hu : u ∈ W) (hv : v ∈ W) :
      outerValue u v = outerValue v u :=
    (intrinsicElementaryForm_isSymm W).eq (Additive.ofMul ⟨u,hu⟩) (Additive.ofMul ⟨v,hv⟩)
  have hc (u v : Model) (hu : u ∈ W) (hv : v ∈ W) : Commute u v :=
    (W.le_centralizer hv) u hu
  have hn : X ≤ normalizer (R : Set Model) := by
    intro x hx
    exact centralizer_le_normalizer _ (fun r hr => hc r x (hRW hr) (hXW hx))
  have split (u : Model) (hu : u ∈ zeroExtension X) :
      ∃ x ∈ X, ∃ r ∈ R, x * r = u := by
    change u ∈ X ⊔ R at hu
    change u ∈ (↑(X ⊔ R) : Set Model) at hu
    rw [coe_mul_of_left_le_normalizer_right X R hn] at hu
    exact hu
  have row (x : Model) (hx : x ∈ X) (v : Model) (hv : v ∈ zeroExtension X) :
      outerValue x v = 0 := by
    by_cases hx1 : x = 1
    · rw [hx1,outerValue_one_left]
    obtain ⟨y,hy,r,hr,rfl⟩ := split v hv
    rw [outerValue_mul_right x (elementary_order X x hx hx1) y r
      (hc x y (hXW hx) (hXW hy)) (hc x r (hXW hx) (hRW hr))]
    have hxy : outerValue x y = 0 := congrArg
      (fun B : LinearMap.BilinForm (ZMod 2) (Additive X) =>
        B (Additive.ofMul ⟨x,hx⟩) (Additive.ofMul ⟨y,hy⟩)) hzero
    rw [hxy,hs x r (hXW hx) (hRW hr),hr.2 x (hXW hx),add_zero]
  ext u v
  change outerValue (u.toMul : Model) (v.toMul : Model) = 0
  have hu := u.toMul.property
  have hv := v.toMul.property
  by_cases hv1 : (v.toMul : Model) = 1
  · rw [hv1,outerValue_one_right]
  obtain ⟨x,hx,r,hr,he⟩ := split u.toMul hu
  rw [← he,hs _ _ (W.mul_mem (hXW hx) (hRW hr)) (hKW hv),
    outerValue_mul_right _ (elementary_order (zeroExtension X) _ hv hv1) x r
      (hc _ _ (hKW hv) (hXW hx)) (hc _ _ (hKW hv) (hRW hr)),
    hs _ x (hKW hv) (hXW hx),row x hx _ hv,
    hs _ r (hKW hv) (hRW hr),hr.2 _ (hKW hv),add_zero]

/-- If X omits the tetrad involution, a strictly larger zero-form group
has a normalizer containing the WHOLE original normalizer. -/
theorem pure_or_larger (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXM : X ≤ M) (himage : (X.subgroupOf M).map projection ≤ imageGroup)
    (k : Fin 30)
    (hpair : ∀ d : Fin 2, imageElement (nonOctadPair k d) ∈ (X.subgroupOf M).map projection)
    (hCM : centralizer (X : Set Model) ≤ M) (hzero : intrinsicElementaryForm X = 0) :
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ Y ≤ X ∧ IsElementaryAbelian 2 Y ∧
      normalizer (X : Set Model) ≤ normalizer (Y : Set Model) ∧
      ∀ y ∈ Y, y ≠ 1 → IsConj a y) ∨
    (X < zeroExtension X ∧ intrinsicElementaryForm (zeroExtension X) = 0 ∧
      normalizer (X : Set Model) ≤ normalizer (zeroExtension X : Set Model)) := by
  by_cases ht : centralInvolution ∈ X
  · exact Or.inl (SextetShears.pure_reduction X hXM himage k hpair hzero ht)
  · have hrad := centralInvolution_mem_radical X hXM himage k hpair hCM
    have hlt : X < zeroExtension X := lt_of_le_of_ne (le_zeroExtension X) (by
      intro he
      exact ht (he ▸ (mem_sup_right hrad : centralInvolution ∈ zeroExtension X)))
    exact Or.inr ⟨hlt,zeroExtension_form X hzero,zeroExtension_normalizer X⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.SextetEnlargement
