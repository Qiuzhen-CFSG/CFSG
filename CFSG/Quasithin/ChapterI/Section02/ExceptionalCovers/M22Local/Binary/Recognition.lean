module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
public import Theory.Representation.BinaryPermutationSixCover.Recognition

/-!
# Recognizing a marked lifted hexad section

The conjugation action is on the actual subgroup hexadRadical, with normality
relative to hexadPreimage. A section of the literal alternating quotient gives
an actual complement and a split-extension isomorphism. Perfectness then forces
R=[R,L]. Native natural-quotient coordinates identify R with the augmentation
core of order 32, carrying the ambient center to the constant line.

The native section and native quotient coordinates remain explicit inputs here;
this module does not assert the full source recognition. The automorphism alpha
records the comparison between the original point labels and the module marking.

Source: Aschbacher–Smith, I.2.2(6), printed p.412, combined manuscript of
1 March 2004.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open scoped IsMulCommutative
variable {K : Type*} [Group K]

/-- Conjugation on the ambient radical, with normality relative to the hexad preimage. -/
noncomputable def hexadConjugation (e : (K ⧸ center K) ≃* M22) (B : Finset (Fin 22)) :
    hexadPreimage e B →* MulAut (hexadRadical e B) :=
  (MulAut.congr (Subgroup.subgroupOfEquivOfLe (hexadRadical_le e B))).toMonoidHom.comp
    MulAut.conjNormal

@[simp] theorem hexadConjugation_coe (e : (K ⧸ center K) ≃* M22) (B : Finset (Fin 22))
    (g : hexadPreimage e B) (r : hexadRadical e B) :
    (hexadConjugation e B g r : K) = g.val * r.val * g.val⁻¹ := rfl

/-- The six-point alternating quotient in the original labels. -/
noncomputable def hexadSixMap (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    hexadPreimage e B →* alternatingGroup (Fin 6) :=
  (hexadQuotientEquiv e hB).toMonoidHom.comp
    (QuotientGroup.mk' ((hexadRadical e B).subgroupOf (hexadPreimage e B)))

theorem hexadSixMap_ker (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (hexadSixMap e hB).ker = (hexadRadical e B).subgroupOf (hexadPreimage e B) := by
  exact (MonoidHom.ker_mulEquiv_comp _ (hexadQuotientEquiv e hB)).trans
    (QuotientGroup.ker_mk' _)

/-- The actual multiplication map from the radical and a proposed alternating section. -/
noncomputable def hexadSplitHom (e : (K ⧸ center K) ≃* M22)
    (B : Finset (Fin 22)) (s : alternatingGroup (Fin 6) →* hexadPreimage e B) :
    hexadRadical e B ⋊[(hexadConjugation e B).comp s] alternatingGroup (Fin 6) →*
      hexadPreimage e B :=
  SemidirectProduct.lift (Subgroup.inclusion (hexadRadical_le e B)) s (by
    intro a
    apply MonoidHom.ext
    intro r
    apply Subtype.ext
    rfl)

/-- A section of the actual six-point quotient constructs, rather than assumes,
the split-extension isomorphism. The automorphism alpha records any change to
the natural-module marking. -/
theorem hexadSplitHom_bijective (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (alpha : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6))
    (s : alternatingGroup (Fin 6) →* hexadPreimage e B)
    (hs : ∀ a, hexadSixMap e hB (s a) = alpha a) :
    Function.Bijective (hexadSplitHom e B s) := by
  let q := hexadSixMap e hB
  have hn (r : hexadRadical e B) : q (Subgroup.inclusion (hexadRadical_le e B) r) = 1 := by
    apply (show (hexadRadical e B).subgroupOf (hexadPreimage e B) ≤ q.ker from
      (hexadSixMap_ker e hB).ge)
    exact r.property
  have hq (x : hexadRadical e B ⋊[(hexadConjugation e B).comp s] alternatingGroup (Fin 6)) :
      q (hexadSplitHom e B s x) = alpha x.right := by
    change q (Subgroup.inclusion (hexadRadical_le e B) x.left * s x.right) = _
    rw [map_mul, hn, hs, one_mul]
  constructor
  · intro x y h
    have hr : x.right = y.right := alpha.injective ((hq x).symm.trans
      ((congrArg q h).trans (hq y)))
    have hl : x.left = y.left := by
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      change x.left.val * (s x.right).val = y.left.val * (s y.right).val at h'
      rwa [hr, mul_right_cancel_iff] at h'
    exact SemidirectProduct.ext hl hr
  · intro g
    let a := alpha.symm (q g)
    have hk : g * (s a)⁻¹ ∈ (hexadRadical e B).subgroupOf (hexadPreimage e B) := by
      rw [← hexadSixMap_ker e hB]
      change q (g * (s a)⁻¹) = 1
      rw [map_mul, map_inv, hs, alpha.apply_symm_apply, mul_inv_cancel]
    let r : hexadRadical e B := ⟨(g * (s a)⁻¹).val, hk⟩
    refine ⟨⟨r, a⟩, ?_⟩
    apply Subtype.ext
    exact inv_mul_cancel_right g.val (s a).val

/-- The section is faithful, so its image is genuinely A6. -/
theorem hexadSection_injective (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (alpha : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6))
    (s : alternatingGroup (Fin 6) →* hexadPreimage e B)
    (hs : ∀ a, hexadSixMap e hB (s a) = alpha a) : Function.Injective s := by
  intro a b hab
  apply alpha.injective
  rw [← hs, ← hs, hab]

/-- The range of a lifted section is an actual complement in the preimage. -/
theorem hexadSection_isComplement (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (alpha : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6))
    (s : alternatingGroup (Fin 6) →* hexadPreimage e B)
    (hs : ∀ a, hexadSixMap e hB (s a) = alpha a) :
    ((hexadRadical e B).subgroupOf (hexadPreimage e B)).IsComplement' s.range := by
  have hd : Disjoint ((hexadRadical e B).subgroupOf (hexadPreimage e B)) s.range := by
    apply disjoint_iff_inf_le.mpr
    rintro g ⟨hr, a, rfl⟩
    have he : hexadSixMap e hB (s a) = 1 := by
      change s a ∈ (hexadSixMap e hB).ker
      rwa [hexadSixMap_ker e hB]
    rw [hs, map_eq_one_iff _ alpha.injective] at he
    rw [he, map_one]
    exact Subgroup.one_mem _
  refine ⟨Subgroup.mul_injective_of_disjoint hd, ?_⟩
  intro g
  obtain ⟨x, hx⟩ := (hexadSplitHom_bijective e hB alpha s hs).surjective g
  refine ⟨(⟨Subgroup.inclusion (hexadRadical_le e B) x.left, x.left.property⟩,
    ⟨s x.right, x.right, rfl⟩), hx⟩

variable [Finite K]

/-- Recognition from native quotient coordinates and a lifted section. Perfectness
of I supplies commutator generation; no module-recognition premise is used. -/
theorem hexadRadical_core_of_section
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 2)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    [Group.IsPerfect (hexadPreimage e B)]
    (alpha : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6))
    (s : alternatingGroup (Fin 6) →* hexadPreimage e B)
    (hs : ∀ a, hexadSixMap e hB (s a) = alpha a)
    (q : hexadRadical e B →* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hqsur : Function.Surjective q)
    (hqker : q.ker = (center K).subgroupOf (hexadRadical e B))
    (hqact : ∀ a r, (q (hexadConjugation e B (s a) r)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) a.val (q r).toAdd) :
    ∃ E : hexadRadical e B ≃* Multiplicative (BinaryPermutation.core (Fin 6)),
      (∀ a r, (E (hexadConjugation e B (s a) r)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) a.val (E r).toAdd) ∧
      (∀ r, BinaryPermutation.coreToNatural (Fin 6) (E r).toAdd = (q r).toAdd) ∧
      (∀ r, r.val ∈ center K ↔ (E r).toAdd.val ∈ BinaryPermutation.constants (Fin 6)) := by
  let :=  hexadRadical_elementary e hZ hB
  let φ := (hexadConjugation e B).comp s
  let F := MulEquiv.ofBijective (hexadSplitHom e B s)
    (hexadSplitHom_bijective e hB alpha s hs)
  let : Group.IsPerfect (hexadRadical e B ⋊[φ] alternatingGroup (Fin 6)) :=
    Group.IsPerfect.ofSurjective (f := F.symm.toMonoidHom) F.symm.surjective
  have hfix (r : hexadRadical e B) (hr : r ∈ q.ker) (a : alternatingGroup (Fin 6)) :
      φ a r = r := by
    rw [hqker] at hr
    apply Subtype.ext
    change (s a).val * r.val * (s a).val⁻¹ = r.val
    have hc := mem_center_iff.mp (show r.val ∈ center K from hr) (s a).val
    rw [hc, mul_inv_cancel_right]
  obtain ⟨E, hE, heq, hk⟩ := BinaryPermutation.SixCover.core_mulEquiv_of_perfect_split φ q
    hqsur hqact hfix (by rw [hexadRadical_card e hB, hZ])
  exact ⟨E, hE, heq, fun r => (show r.val ∈ center K ↔ r ∈ q.ker by rw [hqker]; rfl).trans (hk r)⟩
/-- Perfectness and a section force the literal ambient radical to equal its
commutator with that section's image. -/
theorem hexadRadical_eq_commutator_of_section
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 2)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    [Group.IsPerfect (hexadPreimage e B)]
    (alpha : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6))
    (s : alternatingGroup (Fin 6) →* hexadPreimage e B)
    (hs : ∀ a, hexadSixMap e hB (s a) = alpha a) :
    hexadRadical e B = ⁅hexadRadical e B, s.range.map (hexadPreimage e B).subtype⁆ := by
  let := hexadRadical_elementary e hZ hB
  let φ := (hexadConjugation e B).comp s
  let F := MulEquiv.ofBijective (hexadSplitHom e B s)
    (hexadSplitHom_bijective e hB alpha s hs)
  let : Group.IsPerfect (hexadRadical e B ⋊[φ] alternatingGroup (Fin 6)) :=
    Group.IsPerfect.ofSurjective (f := F.symm.toMonoidHom) F.symm.surjective
  let f := (hexadPreimage e B).subtype.comp (hexadSplitHom e B s)
  have hleft : (SemidirectProduct.inl : hexadRadical e B →*
      hexadRadical e B ⋊[φ] alternatingGroup (Fin 6)).range.map f = hexadRadical e B := by
    rw [← MonoidHom.range_comp]
    have hh : f.comp SemidirectProduct.inl = (hexadRadical e B).subtype := by
      ext r
      simp [f, hexadSplitHom]
    rw [hh, Subgroup.range_subtype]
  have hright : (SemidirectProduct.inr : alternatingGroup (Fin 6) →*
      hexadRadical e B ⋊[φ] alternatingGroup (Fin 6)).range.map f =
        s.range.map (hexadPreimage e B).subtype := by
    rw [← MonoidHom.range_comp, ← MonoidHom.range_comp]
    congr 1
    ext a
    simp [f, hexadSplitHom]
  have h := congrArg (fun H => H.map f)
    (Representation.elementary_range_eq_commutator_of_perfect (p := 2) φ)
  rwa [Subgroup.map_commutator, hleft, hright] at h
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
