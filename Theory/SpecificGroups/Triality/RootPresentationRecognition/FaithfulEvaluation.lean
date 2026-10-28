module
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.Presentation
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.TorusWords
public import Theory.SpecificGroups.Triality.ConcreteBruhat.RelativeNormalizer

/-!
# Faithfulness of a root-preserving triality evaluation

For the explicit universal presentation, any homomorphism preserving the twelve
native root maps is an isomorphism. The abstract Bruhat cover puts its kernel
in the identity Weyl cell: a finite dihedral calculation and native Borel-cell
separation exclude every nonempty alternating word. Joint injectivity of the
native positive and torus coordinates then kills the Borel kernel. Generation
by the native signed roots, including the entire torus, proves surjectivity.

This discharges the faithfulness part of the presentation argument. It does
not supply the homomorphism: constructing that evaluation still requires the
remaining native torus conjugation equations. No order comparison, simplicity
of an unknown group, or presentation faithfulness is assumed here.

Source: the Bruhat argument of GLS3 2.3.5 and the equations of 2.4.7–8.
The original cubic field, fixed subfield, and central quotient are retained.
-/

@[expose] public noncomputable section
namespace Triality.Standard.RootPresentationRecognition.Presentation
open Parabolics ConcreteBruhat TorusCoordinates
variable {n : ℕ} {hn : 0 < n}
local notation "P" => binaryParameters n hn

/-- The native signed root ranges generate the genuine carrier, including its full torus. -/
theorem native_generates : (SignedModel.roots n hn).signedClosure = ⊤ := by
  let H := (SignedModel.roots n hn).signedClosure
  have hs := RootMembership.short_mem (SignedModel.roots n hn)
  have hl := RootMembership.long_mem (SignedModel.roots n hn)
  have hnA (t : (ExtensionField P)ˣ) : (SignedModel.roots n hn).nA t ∈ H :=
    H.mul_mem (H.mul_mem (hs true 0 _) (hs false 0 _)) (hs true 0 _)
  have hnB (t : (fixedField P)ˣ) : (SignedModel.roots n hn).nB t ∈ H :=
    H.mul_mem (H.mul_mem (hl true 0 _) (hl false 0 _)) (hl true 0 _)
  have ht : ConcreteBruhat.torus P ≤ H := by
    intro t ht
    obtain ⟨p,hp⟩ := (torusMulEquiv P rfl).surjective ⟨t,ht⟩
    have he : (SignedModel.roots n hn).torus p = t := (SignedModel.torus_eq n hn p).trans (congrArg Subtype.val hp)
    rw [← he]
    exact H.mul_mem (H.mul_mem (hnA _) (hnA _)) (H.mul_mem (hnB _) (hnB _))
  have hu : unipotent P ≤ H := by
    rw [← native_positiveClosure n hn]
    exact le_sup_left
  have hb : borel P ≤ H := by
    intro b hb
    obtain ⟨⟨u,t⟩,he⟩ := (borelEquiv P rfl).surjective ⟨b,hb⟩
    have hx : u.val*t.val = b := congrArg Subtype.val he
    rw [← hx]
    exact H.mul_mem (hu u.property) (ht t.property)
  have hw : normalizerCandidate P rfl ≤ H := by
    apply sup_le ht
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨a,rfl⟩
    cases a
    · exact (SignedModel.nA_one n hn) ▸ hnA 1
    · exact (SignedModel.nB_one n hn) ▸ hnB 1
  apply top_unique
  rw [← RelativeNormalizer.borel_sup_normalizer n hn]
  exact sup_le hb hw

variable (f : Universal n hn →* BinaryCarrier n hn)
variable (hs : ∀ s i t, f (roots.shortSigned s i t) = (SignedModel.roots n hn).shortSigned s i t)
variable (hl : ∀ s i t, f (roots.longSigned s i t) = (SignedModel.roots n hn).longSigned s i t)

include hs in
private theorem map_nA (t : (ExtensionField P)ˣ) : f (roots.nA t) = (SignedModel.roots n hn).nA t := by
  change f (roots.shortSigned true 0 t.val * roots.shortSigned false 0 (t⁻¹).val *
    roots.shortSigned true 0 t.val) = _
  simp only [map_mul, hs]
  rfl

include hl in
private theorem map_nB (t : (fixedField P)ˣ) : f (roots.nB t) = (SignedModel.roots n hn).nB t := by
  change f (roots.longSigned true 0 t.val * roots.longSigned false 0 (t⁻¹).val *
    roots.longSigned true 0 t.val) = _
  simp only [map_mul, hl]
  rfl

include hs hl in
private theorem map_torus (p : TorusParameters n hn) : f (roots.torus p) = (SignedModel.roots n hn).torus p := by
  simp only [SignedRoots.torus, SignedRoots.hA, SignedRoots.hB, map_mul,
    map_nA f hs, map_nB f hl]

include hs hl in
private theorem map_product (v : PositiveParameters n hn) :
    f (roots.positive.product v) = (nativePositiveRoots n hn).product v := by
  have he (i : Fin 6) : f (roots.positive.factor i v) = (nativePositiveRoots n hn).factor i v := by
    fin_cases i <;> first | exact hs true _ _ | exact hl true _ _
  simp only [PositiveRoots.product, map_list_prod, List.map_ofFn, Function.comp_def, he]

private def wordIndex (a : Bool) : ℕ → DihedralGroup 6
  | 0 => 1
  | k+1 => relativeReflection (if a then .arms else .central) * wordIndex (!a) k

private theorem wordIndex_ne (a : Bool) (k : ℕ) (hk : k ≤ 6) (hk0 : 0 < k) : wordIndex a k ≠ 1 := by
  have h : ∀ (a : Bool) (k : Fin 7), 0 < k.val → wordIndex a k.val ≠ 1 := by decide +kernel
  exact h a ⟨k,by omega⟩ hk0

include hs hl in
private theorem map_alternating (a : Bool) (k : ℕ) :
    f (roots.alternating a k) = weylRepresentative P rfl (wordIndex a k) := by
  induction k generalizing a with
  | zero => exact (map_one f).trans (weylRepresentative_one P rfl).symm
  | succ k ih =>
      have hr : f (roots.reflection a) =
          weylRepresentative P rfl (relativeReflection (if a then .arms else .central)) := by
        cases a
        · exact (map_nB f hl 1).trans ((SignedModel.nB_one n hn).trans
            (weylRepresentative_simple P rfl .central).symm)
        · exact (map_nA f hs 1).trans ((SignedModel.nA_one n hn).trans
            (weylRepresentative_simple P rfl .arms).symm)
      change f (roots.reflection a * roots.alternating (!a) k) = _
      rw [map_mul, hr, ih]
      exact (weylRepresentative_mul P rfl _ _).symm

include hs hl

/-- Root-preserving evaluation is faithful: the abstract cover reduces its kernel
first to the native identity cell and then to the faithful Borel coordinates.
The existence of this evaluation is a separate concrete-relation obligation. -/
theorem injective_of_root_images : Function.Injective f := by
  apply SignedRoots.injective_of_borel_and_weyl roots relations f (borel P) generates
  · intro b hb
    obtain ⟨v,p,rfl⟩ := (roots.mem_borel_iff relations b).mp hb
    rw [map_mul, map_product f hs hl, map_torus f hs hl, SignedModel.torus_eq]
    apply (borel P).mul_mem
    · apply unipotent_le_borel P
      rw [← native_positiveClosure n hn]
      exact ((nativePositiveRoots n hn).mem_positiveClosure_iff (native_relations n hn) _).mpr ⟨v,rfl⟩
    · exact torus_le_borel P (torusMulEquiv P rfl p).property
  · intro b hb h1
    obtain ⟨v,p,rfl⟩ := (roots.mem_borel_iff relations b).mp hb
    rw [map_mul, map_product f hs hl, map_torus f hs hl] at h1
    have he : (v,p) = (0,1) := SignedModel.borel_coordinates_injective n hn (by
      change (nativePositiveRoots n hn).product v * (SignedModel.roots n hn).torus p =
        (nativePositiveRoots n hn).product 0 * (SignedModel.roots n hn).torus 1
      rw [h1, PositiveRoots.product_zero, SignedModel.torus_one, mul_one])
    cases he
    rw [PositiveRoots.product_zero, one_mul]
    exact (roots.torusHom relations).map_one
  · intro a k hk hk0 hw
    rw [map_alternating f hs hl] at hw
    exact wordIndex_ne a k hk hk0 ((RelativeNormalizer.representative_mem_borel_iff n hn _).mp hw)

/-- The genuine model is generated by the images of the twelve signed roots. -/
theorem surjective_of_root_images : Function.Surjective f := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← native_generates (n := n) (hn := hn)]
  apply RootMembership.closure_le
  · intro s i t
    exact ⟨roots.shortSigned s i t,hs s i t⟩
  · intro s i t
    exact ⟨roots.longSigned s i t,hl s i t⟩

/-- A root-preserving homomorphism from the explicit presentation is an equivalence.
No injectivity, group order, or target simplicity is assumed. -/
def equivOfRootImages : Universal n hn ≃* BinaryCarrier n hn :=
  MulEquiv.ofBijective f (by exact ⟨injective_of_root_images f hs hl, surjective_of_root_images f hs hl⟩)

end Triality.Standard.RootPresentationRecognition.Presentation
