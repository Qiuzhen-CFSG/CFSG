module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.Normalizer
public import Theory.ElementaryAbelian.Injective
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.Noninvolutions
/-!
# Center bounds from the actual Mathieu image

Every subgroup between the self-centralizing binary kernel and max1 has its
center equal to its full ambient centralizer. Centers of Mathieu preimages
therefore decrease as the image grows. The certified binary mask action bounds
the product of a nontrivial elementary image's order and its preimage center
by 1024. Only the quotient image needs to be elementary; the lifted two-group
need not be abelian. The non-involution fixed-space sieve forces the whole
Mathieu image of a radical with center of order at least 64 to be elementary;
the product bound then makes its order at most 16.

This supplies a selective local bound in the radical strategy of
An--O'Brien--Wilson (2003), Section 4 and Table 1, pp.122,124. The finite input
is the native action calculation used for Kleidman--Wilson (1988), Lemma
1.1.2(i). This does not classify the remaining images or give global placement.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
open ElementaryNormalizerCover MathieuHallActors SylowCore SylowCore.Transport
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.localKernel Cardinality.max1Subgroup

private def imageEquiv {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : G →* K) (hk : f.ker = g.ker) (A : Subgroup G) :
    A.map f ≃* A.map g := by
  let a := f.subgroupMap A
  let b := g.subgroupMap A
  have h : a.ker = b.ker := by
    ext x
    change (a x = 1) ↔ (b x = 1)
    simp only [Subtype.ext_iff]
    change x.val ∈ f.ker ↔ x.val ∈ g.ker
    rw [hk]
  exact (QuotientGroup.quotientKerEquivOfSurjective a (f.subgroupMap_surjective A)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans
      (QuotientGroup.quotientKerEquivOfSurjective b (g.subgroupMap_surjective A)))

private theorem local_image_alignment (U : Subgroup max1) (hp : IsPGroup 2 U)
    (hE : kernel ≤ U) :
    ∃ B : Subgroup Simplicity.Max1Fusion.QuotientInvolutions.sylowCandidate,
      Nonempty (B ≃* U.map projection) ∧ Nat.card (center U) ≤ Nat.card (FixedMasks B) := by
  obtain ⟨S,hUS⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := exists_alignment S
  let A := U.subgroupOf S.toSubgroup
  let f := alignedHom S g hg
  let q := projection.comp S.toSubgroup.subtype
  have hk : f.ker = q.ker := by
    rw [alignedHom_ker]
    ext x
    change x.val ∈ kernel ↔ projection x.val = 1
    change x.val ∈ Cardinality.localKernel matrixA_mul_self matrixB_pow_four ↔ _
    rw [← projection_ker]
    rfl
  let e := imageEquiv f q hk A
  have hi : A.map q = U.map projection := by
    rw [show A.map q = (A.map S.toSubgroup.subtype).map projection from
      (map_map A projection S.toSubgroup.subtype).symm, map_subgroupOf_eq_of_le hUS]
  let eqi : A.map f ≃* U.map projection := e.trans (MulEquiv.subgroupCongr hi)
  have hzE (z : center U) : z.val.val ∈ kernel := by
    change z.val.val ∈ Cardinality.localKernel matrixA_mul_self matrixB_pow_four
    rw [← centralizer_localKernel matrixA_mul_self matrixB_pow_four]
    intro v hv
    exact congrArg U.subtype (mem_center_iff.mp z.property ⟨v,hE hv⟩)
  let j : center U → (centralizer (A : Set S)).subgroupOf (core S) := fun z =>
    ⟨⟨⟨z.val.val,hUS z.val.property⟩,hzE z⟩,by
      intro a ha
      apply Subtype.ext
      exact congrArg U.subtype (mem_center_iff.mp z.property ⟨a.val,ha⟩)⟩
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val.val.val) h))
  have hc := (Nat.card_le_card_of_injective j hj).trans (centralizer_card_le_fixedMasks S A g hg)
  exact ⟨A.map f, ⟨eqi⟩, hc⟩

/-- Elementary quotient images bound their full kernel centralizers; the lift need not be elementary. -/
theorem local_elementary_image_center_bound (U : Subgroup max1) (hp : IsPGroup 2 U)
    (hE : kernel ≤ U) [IsElementaryAbelian 2 (U.map projection)]
    (hne : U.map projection ≠ ⊥) :
    Nat.card (U.map projection) * Nat.card (center U) ≤ 1024 := by
  obtain ⟨B,⟨e⟩,hc⟩ := local_image_alignment U hp hE
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hBn : B ≠ ⊥ := by
    intro hb
    have hh := Nat.card_congr e.toEquiv
    rw [hb,card_bot] at hh
    exact hne (card_eq_one.mp hh.symm)
  rw [← Nat.card_congr e.toEquiv]
  exact (Nat.mul_le_mul_left _ hc).trans (ElementaryBound.elementary_fixed_bound B hBn)

/-- A center of order greater than sixteen forces the actual Mathieu image to be elementary. -/
theorem local_large_center_image_elementary (U : Subgroup max1) (hp : IsPGroup 2 U)
    (hE : kernel ≤ U) (hlarge : 16 < Nat.card (center U)) :
    IsElementaryAbelian 2 (U.map projection) := by
  obtain ⟨B,⟨e⟩,hc⟩ := local_image_alignment U hp hE
  let : IsElementaryAbelian 2 B := Noninvolutions.elementary_of_large_fixed B (hlarge.trans_le hc)
  exact IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective

/-- The center is the whole ambient centralizer for every overgroup of E in max1. -/
theorem preimage_center_map (A : Subgroup Sporadic.Mathieu.M24) :
    (center (preimage A)).map (preimage A).subtype = centralizer (preimage A : Set Model) := by
  apply le_antisymm
  · rintro _ ⟨z,hz,rfl⟩ y hy
    exact congrArg (preimage A).subtype (mem_center_iff.mp hz ⟨y,hy⟩)
  · intro z hz
    have hE : z ∈ embeddedKernel := by
      change z ∈ (Cardinality.localKernel matrixA_mul_self matrixB_pow_four).map max1.subtype
      rw [← centralizer_embedded_localKernel]
      exact centralizer_le (kernel_le_preimage A) hz
    exact ⟨⟨z,kernel_le_preimage A hE⟩,mem_center_iff.mpr (fun y =>
      Subtype.ext (hz y y.property)),rfl⟩

theorem preimage_center_card_antitone {A B : Subgroup Sporadic.Mathieu.M24} (h : A ≤ B) :
    Nat.card (center (preimage B)) ≤ Nat.card (center (preimage A)) := by
  have hh := card_le_of_le (centralizer_le (map_mono (comap_mono h) : preimage A ≤ preimage B))
  change Nat.card (centralizer (preimage B : Set Model)) ≤ Nat.card (centralizer (preimage A : Set Model)) at hh
  rw [← preimage_center_map, ← preimage_center_map,
    card_map_of_injective (preimage A).subtype_injective,
    card_map_of_injective (preimage B).subtype_injective] at hh
  exact hh

theorem elementary_preimage_center_bound (A : Subgroup Sporadic.Mathieu.M24)
    [IsElementaryAbelian 2 A] (hne : A ≠ ⊥) :
    Nat.card A * Nat.card (center (preimage A)) ≤ 1024 := by
  have hk : IsPGroup 2 projection.ker := by
    rw [projection_ker,localKernel_eq_twoCore]
    exact pCore_isPGroup
  have hp := (IsElementaryAbelian.isPGroup 2 A).comap_of_ker_isPGroup projection hk
  have hE : kernel ≤ A.comap projection := by
    change Cardinality.localKernel matrixA_mul_self matrixB_pow_four ≤ _
    rw [← projection_ker]
    exact MonoidHom.ker_le_comap projection A
  have hi : (A.comap projection).map projection = A :=
    map_comap_eq_self_of_surjective projection_surjective A
  let : IsElementaryAbelian 2 ((A.comap projection).map projection) := hi.symm ▸ inferInstance
  have hb := local_elementary_image_center_bound (A.comap projection) hp hE (hi.symm ▸ hne)
  rw [hi] at hb
  let e : A.comap projection ≃* preimage A :=
    (A.comap projection).equivMapOfInjective max1.subtype max1.subtype_injective
  rwa [Nat.card_congr (centerCongr e).toEquiv] at hb

/-- Every elementary subgroup of the actual Mathieu image has order at most sixteen. -/
theorem radical_mathieu_elementary_image_bound (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ max1) (hlarge : 64 ≤ Nat.card (center P))
    (A : Subgroup Sporadic.Mathieu.M24) [IsElementaryAbelian 2 A]
    (hA : A ≤ (P.subgroupOf max1).map projection) : Nat.card A ≤ 16 := by
  by_cases hn : A = ⊥
  · simp [hn]
  have hz := preimage_center_card_antitone hA
  rw [← radical_eq_preimage P hP hN] at hz
  have hb := elementary_preimage_center_bound A hn
  have hc : 64 ≤ Nat.card (center (preimage A)) := hlarge.trans hz
  have hm := (Nat.mul_le_mul_left (Nat.card A) hc).trans hb
  omega

/-- The whole Mathieu image of a large-center radical is elementary and has order at most sixteen. -/
theorem radical_mathieu_image_small (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ max1) (hlarge : 64 ≤ Nat.card (center P)) :
    IsElementaryAbelian 2 ((P.subgroupOf max1).map projection) ∧
      Nat.card ((P.subgroupOf max1).map projection) ≤ 16 := by
  have hPM := P.le_normalizer.trans hN
  have hE : kernel ≤ P.subgroupOf max1 := by
    intro x hx
    exact kernel_le_radical P hP hN (mem_map_of_mem max1.subtype hx)
  have hc : 16 < Nat.card (center (P.subgroupOf max1)) := by
    rw [Nat.card_congr (centerCongr (subgroupOfEquivOfLe hPM)).toEquiv]
    omega
  let hElem := local_large_center_image_elementary (P.subgroupOf max1)
    (hP.isPGroup.comap_of_injective max1.subtype max1.subtype_injective) hE hc
  let := hElem
  exact ⟨hElem, radical_mathieu_elementary_image_bound P hP hN hlarge _ le_rfl⟩

end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
