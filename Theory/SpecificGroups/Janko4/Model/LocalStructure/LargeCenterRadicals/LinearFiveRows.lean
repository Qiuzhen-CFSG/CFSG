module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.NativeLinearFive
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Arbitrary radicals inside the recognized linear-five local

Radical saturation forces F into any radical P whose full normalizer lies
in N(F). The actual native projection then gives a radical core equation in
SL₅(2), and its restricted normalizer map identifies the two full intrinsic
quotients. The original center is in bijection with the fixed space under
the same exterior marking. Thus the large-center condition becomes an exact
fixed-space condition on the literal image; the trivial image is the F row.
The classification of nontrivial images remains to be proved.

Source: An--O'Brien--Wilson (2003), Section 4 and Table 1, pp.122,124;
Kleidman--Wilson (1988), Lemma 1.1.1, for the native exterior action.
-/

@[expose] public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals.LinearFiveRows
open LinearFive
open Representation.SL5TenDimensional Representation.SL5ExteriorSquare
attribute [local irreducible] modelGroup matrixA matrixB
private instance exteriorFinite : Finite V :=
  Finite.of_equiv (Fin 10 → ZMod 2) Representation.SL5ExteriorSquare.coordinates.symm.toEquiv

/-- Saturation puts the full elementary core F in every placed radical. -/
theorem F_le_radical (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer) : F ≤ P := by
  have h := le_of_normalizer_le_normalizer_of_pCore_normalizer_le P (fullNormalizer.pCoreIn 2)
    hP.isPGroup (isPGroup_pCoreIn 2 fullNormalizer) hP.2.le
    (hN.trans (fullNormalizer.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image fullNormalizer (pCore 2 fullNormalizer))))
  rwa [F_ambient_twoCore] at h

/-- The literal SL5 image under the recognized native normalizer projection. -/
abbrev image (P : Subgroup Model) : Subgroup Group :=
  (P.subgroupOf fullNormalizer).map normalizerProjection

private theorem kernel_le_restriction (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer) :
    normalizerProjection.ker ≤ P.subgroupOf fullNormalizer := by
  rw [normalizerProjection_ker]
  intro x hx
  exact F_le_radical P hP hN hx

/-- Placed radicals are the full preimages of their actual linear images. -/
theorem radical_eq_preimage (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer) :
    P = ((image P).comap normalizerProjection).map fullNormalizer.subtype := by
  rw [image, comap_map_eq_self (kernel_le_restriction P hP hN),
    map_subgroupOf_eq_of_le (P.le_normalizer.trans hN)]

/-- The SL5 image has the full radical core equation, including the trivial-image case. -/
theorem image_core (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer) :
    (normalizer (image P : Set Group)).pCoreIn 2 = image P := by
  have hr := hP.subgroupOf_of_normalizer_normalizes fullNormalizer
    (P.le_normalizer.trans hN) (hN.trans fullNormalizer.le_normalizer)
  exact map_normalizer_core_of_p_kernel _ hr.isPGroup hr.2 normalizerProjection
    normalizerProjection_surjective (kernel_le_restriction P hP hN)

/-- The trivial linear image identifies the actual native radical F. -/
theorem radical_eq_F_of_image_bot (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer) (hi : image P = ⊥) : P = F := by
  rw [radical_eq_preimage P hP hN, hi]
  change normalizerProjection.ker.map fullNormalizer.subtype = F
  rw [normalizerProjection_ker]
  exact map_subgroupOf_eq_of_le F.le_normalizer

private theorem normalizer_image (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer) :
    (normalizer (P.subgroupOf fullNormalizer : Set fullNormalizer)).map normalizerProjection =
      normalizer (image P : Set Group) := by
  have he : (normalizer (image P : Set Group)).comap normalizerProjection =
      normalizer (P.subgroupOf fullNormalizer : Set fullNormalizer) := by
    rw [comap_normalizer_eq_of_surjective _ normalizerProjection_surjective,
      image, comap_map_eq_self (kernel_le_restriction P hP hN)]
  rw [← he, map_comap_eq_self_of_surjective normalizerProjection_surjective]

/-- The whole ambient normalizer quotient is the full intrinsic quotient of
its actual SL5 image normalizer. -/
def radicalNormalizerQuotientEquiv (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer) :
    let N := normalizer (P : Set Model)
    let H := normalizer (image P : Set Group)
    N ⧸ pCore 2 N ≃* H ⧸ pCore 2 H := by
  let H := normalizer (P.subgroupOf fullNormalizer : Set fullNormalizer)
  let f := normalizerProjection.subgroupMap H
  have hk : f.ker = normalizerProjection.ker.comap H.subtype := by
    ext x
    exact Subtype.ext_iff
  have hp : IsPGroup 2 f.ker := by
    rw [hk, normalizerProjection_ker]
    exact normalizerKernel_isPGroup.comap_of_injective _ H.subtype_injective
  let e := (subgroupOfEquivOfLe hN).symm.trans
    (MulEquiv.subgroupCongr (subgroupOf_normalizer_eq (P.le_normalizer.trans hN)))
  exact (MathieuRows.coreQuotientCongr e).trans
    ((f.quotientPCoreEquivOfSurjective (normalizerProjection.subgroupMap_surjective H) hp).trans
      (MathieuRows.coreQuotientCongr (MulEquiv.subgroupCongr (by exact normalizer_image P hP hN))))

private theorem center_mem_F (P : Subgroup Model) (hFP : F ≤ P) (z : center P) :
    (z : P).val ∈ F := by
  rw [← centralizer_F]
  intro x hx
  exact congrArg P.subtype (mem_center_iff.mp z.property ⟨x,hFP hx⟩)

/-- The center embeds into the fixed space under the very same native exterior marking. -/
def centerFixedMap (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer) :
    center P → Representation.BinaryOffender.fixedSpace (exteriorAction 2) (image P) :=
  by
    intro z
    let x : F := ⟨(z : P).val, by exact center_mem_F P (F_le_radical P hP hN) z⟩
    refine ⟨(exteriorMarking x).toAdd, ?_⟩
    intro a
    obtain ⟨n,hn,he⟩ := a.property
    change exteriorAction 2 a.val _ = _
    rw [← he, ← normalizerProjection_exterior]
    have hx : F.normalizerMonoidHom n x = x := by
      apply Subtype.ext
      change n.val * (z : P).val * n.val⁻¹ = (z : P).val
      have hz : n.val * (z : P).val = (z : P).val * n.val :=
        congrArg P.subtype (mem_center_iff.mp z.property ⟨n.val,hn⟩)
      rw [hz, mul_assoc, mul_inv_cancel, mul_one]
    rw [hx]

theorem centerFixedMap_injective (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer) :
    Function.Injective (centerFixedMap P hP hN) := by
  intro x y h
  have he := congrArg (fun z => Multiplicative.ofAdd z.val) h
  have hf := exteriorMarking.injective he
  have hh : (x : P).val = (y : P).val := congrArg (fun t : F => (t : Model)) hf
  exact Subtype.ext (Subtype.ext hh)

/-- Every fixed vector lifts to an element of the actual center, not just to
an abstract subgroup of matching order. -/
theorem centerFixedMap_surjective (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer) :
    Function.Surjective (centerFixedMap P hP hN) := by
  intro v
  let x : F := exteriorMarking.symm (Multiplicative.ofAdd v.val)
  have hFP := F_le_radical P hP hN
  have hx (p : P) : p.val * x.val = x.val * p.val := by
    let n : fullNormalizer := ⟨p.val, (P.le_normalizer.trans hN) p.property⟩
    have hv := v.property ⟨normalizerProjection n, ⟨n,p.property,rfl⟩⟩
    change exteriorAction 2 (normalizerProjection n) v.val = v.val at hv
    have ha : F.normalizerMonoidHom n x = x := by
      apply exteriorMarking.injective
      apply Multiplicative.toAdd.injective
      rw [normalizerProjection_exterior]
      simpa only [x, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hv
    have hh := congrArg F.subtype ha
    change p.val * x.val * p.val⁻¹ = x.val at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  let z : center P := ⟨⟨x.val,hFP x.property⟩, mem_center_iff.mpr
    (fun p => Subtype.ext (hx p))⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change (exteriorMarking x).toAdd = v.val
  exact congrArg Multiplicative.toAdd (exteriorMarking.apply_symm_apply _)

/-- Exact equality of the original center size with the exterior fixed-space size. -/
theorem center_card_eq_fixedSpace (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer) :
    Nat.card (center P) =
      Nat.card (Representation.BinaryOffender.fixedSpace (exteriorAction 2) (image P)) :=
  Nat.card_congr (Equiv.ofBijective (centerFixedMap P hP hN)
    ⟨centerFixedMap_injective P hP hN, centerFixedMap_surjective P hP hN⟩)

/-- The original center bound applies to the literal SL5 image and exterior action. -/
theorem large_fixedSpace (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer)
    (hlarge : 64 ≤ Nat.card (center P)) :
    64 ≤ Nat.card (Representation.BinaryOffender.fixedSpace (exteriorAction 2) (image P)) :=
  hlarge.trans (Nat.card_le_card_of_injective _ (centerFixedMap_injective P hP hN))

/-- The arbitrary placed radical either has the required native quotient
already, or leaves a nontrivial radical SL5 image with the literal large fixed
space and full normalizer quotient. This is the remaining local row problem. -/
theorem radical_quotient_or_nontrivial_image (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ fullNormalizer)
    (hlarge : 64 ≤ Nat.card (center P)) :
    Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃* Group) ∨
      (image P).IsPRadical 2 ∧
      64 ≤ Nat.card (Representation.BinaryOffender.fixedSpace (exteriorAction 2) (image P)) ∧
      Nonempty ((normalizer (P : Set Model) ⧸ pCore 2 (normalizer (P : Set Model))) ≃*
        (normalizer (image P : Set Group) ⧸ pCore 2 (normalizer (image P : Set Group)))) := by
  by_cases hi : image P = ⊥
  · left
    have he := radical_eq_F_of_image_bot P hP hN hi
    subst P
    exact ⟨intrinsicNormalizerQuotient⟩
  · exact Or.inr ⟨⟨hi,image_core P hP hN⟩,large_fixedSpace P hP hN hlarge,
      ⟨radicalNormalizerQuotientEquiv P hP hN⟩⟩

end Janko4.LocalStructure.LargeCenterRadicals.LinearFiveRows
