module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.Centralizers

/-!
# Six-coordinate identification of the hexad cocode fixed space

Even words on the actual source octad have two explicit images: their native
M22 cocode classes, and their restrictions to the six remaining coordinates
modulo constants. Restriction is onto, using stars through coordinate zero.
The pair word restricts to zero; the only supported Golay words are constants.
These facts, with rank-nullity, identify the two kernels and yield an explicit
linear equivalence. Equivariance is proved on representatives for the actual
native stabilizer permutations. The relative permutation kernel is detected
by the quotient pair classes.

Only the earlier M24 fixed dimension and element displacements, and the H.14
intrinsic kernel comparison and displacements, remain explicit in the fixed
space transfer. No M22 module identification is a premise. Identifying the
permutation images with A6 and S6 and the orthogonal duality are separate
steps; in particular no quadratic form is descended through the pair line.

Source: Aschbacher--Smith, H.15.2(2), printed pp.398--399,
combined manuscript of 1 March 2004.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
open scoped BigOperators Pointwise
namespace MathieuCode.Hexad.CocodeAction.SixPointModel
noncomputable section
abbrev O := m22SourceOctad
/-- The six actual coordinates remaining in the marked octad. -/
def coordinates : Finset (Fin 24) := O.val \ m22Pair
abbrev H := ↥coordinates
lemma card_H : Fintype.card H = 6 := by decide +kernel
instance : Nonempty H := ⟨⟨2, by decide +kernel⟩⟩
instance : Nonempty O.val := ⟨⟨0, by decide +kernel⟩⟩
def inOctad (i : H) : O.val := ⟨i.val, (Finset.mem_sdiff.mp i.property).1⟩
def anchor : O.val := ⟨0, by decide +kernel⟩
def partner : O.val := ⟨9, by decide +kernel⟩
def pairWord : BinaryPermutation.core O.val := CocodeOctad.starWord O.val anchor partner
lemma pairWord_cocode : CocodeOctad.toCocode O.val pairWord = m22PairClass := by
  rw [pairWord, CocodeOctad.starWord, CocodeOctad.toCocode_pair _ _ (by decide +kernel)]
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  change wordOfSet {partner.val, anchor.val} = m22PairWord
  rw [m22PairWord_eq_wordOfSet]
  congr 1
  exact Finset.pair_comm _ _
/-- Restrict an even octad word to its six remaining coordinates. -/
def restrict : BinaryPermutation.core O.val →ₗ[ZMod 2] BinaryPermutation.Full H where
  toFun v i := v.val (inOctad i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma restrict_pairWord : restrict pairWord = 0 := by
  ext i
  have hi := (Finset.mem_sdiff.mp i.property).2
  have ha : inOctad i ≠ anchor := by
    intro h
    apply hi
    have := congrArg Subtype.val h
    simp only [inOctad, anchor] at this
    simp [m22Pair, this]
  have hb : inOctad i ≠ partner := by
    intro h
    apply hi
    have := congrArg Subtype.val h
    simp only [inOctad, partner] at this
    simp [m22Pair, this]
  simp [restrict, pairWord, CocodeOctad.starWord, ha, hb]
/-- A star through coordinate zero lifts every six-coordinate word. -/
def lift : BinaryPermutation.Full H →ₗ[ZMod 2] BinaryPermutation.core O.val where
  toFun v := ∑ i : H, v i • CocodeOctad.starWord O.val anchor (inOctad i)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, mul_smul]
lemma restrict_lift (v : BinaryPermutation.Full H) : restrict (lift v) = v := by
  ext i
  have ha : inOctad i ≠ anchor := by
    intro h
    have hv := congrArg Subtype.val h
    have hi := (Finset.mem_sdiff.mp i.property).2
    exact hi (by simp [m22Pair, show i.val = 0 from hv])
  have he (j : H) : inOctad i = inOctad j ↔ i = j := by
    constructor
    · exact fun h => Subtype.ext (congrArg (fun x : O.val => x.val) h)
    · exact congrArg inOctad
  change (∑ j : H, v j • CocodeOctad.starWord O.val anchor (inOctad j)).val (inOctad i) = _
  simp [CocodeOctad.starWord, Finset.sum_apply, Pi.single_apply, ha, he]
lemma restrict_surjective : Function.Surjective restrict := fun v => ⟨lift v, restrict_lift v⟩
/-- The six-coordinate quotient map. -/
def toDeleted : BinaryPermutation.core O.val →ₗ[ZMod 2] BinaryPermutation.Deleted H :=
  (BinaryPermutation.constants H).mkQ.comp restrict
/-- Both actual cocode quotient maps, on supported even words. -/
def toM22 : BinaryPermutation.core O.val →ₗ[ZMod 2] M22Cocode :=
  m22PairLine.mkQ.comp (CocodeOctad.toCocode O.val)
lemma toDeleted_surjective : Function.Surjective toDeleted :=
  (BinaryPermutation.constants H).mkQ_surjective.comp restrict_surjective
lemma ker_toM22_le : toM22.ker ≤ toDeleted.ker := by
  intro v hv
  have hm : CocodeOctad.toCocode O.val v ∈ m22PairLine :=
    (Submodule.Quotient.mk_eq_zero m22PairLine).mp hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have hw : v - c • pairWord ∈ (CocodeOctad.toCocode O.val).ker := by
    change CocodeOctad.toCocode O.val (v - c • pairWord) = 0
    rw [map_sub, map_smul, pairWord_cocode, hc, sub_self]
  rw [CocodeOctad.ker_toCocode] at hw
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hw
  change (BinaryPermutation.constants H).mkQ (restrict v) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine Submodule.mem_span_singleton.mpr ⟨d, ?_⟩
  funext i
  have he := congrFun hd (inOctad i)
  have hz := congrFun restrict_pairWord i
  change pairWord.val (inOctad i) = 0 at hz
  simpa [BinaryPermutation.allOne, restrict, hz] using he
lemma range_toM22 : toM22.range = (supportedPairSpace O.val).map m22PairLine.mkQ := by
  rw [toM22, LinearMap.range_comp, CocodeOctad.range_toCocode]
lemma pairLine_le_supported : m22PairLine ≤ supportedPairSpace O.val := by
  apply Submodule.span_le.mpr
  rintro _ rfl
  rw [← pairWord_cocode, ← CocodeOctad.range_toCocode]
  exact LinearMap.mem_range_self _ _
lemma finrank_range_toM22 : Module.finrank (ZMod 2) toM22.range = 5 := by
  have h := HexadTransfer.finrank_map_add_ker m22PairLine.mkQ
    (supportedPairSpace O.val) (by rw [Submodule.ker_mkQ]; exact pairLine_le_supported)
  rw [Submodule.ker_mkQ, finrank_m22PairLine, CocodeOctad.finrank_supportedPairSpace,
    ← range_toM22] at h
  exact Nat.add_right_cancel h
/-- Equality of kernels of the two explicit maps, not an inferred module action. -/
lemma ker_toM22 : toM22.ker = toDeleted.ker := by
  apply Submodule.eq_of_le_of_finrank_eq ker_toM22_le
  have h₁ := toM22.finrank_range_add_finrank_ker
  have h₂ := toDeleted.finrank_range_add_finrank_ker
  rw [finrank_range_toM22] at h₁
  rw [LinearMap.range_eq_top.mpr toDeleted_surjective, finrank_top,
    BinaryPermutation.finrank_deleted, card_H] at h₂
  omega
/-- The actual image of the supported octad in the M22 cocode. -/
abbrev imageSpace := toM22.range
/-- Canonical identification induced by six-coordinate restriction. -/
def imageEquiv : imageSpace ≃ₗ[ZMod 2] BinaryPermutation.Deleted H :=
  toM22.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ ker_toM22).trans
      (toDeleted.quotKerEquivOfSurjective toDeleted_surjective))
lemma imageEquiv_apply (v : BinaryPermutation.core O.val) :
    imageEquiv ⟨toM22 v, LinearMap.mem_range_self _ _⟩ = toDeleted v := by
  simp only [imageEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivRange_symm_apply_image]
  rfl
variable {G : Type*} [Group G]
/-- The literal preimage of the marked octad stabilizer. -/
abbrev Stabilizer (f : G →* m22PairStabilizer) : Subgroup G :=
  (octadStabilizer O).comap (m22PairStabilizer.subtype.comp f)
def octadHom (f : G →* m22PairStabilizer) : Stabilizer f →* octadStabilizer O where
  toFun g := ⟨(f g.val).val, g.property⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
lemma preserves_coordinates (f : G →* m22PairStabilizer) (g : Stabilizer f) (i : Fin 24) :
    (f g.val).val.val i ∈ coordinates ↔ i ∈ coordinates := by
  simp only [coordinates, Finset.mem_sdiff]
  exact and_congr (MulAction.mem_stabilizer_finset.mp g.property i)
    (not_congr (MulAction.mem_stabilizer_finset.mp (f g.val).property i))
/-- Actual restriction of native permutations to the six remaining coordinates. -/
def coordinateAction (f : G →* m22PairStabilizer) : Stabilizer f →* Equiv.Perm H where
  toFun g := (f g.val).val.val.subtypePerm (preserves_coordinates f g)
  map_one' := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    change (f 1).val.val i.val = i.val
    rw [map_one]
    rfl
  map_mul' g h := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    change (f (g.val * h.val)).val.val i.val = (f g.val).val.val ((f h.val).val.val i.val)
    rw [map_mul]
    rfl
lemma coordinateAction_apply (f : G →* m22PairStabilizer) (g : Stabilizer f) (i : H) :
    (coordinateAction f g i).val = (f g.val).val.val i.val := rfl
lemma toDeleted_equivariant (f : G →* m22PairStabilizer) (g : Stabilizer f)
    (v : BinaryPermutation.core O.val) :
    toDeleted (BinaryPermutation.coreRepresentation O.val
        (CocodeOctad.coordinateAction O (octadHom f g)) v) =
      BinaryPermutation.deletedRepresentation H (coordinateAction f g) (toDeleted v) := rfl
lemma toM22_equivariant (f : G →* m22PairStabilizer) (g : Stabilizer f)
    (v : BinaryPermutation.core O.val) :
    toM22 (BinaryPermutation.coreRepresentation O.val
        (CocodeOctad.coordinateAction O (octadHom f g)) v) =
      quotientRepresentation f g.val (toM22 v) := by
  change m22PairLine.mkQ (CocodeOctad.toCocode O.val _) =
    m22PairLine.mkQ (cocodeRepresentation (f g.val).val (CocodeOctad.toCocode O.val v))
  rw [CocodeOctad.toCocode_equivariant]
  rfl
lemma imageSpace_invariant (f : G →* m22PairStabilizer) (g : Stabilizer f)
    {v : M22Cocode} (hv : v ∈ imageSpace) : quotientRepresentation f g.val v ∈ imageSpace := by
  obtain ⟨w, rfl⟩ := hv
  rw [← toM22_equivariant f g]
  exact LinearMap.mem_range_self _ _
/-- The restriction of the given M22 cocode action to the geometric image. -/
def imageRepresentation (f : G →* m22PairStabilizer) :
    Representation (ZMod 2) (Stabilizer f) imageSpace where
  toFun g := (quotientRepresentation f g.val).restrict (fun _ hv => imageSpace_invariant f g hv)
  map_one' := by
    ext v
    exact LinearMap.congr_fun (map_one (quotientRepresentation f)) v.val
  map_mul' g h := by
    ext v
    exact LinearMap.congr_fun (map_mul (quotientRepresentation f) g.val h.val) v.val
/-- The six-coordinate identification intertwines the actual cocode action. -/
lemma imageEquiv_equivariant (f : G →* m22PairStabilizer) (g : Stabilizer f)
    (v : imageSpace) :
    imageEquiv (imageRepresentation f g v) =
      BinaryPermutation.deletedRepresentation H (coordinateAction f g) (imageEquiv v) := by
  obtain ⟨w, hw⟩ := v.property
  have hv : v = ⟨toM22 w, LinearMap.mem_range_self _ _⟩ := Subtype.ext hw.symm
  subst v
  have he : imageRepresentation f g ⟨toM22 w, LinearMap.mem_range_self _ _⟩ =
      ⟨toM22 (BinaryPermutation.coreRepresentation O.val
        (CocodeOctad.coordinateAction O (octadHom f g)) w), LinearMap.mem_range_self _ _⟩ :=
    Subtype.ext (toM22_equivariant f g w).symm
  rw [he, imageEquiv_apply, imageEquiv_apply, toDeleted_equivariant]
/-- Supported pair classes are fixed by the actual marked kernel. -/
lemma imageSpace_le_fixed {f : G →* m22PairStabilizer} {K : Subgroup G}
    (hK : K.map (m22PairStabilizer.subtype.comp f) = octadPointwiseKernel O) :
    imageSpace ≤ fixedSpace (quotientRepresentation f) K := by
  rw [show imageSpace = (supportedPairSpace O.val).map m22PairLine.mkQ from range_toM22,
    Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨P, hP, rfl⟩
  exact quotient_pair_mem_fixedSpace hK P hP
/-- The scalar M24 inputs identify the common fixed space with the explicit image.
No module recognition is imposed as a premise. -/
lemma fixedSpace_eq_image {f : G →* m22PairStabilizer} {K : Subgroup G}
    (h : RestrictionInput f K O)
    (hd : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (h6 : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (octadPointwiseKernel O)) = 6) :
    fixedSpace (quotientRepresentation f) K = imageSpace := by
  symm
  exact Submodule.eq_of_le_of_finrank_eq (imageSpace_le_fixed h.kernel_image)
    (finrank_range_toM22.trans (h.fixedSpace_finrank hd h6).symm)
/-- The actual common fixed space is the six-point deleted permutation module. -/
def fixedEquiv {f : G →* m22PairStabilizer} {K : Subgroup G}
    (h : RestrictionInput f K O)
    (hd : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (h6 : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (octadPointwiseKernel O)) = 6) :
    fixedSpace (quotientRepresentation f) K ≃ₗ[ZMod 2] BinaryPermutation.Deleted H :=
  (LinearEquiv.ofEq _ _ (fixedSpace_eq_image h hd h6)).trans imageEquiv
lemma fixedEquiv_apply {f : G →* m22PairStabilizer} {K : Subgroup G}
    (h : RestrictionInput f K O)
    (hd : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (h6 : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (octadPointwiseKernel O)) = 6)
    (v : BinaryPermutation.core O.val) :
    fixedEquiv h hd h6 ⟨toM22 v, imageSpace_le_fixed h.kernel_image (LinearMap.mem_range_self _ _)⟩ =
      (BinaryPermutation.constants H).mkQ (restrict v) := imageEquiv_apply v
lemma fixedSpace_invariant {f : G →* m22PairStabilizer} {K : Subgroup G}
    (h : RestrictionInput f K O)
    (hd : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (h6 : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (octadPointwiseKernel O)) = 6)
    (g : Stabilizer f) {v : M22Cocode} (hv : v ∈ fixedSpace (quotientRepresentation f) K) :
    quotientRepresentation f g.val v ∈ fixedSpace (quotientRepresentation f) K := by
  rw [fixedSpace_eq_image h hd h6] at hv ⊢
  exact imageSpace_invariant f g hv
lemma fixedEquiv_equivariant {f : G →* m22PairStabilizer} {K : Subgroup G}
    (h : RestrictionInput f K O)
    (hd : ∀ z ∈ octadPointwiseKernel O, z ≠ 1 →
      fixedCodim cocodeRepresentation (Subgroup.zpowers z) = 4)
    (h6 : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (octadPointwiseKernel O)) = 6)
    (g : Stabilizer f) (v : fixedSpace (quotientRepresentation f) K) :
    fixedEquiv h hd h6 ⟨quotientRepresentation f g.val v.val,
        fixedSpace_invariant h hd h6 g v.property⟩ =
      BinaryPermutation.deletedRepresentation H (coordinateAction f g) (fixedEquiv h hd h6 v) :=
  imageEquiv_equivariant f g ⟨v.val, (fixedSpace_eq_image h hd h6) ▸ v.property⟩
/-- The six-coordinate action has exactly the relative intrinsic kernel,
using the genuine H.14 kernel image comparison. -/
lemma coordinateAction_ker {f : G →* m22PairStabilizer} {K : Subgroup G}
    (hf : Function.Injective f)
    (hK : K.map (m22PairStabilizer.subtype.comp f) = octadPointwiseKernel O) :
    (coordinateAction f).ker = K.subgroupOf (Stabilizer f) := by
  ext g
  change coordinateAction f g = 1 ↔ g.val ∈ K
  constructor
  · intro hg
    have hfix (i : Fin 24) (hi : i ∈ coordinates) : (f g.val).val • i = i :=
      congrArg Subtype.val (Equiv.congr_fun hg ⟨i, hi⟩)
    have hm : (f g.val).val ∈ octadPointwiseKernel O := by
      apply octad_kernel_of_quotient_pairs_fixed O m22Pair_le_sourceOctad (f g.val)
      intro P hP
      change m22PairLine.mkQ (cocodeRepresentation (f g.val).val (pairVector P)) = _
      congr 1
      apply (pairVector_fixed_iff _ _).mpr
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_smul_finset.mp hi
        rwa [hfix j (hP hj)]
      · intro hi
        exact Finset.mem_smul_finset.mpr ⟨i, hi, hfix i (hP hi)⟩
    rw [← hK] at hm
    obtain ⟨a, ha, he⟩ := hm
    exact (Subtype.val_injective.comp hf) he ▸ ha
  · intro hg
    have hm : (f g.val).val ∈ octadPointwiseKernel O := by
      rw [← hK]
      exact Subgroup.mem_map_of_mem _ hg
    apply Equiv.ext
    intro i
    exact Subtype.ext ((mem_octadPointwiseKernel O _).mp hm i.val
      (Finset.mem_sdiff.mp i.property).1)
/-- The outer action is on the literal setwise pair stabilizer. -/
abbrev outerCoordinateAction : m22OuterHexadStabilizer O →* Equiv.Perm H :=
  coordinateAction (MonoidHom.id m22PairStabilizer)
/-- The inner action uses the native M22 embedding, fixing both pair points. -/
abbrev innerCoordinateAction : m22InnerHexadStabilizer O →* Equiv.Perm H :=
  coordinateAction m22ToPairStabilizer
end
end MathieuCode.Hexad.CocodeAction.SixPointModel
