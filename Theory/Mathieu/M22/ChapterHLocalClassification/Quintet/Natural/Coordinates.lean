module

public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Translations
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeKernelTransitivity
public import Theory.AtlasPort.OtherSporadic.Mathieu.TetradPointwiseStabilizer
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Native coordinate-zero translations and their geometric actor

The source affine coordinates send the two deleted native points 0 and 9 to
rows 0 and 1 of the first tetrad. Fixing the first point is exactly vanishing
of the corresponding hexacode coordinate. Thus the sixteen coordinate-zero
words are the literal inner translation group, with its actual binary
conjugation representation.

The pointwise stabilizer of that source tetrad embeds in the native quintet
stabilizer Q. Its quotient by the literal inner translations is the local
hexacode kernel, via the original sextet quotient. The conjugation intertwiner
and transitivity of the local kernel on the fifteen nonzero words prove
irreducibility for the full Q action. The matrix identification is assembled
in `Quintet.Natural`; no intrinsic two-core equality is assumed here.

Source: Aschbacher--Smith H.14.3(2), printed p.397, and the source marking on
p.396. The affine and local hexacode results reuse the licensed ATLAS ports
of Gerald Höhn and ATLAS contributors, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`; see `LICENSES/ATLAS.txt` and the
attribution in the imported port modules. No new port is used here.
-/

public section

noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode MathieuCode.M22Quintet
open Atlas.Codes
open scoped Pointwise IsMulCommutative
namespace Sporadic.Mathieu.M22ChapterH.Quintet
open Sextet

/-- The coordinates in the pair-compatible source sextet. -/
def naturalPointCoordinates : Omega ≃ Fin 24 :=
  atlasPointEquiv.trans m22GeometryConjugator.val

abbrev naturalIndex : HexIndex := firstThree 0

@[simp] theorem naturalPointCoordinates_zero : naturalPointCoordinates (naturalIndex, 0) = 0 := by
  decide +kernel
@[simp] theorem naturalPointCoordinates_nine : naturalPointCoordinates (naturalIndex, 1) = 9 := by
  decide +kernel

/-- The literal affine model in the source sextet stabilizer. -/
def naturalAffineEquiv : SextetAffineGroup ≃* sextetStabilizer m22SourceSextet :=
  (sextetAffineEquiv.trans SextetCore.sextetEquiv.symm).trans sourceStabilizerEquiv

private theorem sourceStabilizer_points (g : sextetStabilizer standardSextet) (p : Fin 24) :
    (sourceStabilizerEquiv g).val.val (m22GeometryConjugator.val p) =
      m22GeometryConjugator.val (g.val.val p) := by
  rw [sourceStabilizerEquiv_coe]
  generalize m22GeometryConjugator = c
  change c.val (g.val.val (c.val.symm (c.val p))) = c.val (g.val.val p)
  rw [Equiv.symm_apply_apply]

private theorem atlasStabilizer_points (g : SextetStabilizer) (p : Omega) :
    (SextetCore.sextetEquiv.symm g).val.val (atlasPointEquiv p) =
      atlasPointEquiv (g.val.val p) := by
  have h := congrArg (fun g : SextetStabilizer => g.val.val p)
    (SextetCore.sextetEquiv.apply_symm_apply g)
  change atlasPointEquiv.symm
    ((SextetCore.sextetEquiv.symm g).val.val (atlasPointEquiv p)) = _ at h
  exact (atlasPointEquiv.symm_apply_eq).mp h

theorem naturalAffineEquiv_points (x : SextetAffineGroup) (p : Omega) :
    (naturalAffineEquiv x).val.val (naturalPointCoordinates p) =
      naturalPointCoordinates ((sextetAffineEquiv x).val.val p) := by
  dsimp only [naturalAffineEquiv, MulEquiv.trans_apply, naturalPointCoordinates, Equiv.trans_apply]
  rw [sourceStabilizer_points, atlasStabilizer_points]

@[simp] theorem naturalAffineEquiv_translation (w : Multiplicative hexacode) :
    (naturalAffineEquiv (SemidirectProduct.inl w)).val = (sourceTranslationEquiv w).val := (rfl)

theorem sourceTranslation_points (w : Multiplicative hexacode) (i : HexIndex) (k : Fin 4) :
    (sourceTranslationEquiv w).val.val (naturalPointCoordinates (i,k)) =
      naturalPointCoordinates (i, rowLabel.symm (rowLabel k + w.toAdd.val i)) := by
  rw [← naturalAffineEquiv_translation]
  exact (naturalAffineEquiv_points (SemidirectProduct.inl w) (i,k)).trans
    (congrArg naturalPointCoordinates (sextetTranslation_coordinates w i k))

set_option maxRecDepth 4096 in
/-- Fixing the native deleted point is exactly the zero-coordinate condition. -/
theorem sourceTranslation_fixed_zero_iff (w : Multiplicative hexacode) :
    (sourceTranslationEquiv w).val.val 0 = 0 ↔ w.toAdd.val naturalIndex = 0 := by
  rw [← naturalPointCoordinates_zero, sourceTranslation_points,
    naturalPointCoordinates.injective.eq_iff]
  change (naturalIndex, rowLabel.symm (0 + w.toAdd.val naturalIndex)) = (naturalIndex, 0) ↔ _
  simp only [zero_add, Prod.mk.injEq, true_and]
  rw [Equiv.symm_apply_eq]
  rfl

private theorem zero_word_fixed (w : hexZeroCoordinate naturalIndex) (k : Fin 4) :
    (sourceTranslationEquiv (Multiplicative.ofAdd w.val)).val.val
      (naturalPointCoordinates (naturalIndex,k)) = naturalPointCoordinates (naturalIndex,k) := by
  rw [sourceTranslation_points]
  have hw : w.val.val naturalIndex = 0 := w.property
  simp only [Multiplicative.toAdd, Equiv.symm_apply_apply]
  rw [hw, add_zero, rowLabel.symm_apply_apply]

private theorem fixes_pair_mem (g : M24) (h0 : g.val 0 = 0) (h9 : g.val 9 = 9) :
    g ∈ m22PairStabilizer := by
  change m22Pair.image g.val = m22Pair
  simp only [m22Pair, Finset.image_insert, Finset.image_singleton, h0, h9]

private def translationAmbient : Multiplicative (hexZeroCoordinate naturalIndex) →* M24 :=
  sourceCore.subtype.comp (sourceTranslationEquiv.toMonoidHom.comp (hexZeroInclusion naturalIndex))

private theorem translationAmbient_apply (w : Multiplicative (hexZeroCoordinate naturalIndex)) :
    translationAmbient w = (sourceTranslationEquiv (Multiplicative.ofAdd w.toAdd.val)).val := (rfl)

private theorem translationAmbient_fixed (w : Multiplicative (hexZeroCoordinate naturalIndex)) :
    (translationAmbient w).val 0 = 0 ∧ (translationAmbient w).val 9 = 9 := by
  rw [translationAmbient_apply]
  constructor
  · simpa only [naturalPointCoordinates_zero] using zero_word_fixed w.toAdd 0
  · simpa only [naturalPointCoordinates_nine] using zero_word_fixed w.toAdd 1

private def translationPair : Multiplicative (hexZeroCoordinate naturalIndex) →* m22PairStabilizer :=
  translationAmbient.codRestrict _ (fun w =>
    fixes_pair_mem _ (translationAmbient_fixed w).1 (translationAmbient_fixed w).2)

/-- Coordinate-zero words as actual inner native translations. -/
def naturalTranslation : Multiplicative (hexZeroCoordinate naturalIndex) →* innerTranslationGroup :=
  translationPair.codRestrict _ (fun w =>
    ⟨(sourceTranslationEquiv (Multiplicative.ofAdd w.toAdd.val)).property,
      (m22ToPairStabilizer_mem_range_iff_fixed_zero _).mpr (translationAmbient_fixed w).1⟩)

@[simp] theorem naturalTranslation_coe (w : Multiplicative (hexZeroCoordinate naturalIndex)) :
    (naturalTranslation w).val.val =
      (sourceTranslationEquiv (Multiplicative.ofAdd w.toAdd.val)).val := (rfl)

theorem naturalTranslation_bijective : Function.Bijective naturalTranslation := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro u v h
    have hv : (sourceTranslationEquiv (Multiplicative.ofAdd u.toAdd.val)).val =
        (sourceTranslationEquiv (Multiplicative.ofAdd v.toAdd.val)).val :=
      by simpa only [naturalTranslation_coe] using congrArg (fun x : innerTranslationGroup => x.val.val) h
    have h' := sourceTranslationEquiv.injective (Subtype.ext hv)
    exact congrArg Multiplicative.ofAdd (Subtype.ext (congrArg Multiplicative.toAdd h'))
  · rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (hexZeroCoordinate naturalIndex) ≃ _),
      hexZeroCoordinate_card, innerTranslationGroup_card]

def naturalTranslationEquiv : Multiplicative (hexZeroCoordinate naturalIndex) ≃* innerTranslationGroup :=
  MulEquiv.ofBijective naturalTranslation naturalTranslation_bijective

/-- The native binary coordinates are induced by the translation isomorphism. -/
def innerTranslationCoordinates : Additive innerTranslationGroup ≃ₗ[ZMod 2]
    hexZeroCoordinate naturalIndex :=
  { naturalTranslationEquiv.symm.toAdditiveLeft with
    map_smul' c v := by
      fin_cases c
      · change naturalTranslationEquiv.symm.toAdditiveLeft ((0 : ZMod 2) • v) = (0 : ZMod 2) • _
        simp
      · change naturalTranslationEquiv.symm.toAdditiveLeft ((1 : ZMod 2) • v) = (1 : ZMod 2) • _
        simp }

/-- The actual tetrad pointwise affine group embeds into the native quintet. -/
def naturalActorInclusion : TetradPointAffine naturalIndex →* Q where
  toFun x :=
    let s := naturalAffineEquiv (tetradPointAffineInclusion naturalIndex x)
    have hf : ∀ k, s.val.val (naturalPointCoordinates (naturalIndex,k)) =
        naturalPointCoordinates (naturalIndex,k) := by
      intro k
      rw [naturalAffineEquiv_points]
      rw [((sextetAffine_fixes_tetrad naturalIndex (tetradPointAffineInclusion naturalIndex x)).mpr
        ⟨x.right.val.property, x.left.toAdd.property, x.right.property⟩) k]
    ⟨⟨s.val, fixes_pair_mem _
      (by simpa only [naturalPointCoordinates_zero] using hf 0)
      (by simpa only [naturalPointCoordinates_nine] using hf 1)⟩, s.property⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (by simp)
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (by simp)

@[simp] theorem naturalActorInclusion_coe (x : TetradPointAffine naturalIndex) :
    (naturalActorInclusion x).val.val =
      (naturalAffineEquiv (tetradPointAffineInclusion naturalIndex x)).val := (rfl)

theorem naturalActorInclusion_injective : Function.Injective naturalActorInclusion := by
  intro x y h
  have hv : (naturalAffineEquiv (tetradPointAffineInclusion naturalIndex x)).val =
      (naturalAffineEquiv (tetradPointAffineInclusion naturalIndex y)).val :=
    by simpa only [naturalActorInclusion_coe] using congrArg (fun x : Q => x.val.val) h
  have h' := naturalAffineEquiv.injective (Subtype.ext hv)
  apply SemidirectProduct.ext
  · exact congrArg Multiplicative.ofAdd (Subtype.ext
      (congrArg (fun z : SextetAffineGroup => z.left.toAdd) h'))
  · exact Subtype.ext (Subtype.ext (congrArg SemidirectProduct.right h'))

theorem naturalActor_quotient (x : TetradPointAffine naturalIndex) :
    SextetCore.quotientHom
      (sourceStabilizerEquiv.symm
        (naturalAffineEquiv (tetradPointAffineInclusion naturalIndex x))) = x.right.val.val := by
  change sextetQuotient
    (SextetCore.sextetEquiv (sourceStabilizerEquiv.symm
      (sourceStabilizerEquiv (SextetCore.sextetEquiv.symm
        (sextetAffineEquiv (tetradPointAffineInclusion naturalIndex x)))))) = _
  rw [sourceStabilizerEquiv.symm_apply_apply, SextetCore.sextetEquiv.apply_symm_apply,
    sextetQuotient_affine]
  rfl

/-- Conjugation of native translations is the restricted hexacode action. -/
theorem naturalTranslation_conjugation (x : TetradPointAffine naturalIndex)
    (w : hexZeroCoordinate naturalIndex) :
    innerTranslationConjugation (naturalActorInclusion x)
      (Additive.ofMul (naturalTranslation (Multiplicative.ofAdd w))) =
    Additive.ofMul (naturalTranslation
      (Multiplicative.ofAdd (hexZeroLinear naturalIndex x.right.val w))) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [innerTranslationConjugation_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, naturalActorInclusion_coe,
    naturalTranslation_coe, Additive.toMul, Equiv.symm_apply_apply]
  have h := sourceTranslationEquiv_conjugation
    (naturalAffineEquiv (tetradPointAffineInclusion naturalIndex x)) w.val
  rw [naturalActor_quotient] at h
  exact h

@[simp] theorem innerTranslationCoordinates_symm_coe (w : hexZeroCoordinate naturalIndex) :
    innerTranslationCoordinates.symm w =
      Additive.ofMul (naturalTranslation (Multiplicative.ofAdd w)) := (rfl)

theorem innerTranslationCoordinates_equivariant (x : TetradPointAffine naturalIndex)
    (v : Additive innerTranslationGroup) :
    innerTranslationCoordinates (innerTranslationConjugation (naturalActorInclusion x) v) =
      hexZeroLinear naturalIndex x.right.val (innerTranslationCoordinates v) := by
  obtain ⟨w, rfl⟩ := innerTranslationCoordinates.symm.surjective v
  rw [innerTranslationCoordinates_symm_coe, naturalTranslation_conjugation,
    ← innerTranslationCoordinates_symm_coe, innerTranslationCoordinates.apply_symm_apply,
    ← innerTranslationCoordinates_symm_coe, innerTranslationCoordinates.apply_symm_apply]

/-- The full actual Q action is transitive on the fifteen nonzero translations. -/
theorem innerTranslationConjugation_transitive (u v : Additive innerTranslationGroup)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : Q, innerTranslationConjugation g u = v := by
  obtain ⟨g, hg⟩ := hexPointKernel_nonzero_transitive naturalIndex
    (innerTranslationCoordinates u) (innerTranslationCoordinates v)
    (fun h => hu (innerTranslationCoordinates.map_eq_zero_iff.mp h))
    (fun h => hv (innerTranslationCoordinates.map_eq_zero_iff.mp h))
  refine ⟨naturalActorInclusion (SemidirectProduct.inr g), ?_⟩
  apply innerTranslationCoordinates.injective
  rw [innerTranslationCoordinates_equivariant]
  exact hg

/-- Unconditional irreducibility of the native inner translation conjugation module. -/
theorem innerTranslationConjugation_isIrreducible :
    Representation.IsIrreducible innerTranslationConjugation := by
  have hn : Nontrivial (Additive innerTranslationGroup) := by
    by_contra! h
    have hc := Finite.card_le_one_iff_subsingleton.mpr h
    rw [Nat.card_congr (Additive.toMul : Additive innerTranslationGroup ≃ _),
      innerTranslationGroup_card] at hc
    omega
  let := hn
  apply IsSimpleOrder.of_forall_eq_top
  intro W hW
  have he : ∃ u, u ∈ W ∧ u ≠ 0 := by
    by_contra! h
    apply hW
    apply le_antisymm
    · intro u hu
      exact (Submodule.mem_bot (R := ZMod 2)).mpr (h u hu)
    · exact bot_le
  obtain ⟨u, hu, hun⟩ := he
  apply top_unique
  intro v _
  by_cases hv : v = 0
  · exact hv ▸ W.toSubmodule.zero_mem
  obtain ⟨g, rfl⟩ := innerTranslationConjugation_transitive u v hun hv
  exact W.apply_mem_toSubmodule g hu

/-- The pointwise source-tetrad stabilizer, viewed inside the actual native Q. -/
def naturalActor : Subgroup Q := naturalActorInclusion.range

def naturalActorEquiv : TetradPointAffine naturalIndex ≃* naturalActor :=
  MonoidHom.ofInjective naturalActorInclusion_injective

@[simp] theorem naturalActorEquiv_coe (x : TetradPointAffine naturalIndex) :
    (naturalActorEquiv x).val = naturalActorInclusion x := (rfl)

theorem naturalActorInclusion_fixed (x : TetradPointAffine naturalIndex) (k : Fin 4) :
    (naturalActorInclusion x).val.val.val (naturalPointCoordinates (naturalIndex,k)) =
      naturalPointCoordinates (naturalIndex,k) := by
  rw [naturalActorInclusion_coe, naturalAffineEquiv_points]
  rw [((sextetAffine_fixes_tetrad naturalIndex (tetradPointAffineInclusion naturalIndex x)).mpr
    ⟨x.right.val.property, x.left.toAdd.property, x.right.property⟩) k]

/-- This actor is precisely the subgroup fixing all four points of the source tetrad. -/
theorem mem_naturalActor_iff (g : Q) : g ∈ naturalActor ↔
    ∀ k : Fin 4, g.val.val.val (naturalPointCoordinates (naturalIndex,k)) =
      naturalPointCoordinates (naturalIndex,k) := by
  constructor
  · rintro ⟨x, rfl⟩ k
    exact naturalActorInclusion_fixed x k
  · intro hg
    let s : sextetStabilizer m22SourceSextet := ⟨g.val.val, g.property⟩
    obtain ⟨x, hx⟩ := naturalAffineEquiv.surjective s
    have hf : ∀ k, (sextetAffineEquiv x).val.val (naturalIndex,k) = (naturalIndex,k) := by
      intro k
      apply naturalPointCoordinates.injective
      rw [← naturalAffineEquiv_points, hx]
      exact hg k
    obtain ⟨hp, ht, hL⟩ := (sextetAffine_fixes_tetrad naturalIndex x).mp hf
    let y : TetradPointAffine naturalIndex :=
      ⟨Multiplicative.ofAdd ⟨x.left.toAdd, ht⟩, ⟨⟨x.right, hp⟩, hL⟩⟩
    have hy : tetradPointAffineInclusion naturalIndex y = x := by cases x; rfl
    refine ⟨y, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [naturalActorInclusion_coe, hy, hx]

/-- These four coordinate points are the literal source tetrad {0,2,9,14}. -/
theorem naturalActor_tetrad :
    Finset.univ.image (fun k : Fin 4 => naturalPointCoordinates (naturalIndex,k)) =
      m22SourceTetrad 0 := by decide +kernel

/-- The genuine local linear quotient map on the actual preimage in Q. -/
def naturalActorProjection : naturalActor →* hexPointKernel naturalIndex :=
  SemidirectProduct.rightHom.comp naturalActorEquiv.symm.toMonoidHom

theorem naturalActorProjection_surjective : Function.Surjective naturalActorProjection := by
  intro g
  refine ⟨naturalActorEquiv (SemidirectProduct.inr g), ?_⟩
  change (naturalActorEquiv.symm (naturalActorEquiv (SemidirectProduct.inr g))).right = g
  rw [naturalActorEquiv.symm_apply_apply]
  rfl

@[simp] theorem naturalActorProjection_equiv (x : TetradPointAffine naturalIndex) :
    naturalActorProjection (naturalActorEquiv x) = x.right := by
  change (naturalActorEquiv.symm (naturalActorEquiv x)).right = x.right
  rw [naturalActorEquiv.symm_apply_apply]

/-- The literal preimage of the inner translation group in this geometric actor. -/
def naturalActorTranslations : Subgroup naturalActor :=
  innerTranslationGroup.comap (Q.subtype.comp naturalActor.subtype)

@[simp] theorem naturalActorInclusion_inl (w : Multiplicative (hexZeroCoordinate naturalIndex)) :
    (naturalActorInclusion (SemidirectProduct.inl w)).val = (naturalTranslation w).val := (rfl)

theorem naturalActorProjection_kernel : naturalActorProjection.ker = naturalActorTranslations := by
  ext a
  obtain ⟨x, rfl⟩ := naturalActorEquiv.surjective a
  change naturalActorProjection (naturalActorEquiv x) = 1 ↔
    (naturalActorEquiv x).val.val ∈ innerTranslationGroup
  rw [naturalActorProjection_equiv, naturalActorEquiv_coe]
  constructor
  · intro hx
    have he : x = SemidirectProduct.inl x.left := by
      rw [← SemidirectProduct.inl_left_mul_inr_right x, hx, map_one, mul_one]
      rfl
    rw [he, naturalActorInclusion_inl]
    exact (naturalTranslation x.left).property
  · intro hx
    have hs : (naturalAffineEquiv (tetradPointAffineInclusion naturalIndex x)).val ∈ sourceCore := hx.1
    obtain ⟨w, hw⟩ := sourceTranslationEquiv.surjective
      ⟨(naturalAffineEquiv (tetradPointAffineInclusion naturalIndex x)).val, hs⟩
    have he : naturalAffineEquiv (SemidirectProduct.inl w) =
        naturalAffineEquiv (tetradPointAffineInclusion naturalIndex x) := by
      apply Subtype.ext
      rw [naturalAffineEquiv_translation, hw]
    have hr := congrArg SemidirectProduct.right (naturalAffineEquiv.injective he)
    apply Subtype.ext
    apply Subtype.ext
    exact hr.symm

instance naturalActorTranslations_normal : naturalActorTranslations.Normal :=
  naturalActorProjection_kernel ▸ inferInstance

/-- The quotient by the literal native translations is the local hexacode kernel. -/
def naturalActorQuotientEquiv :
    (naturalActor ⧸ naturalActorTranslations) ≃* hexPointKernel naturalIndex :=
  (QuotientGroup.quotientMulEquivOfEq naturalActorProjection_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective naturalActorProjection
      naturalActorProjection_surjective)

@[simp] theorem naturalActorQuotientEquiv_mk (a : naturalActor) :
    naturalActorQuotientEquiv (QuotientGroup.mk a) = naturalActorProjection a := (rfl)

theorem innerTranslationCoordinates_actor (a : naturalActor) (v : Additive innerTranslationGroup) :
    innerTranslationCoordinates (innerTranslationConjugation a.val v) =
      hexZeroLinear naturalIndex (naturalActorProjection a).val (innerTranslationCoordinates v) := by
  obtain ⟨x, rfl⟩ := naturalActorEquiv.surjective a
  rw [naturalActorEquiv_coe, naturalActorProjection_equiv]
  exact innerTranslationCoordinates_equivariant x v

end Sporadic.Mathieu.M22ChapterH.Quintet
