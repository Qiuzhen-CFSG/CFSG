module
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic.GroupRecognition
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic.ActionComparison
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension
public import Theory.Frattini.OmegaProducts

/-!
# Recognition of the actual quartic hexad extension

For a finite covering group with the specified M₂₂ central quotient and cyclic
center of order four, construct a complement to the actual hexad radical and
recognize its conjugation action as the intrinsic signed six-letter A₆ action.
The only earlier-source inputs are perfectness of the hexad preimage (restriction
(i)) and the A₆ two-primary covering identification. Splitting, group recognition
and action comparison are proved prerequisites, not additional inputs.

The proof first constructs marked Frattini coordinates using the binary cover,
then recognizes the resulting central extension and corrects the coordinates
by action rigidity. The original central generator can map to either volume or
inverse volume; its square always maps to the specified sign involution. The
literal central quotient and native six-point marking are retained throughout.

Transporting the two intrinsic quaternion factors proves the central-product
presentation C₄ * Q₈ * Q₈ inside the original radical: the factors commute,
their intersection and the overlap with the actual ambient center are precisely
Frattini, and together they generate the radical. The constructed isomorphism
of whole split extensions retains both subgroup embeddings and quotient maps.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, I.2.2(6),
printed pp.410 and 412 / PDF pp.421 and 423. The parent M₂₂ local-cover assembly
retains the arbitrary S₅/E₁₆ restriction and discharge of the earlier inputs.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
universe u
variable {K : Type u} [Group K]
noncomputable section

/-- Recognized coordinates on the actual quartic hexad extension. -/
structure HexadRecognition (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) extends FrattiniCoordinates e hB where
  radicalEquiv : hexadRadical e B ≃* EvenCliffordSix.Model
  core_projection : ∀ r, EvenCliffordSix.projection (radicalEquiv r) = coreMap r
  action_equivariant : ∀ a r,
    radicalEquiv (hexadConjugation e B (sectionHom a) r) =
      EvenCliffordSix.action a (radicalEquiv r)
  centralGenerator : center K
  central_order : orderOf centralGenerator = 4
  central_image :
    radicalEquiv ⟨centralGenerator.val, center_le_hexadRadical e B centralGenerator.property⟩ =
        EvenCliffordSix.volume ∨
      radicalEquiv ⟨centralGenerator.val, center_le_hexadRadical e B centralGenerator.property⟩ =
        EvenCliffordSix.volume⁻¹
  central_square :
    radicalEquiv ((⟨centralGenerator.val,
      center_le_hexadRadical e B centralGenerator.property⟩ : hexadRadical e B) ^ 2) =
        EvenCliffordSix.involution

/-- Construct all recognition data, with only the earlier source inputs remaining. -/
theorem exists_hexadRecognition [Finite K] [IsCyclic (center K)]
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    [Group.IsPerfect (hexadPreimage e B)]
    (hcover : CentralExtension.TwoPrimaryInvolutionData.{u} (alternatingGroup (Fin 6))) :
    Nonempty (HexadRecognition e hB) := by
  obtain ⟨d⟩ := exists_frattiniCoordinates e hZ hB hcover
  obtain ⟨c, hc, E, hp, hv, hs, _⟩ := d.exists_markedModelEquiv hZ
  obtain ⟨F, hFp, hFa, hFsign, _, hFv, _⟩ := d.exists_equivariant_equiv E hp
  have hv' : E.symm EvenCliffordSix.volume =
      (⟨c.val, center_le_hexadRadical e B c.property⟩ : hexadRadical e B) :=
    E.symm_apply_eq.mpr hv.symm
  refine ⟨{
    toFrattiniCoordinates := d
    radicalEquiv := F
    core_projection := hFp
    action_equivariant := hFa
    centralGenerator := c
    central_order := hc
    central_image := hv' ▸ hFv
    central_square := ?_ }⟩
  rw [hFsign _ ?_, hs]
  rw [radical_frattini e hZ hB]
  exact mem_centralSquares.mpr ⟨c, rfl⟩

namespace HexadRecognition
variable {e : (K ⧸ center K) ≃* M22} {B : Finset (Fin 22)} {hB : B ∈ m22Blocks}
variable (d : HexadRecognition e hB)
include d

/-- The actual complement inside the ambient covering group. -/
def complement : Subgroup K := d.sectionHom.range.map (hexadPreimage e B).subtype

noncomputable def complementEquiv : alternatingGroup (Fin 6) ≃* d.complement :=
  d.toFrattiniCoordinates.complementEquiv.trans (d.sectionHom.range.equivMapOfInjective
    (hexadPreimage e B).subtype Subtype.val_injective)

theorem isComplement :
    ((hexadRadical e B).subgroupOf (hexadPreimage e B)).IsComplement' d.sectionHom.range :=
  d.toFrattiniCoordinates.isComplement

theorem eq_commutator : hexadRadical e B = ⁅hexadRadical e B, d.complement⁆ :=
  d.toFrattiniCoordinates.eq_commutator

/-- The literal quotient by the ambient center retains its native coordinates. -/
theorem radical_natural_projection (r : hexadRadical e B) :
    EvenCliffordSix.naturalProjection (d.radicalEquiv r) = Binary.naturalMap e hB r := by
  apply Multiplicative.toAdd.injective
  change BinaryPermutation.coreToNatural (Fin 6)
    (EvenCliffordSix.projection (d.radicalEquiv r)).toAdd = _
  rw [d.core_projection, d.toFrattiniCoordinates.natural_projection]

/-- The native pointwise-kernel projection is recovered without changing quotient maps. -/
theorem kernel_projection (r : hexadRadical e B) :
    Binary.kernelProjection e B r = (m22HexadNaturalCoordinates hB).symm
      (EvenCliffordSix.naturalProjection (d.radicalEquiv r)) := by
  apply (m22HexadNaturalCoordinates hB).injective
  rw [MulEquiv.apply_symm_apply]
  exact (d.radical_natural_projection r).symm

/-- The original central quotient of K agrees literally with the model coordinates. -/
theorem ambient_projection (r : hexadRadical e B) :
    projection e r.val = ((m22HexadNaturalCoordinates hB).symm
      (EvenCliffordSix.naturalProjection (d.radicalEquiv r))).val.val := by
  change (Binary.kernelProjection e B r).val.val = _
  rw [d.kernel_projection]

/-- The full intrinsic center is precisely the image of the original center. -/
theorem center_iff (r : hexadRadical e B) :
    r.val ∈ center K ↔ d.radicalEquiv r ∈ center EvenCliffordSix.Model := by
  rw [← EvenCliffordSix.Structure.naturalProjection_ker_eq_center]
  change r ∈ (center K).subgroupOf (hexadRadical e B) ↔
    EvenCliffordSix.naturalProjection (d.radicalEquiv r) = 1
  rw [d.radical_natural_projection, ← Binary.naturalMap_ker]
  rfl

/-- Both Frattini subgroups are identified over the literal augmentation projection. -/
theorem frattini_map :
    (frattini (hexadRadical e B)).map d.radicalEquiv.toMonoidHom = EvenCliffordSix.signKernel :=
  (frattini_map_equiv d.radicalEquiv).trans EvenCliffordSix.frattini_eq_signKernel

/-- Center transport is with the ambient embedding, not an abstract cyclic subgroup. -/
theorem center_map :
    ((center K).subgroupOf (hexadRadical e B)).map d.radicalEquiv.toMonoidHom =
      EvenCliffordSix.Structure.cyclicFactor := by
  rw [← EvenCliffordSix.Structure.center_eq_cyclicFactor]
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (d.center_iff r).mp hr
  · intro hx
    exact ⟨d.radicalEquiv.symm x,
      (d.center_iff _).mpr (by simpa using hx), d.radicalEquiv.apply_symm_apply x⟩

/-- The same complement parametrized by the original six-point labels. -/
def nativeSection : alternatingGroup (Fin 6) →* hexadPreimage e B :=
  d.sectionHom.comp (m22HexadMarking hB).symm.toMonoidHom

@[simp] theorem nativeSection_six (a : alternatingGroup (Fin 6)) :
    hexadSixMap e hB (d.nativeSection a) = a := by
  change hexadSixMap e hB (d.sectionHom ((m22HexadMarking hB).symm a)) = a
  rw [d.section_marking, MulEquiv.apply_symm_apply]

/-- With native labels the model action retains exactly the comparison automorphism. -/
theorem nativeSection_equivariant (a : alternatingGroup (Fin 6)) (r : hexadRadical e B) :
    d.radicalEquiv (hexadConjugation e B (d.nativeSection a) r) =
      EvenCliffordSix.precomposedAction (m22HexadMarking hB).symm a (d.radicalEquiv r) :=
  d.action_equivariant ((m22HexadMarking hB).symm a) r

/-- The original extension is isomorphic to the intrinsic signed semidirect product. -/
noncomputable def modelToHexad : EvenCliffordSix.SplitExtension ≃* hexadPreimage e B :=
  (SemidirectProduct.congr d.radicalEquiv.symm (MulEquiv.refl _) (fun a => by
    apply MulEquiv.ext
    intro r
    apply d.radicalEquiv.injective
    change d.radicalEquiv (d.radicalEquiv.symm (EvenCliffordSix.action a r)) =
      d.radicalEquiv (hexadConjugation e B (d.sectionHom a) (d.radicalEquiv.symm r))
    rw [d.action_equivariant]
    simp only [MulEquiv.apply_symm_apply])).trans
      (MulEquiv.ofBijective (hexadSplitHom e B d.sectionHom)
        (hexadSplitHom_bijective e hB (m22HexadMarking hB) d.sectionHom d.section_marking))

@[simp] theorem modelToHexad_coe (x : EvenCliffordSix.SplitExtension) :
    (d.modelToHexad x : K) =
      (d.radicalEquiv.symm x.left : K) * (d.sectionHom x.right : K) := rfl

@[simp] theorem modelToHexad_inl (r : EvenCliffordSix.Model) :
    d.modelToHexad (SemidirectProduct.inl r) =
      Subgroup.inclusion (hexadRadical_le e B) (d.radicalEquiv.symm r) := by
  apply Subtype.ext
  rw [d.modelToHexad_coe]
  simp

@[simp] theorem modelToHexad_inr (a : alternatingGroup (Fin 6)) :
    d.modelToHexad (SemidirectProduct.inr a) = d.sectionHom a := by
  apply Subtype.ext
  rw [d.modelToHexad_coe]
  simp

theorem modelToHexad_six (x : EvenCliffordSix.SplitExtension) :
    hexadSixMap e hB (d.modelToHexad x) = m22HexadMarking hB x.right := by
  change hexadSixMap e hB
    (Subgroup.inclusion (hexadRadical_le e B) (d.radicalEquiv.symm x.left) *
      d.sectionHom x.right) = _
  rw [map_mul, d.section_marking]
  have hn : hexadSixMap e hB (Subgroup.inclusion (hexadRadical_le e B)
      (d.radicalEquiv.symm x.left)) = 1 := by
    apply (hexadSixMap_ker e hB).ge
    exact (d.radicalEquiv.symm x.left).property
  rw [hn, one_mul]

/-- The two quaternion factors are actual subgroups of the original radical. -/
def quaternionFactor (side : Bool) : Subgroup (hexadRadical e B) :=
  (EvenCliffordSix.Structure.quaternionFactor side).map d.radicalEquiv.symm.toMonoidHom

/-- The coordinate maps identify each embedded factor with Q₈. -/
noncomputable def quaternionFactorEquiv (side : Bool) :
    d.quaternionFactor side ≃* QuaternionGroup 2 :=
  (d.radicalEquiv.symm.subgroupMap _).symm.trans
    (EvenCliffordSix.Structure.quaternionEquiv side)

/-- The common involution is the actual Frattini subgroup. -/
theorem sign_map_symm :
    EvenCliffordSix.signKernel.map d.radicalEquiv.symm.toMonoidHom =
      frattini (hexadRadical e B) := by
  rw [← EvenCliffordSix.frattini_eq_signKernel, frattini_map_equiv]

/-- The model cyclic factor corresponds to precisely the embedded ambient center. -/
theorem cyclic_map_symm :
    EvenCliffordSix.Structure.cyclicFactor.map d.radicalEquiv.symm.toMonoidHom =
      (center K).subgroupOf (hexadRadical e B) := by
  rw [Subgroup.map_equiv_eq_comap_symm' (f := d.radicalEquiv.symm)]
  ext r
  change d.radicalEquiv r ∈ EvenCliffordSix.Structure.cyclicFactor ↔ r.val ∈ center K
  rw [← EvenCliffordSix.Structure.center_eq_cyclicFactor]
  exact (d.center_iff r).symm

/-- Intersection of the two quaternion factors is the original Frattini subgroup. -/
theorem quaternion_intersection :
    d.quaternionFactor false ⊓ d.quaternionFactor true = frattini (hexadRadical e B) := by
  rw [quaternionFactor, quaternionFactor, ← Subgroup.map_inf _ _ _ d.radicalEquiv.symm.injective,
    EvenCliffordSix.Structure.factor_intersection, d.sign_map_symm]

/-- These embedded factors commute elementwise. -/
theorem quaternion_commute (x : hexadRadical e B) (hx : x ∈ d.quaternionFactor false)
    (y : hexadRadical e B) (hy : y ∈ d.quaternionFactor true) : x * y = y * x := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [← map_mul, ← map_mul, EvenCliffordSix.Structure.factors_commute a ha b hb]

/-- The two quaternion factors together with the original center generate R. -/
theorem centralProduct_generate :
    (center K).subgroupOf (hexadRadical e B) ⊔
      (d.quaternionFactor false ⊔ d.quaternionFactor true) = ⊤ := by
  rw [← d.cyclic_map_symm, quaternionFactor, quaternionFactor,
    ← Subgroup.map_sup, ← Subgroup.map_sup]
  change (EvenCliffordSix.Structure.cyclicFactor ⊔
    EvenCliffordSix.Structure.quaternionJoin).map d.radicalEquiv.symm.toMonoidHom = ⊤
  rw [EvenCliffordSix.Structure.factors_generate,
    Subgroup.map_top_of_surjective _ d.radicalEquiv.symm.surjective]

/-- The overlap of the cyclic-four factor and Q₈*Q₈ is the same central involution. -/
theorem centralProduct_intersection :
    (center K).subgroupOf (hexadRadical e B) ⊓
      (d.quaternionFactor false ⊔ d.quaternionFactor true) = frattini (hexadRadical e B) := by
  rw [← d.cyclic_map_symm, quaternionFactor, quaternionFactor, ← Subgroup.map_sup,
    ← Subgroup.map_inf _ _ _ d.radicalEquiv.symm.injective]
  change (EvenCliffordSix.Structure.cyclicFactor ⊓
    EvenCliffordSix.Structure.quaternionJoin).map d.radicalEquiv.symm.toMonoidHom = _
  rw [EvenCliffordSix.Structure.cyclicFactor_intersection, d.sign_map_symm]

/-- The full center of the radical is the actual embedded ambient center. -/
theorem center_eq_ambient :
    center (hexadRadical e B) = (center K).subgroupOf (hexadRadical e B) := by
  rw [← d.cyclic_map_symm, ← EvenCliffordSix.Structure.center_eq_cyclicFactor,
    Subgroup.center_map_equiv]

/-- The shared involution remains the square of the specified ambient generator. -/
theorem frattini_eq_zpowers : frattini (hexadRadical e B) =
    zpowers ((⟨d.centralGenerator.val,
      center_le_hexadRadical e B d.centralGenerator.property⟩ : hexadRadical e B) ^ 2) := by
  rw [← d.sign_map_symm, EvenCliffordSix.signKernel_eq_zpowers, MonoidHom.map_zpowers]
  congr 1
  exact d.radicalEquiv.symm_apply_eq.mpr d.central_square.symm

/-- This identifies the cyclic factor as an actual C₄ inside R. -/
noncomputable def cyclicFactorEquiv :
    (center K).subgroupOf (hexadRadical e B) ≃* Multiplicative (ZMod 4) :=
  (MulEquiv.subgroupCongr d.cyclic_map_symm.symm).trans
    ((d.radicalEquiv.symm.subgroupMap _).symm.trans EvenCliffordSix.Structure.cyclicFourEquiv)

/-- Mapping the intrinsic radical center back into K gives exactly Z(K). -/
theorem center_ambient_map :
    (center (hexadRadical e B)).map (hexadRadical e B).subtype = center K := by
  rw [d.center_eq_ambient, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (center_le_hexadRadical e B)]

/-- The square of the marked central generator belongs to both quaternion factors. -/
theorem central_square_mem_factors (side : Bool) :
    (⟨d.centralGenerator.val, center_le_hexadRadical e B d.centralGenerator.property⟩ :
      hexadRadical e B) ^ 2 ∈ d.quaternionFactor side := by
  refine ⟨EvenCliffordSix.involution, EvenCliffordSix.Structure.involution_mem_factor side, ?_⟩
  exact d.radicalEquiv.symm_apply_eq.mpr d.central_square.symm

/-- The common subgroup has order two, whereas the full center has order four. -/
theorem quaternion_intersection_card :
    Nat.card (d.quaternionFactor false ⊓ d.quaternionFactor true :
      Subgroup (hexadRadical e B)) = 2 := by
  rw [d.quaternion_intersection,
    Nat.card_congr (d.radicalEquiv.subgroupMap (frattini (hexadRadical e B))).toEquiv]
  change Nat.card ((frattini (hexadRadical e B)).map d.radicalEquiv.toMonoidHom) = 2
  rw [d.frattini_map, EvenCliffordSix.signKernel_card]

/-- The model split coordinates retain exactly the embedded original center. -/
theorem modelToHexad_mem_center (x : EvenCliffordSix.SplitExtension) :
    (d.modelToHexad x : K) ∈ center K ↔ x ∈ EvenCliffordSix.SplitExtension.central := by
  constructor
  · intro hx
    have hn : hexadSixMap e hB (d.modelToHexad x) = 1 := by
      apply (hexadSixMap_ker e hB).ge
      exact center_le_hexadRadical e B hx
    rw [d.modelToHexad_six, map_eq_one_iff _ (m22HexadMarking hB).injective] at hn
    rw [d.modelToHexad_coe, hn, map_one] at hx
    simp only [OneMemClass.coe_one, mul_one] at hx
    refine ⟨x.left, ?_, ?_⟩
    · change x.left ∈ center EvenCliffordSix.Model
      simpa only [MulEquiv.apply_symm_apply] using (d.center_iff _).mp hx
    · apply SemidirectProduct.ext <;> simp [hn, EvenCliffordSix.SplitExtension.radicalEmbedding]
  · rintro ⟨z, hz, rfl⟩
    change z ∈ center EvenCliffordSix.Model at hz
    rw [d.modelToHexad_inl]
    exact (d.center_iff _).mpr (by simpa only [MulEquiv.apply_symm_apply] using hz)

end HexadRecognition
end
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
