module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Orthogonal
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.BinaryMaps

/-!
# The native octad action in split orthogonal coordinates

Reindexing the even octad words intertwines the native action with the deleted
eight-point action. Transport through the explicit split isometry gives its
literal orthogonal image: the image of A8 under the faithful deleted action.
Its kernel is the intrinsic two-core, so the quotient acts faithfully on the
supported quadratic space. Pullback of invariant subspaces to the natural
binary permutation section proves irreducibility.

This module does not identify the alternating image with the Siegel-generated
Omega subgroup; that is a separate finite orthogonal-group comparison.

Source: Aschbacher--Smith, H.15.2(2), printed pp.398--399. The deleted-module
isometry and faithful permutation action are the licensed ATLAS constructions
imported above, with attribution retained in their owning modules.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.CocodeOctad

/-- The native octad permutations written on eight numbered coordinates. -/
def coordinateActionEight (O : Octad) : octadStabilizer O →* Equiv.Perm (Fin 8) :=
  (indexEquiv O).permCongrHom.toMonoidHom.comp (coordinateAction O)

lemma coordinateActionEight_range (O : Octad) :
    (coordinateActionEight O).range = alternatingGroup (Fin 8) := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    apply Equiv.Perm.mem_alternatingGroup.mpr
    change Equiv.Perm.sign ((indexEquiv O).permCongr (coordinateAction O g)) = 1
    rw [Equiv.Perm.sign_permCongr]
    apply Equiv.Perm.mem_alternatingGroup.mp
    rw [← coordinateAction_range]
    exact ⟨g, rfl⟩
  · intro hp
    let q := (indexEquiv O).symm.permCongr p
    have hq : q ∈ alternatingGroup O.val := by
      apply Equiv.Perm.mem_alternatingGroup.mpr
      rw [Equiv.Perm.sign_permCongr]
      exact Equiv.Perm.mem_alternatingGroup.mp hp
    rw [← coordinateAction_range] at hq
    obtain ⟨g, hg⟩ := hq
    refine ⟨g, ?_⟩
    change (indexEquiv O).permCongr (coordinateAction O g) = p
    rw [hg]
    exact (indexEquiv O).permCongr.apply_symm_apply p

lemma coordinateActionEight_ker (O : Octad) :
    (coordinateActionEight O).ker = pCore 2 (octadStabilizer O) := by
  rw [core_eq_coordinateKernel]
  ext g
  change (indexEquiv O).permCongrHom (coordinateAction O g) = 1 ↔ coordinateAction O g = 1
  exact (indexEquiv O).permCongrHom.map_eq_one_iff

def toSupportedSpace (O : Octad) : BinaryPermutation.core O.val →ₗ[Bit]
    supportedPairSpace O.val :=
  (toCocode O.val).codRestrict _ (by
    let : Nonempty O.val := Fintype.card_pos_iff.mp (by
      rw [Fintype.card_coe, m24Blocks_card _ O.property]; decide)
    intro v
    rw [← range_toCocode]
    exact LinearMap.mem_range_self _ _)

lemma toSupportedSpace_surjective (O : Octad) : Function.Surjective (toSupportedSpace O) := by
  let : Nonempty O.val := Fintype.card_pos_iff.mp (by
    rw [Fintype.card_coe, m24Blocks_card _ O.property]; decide)
  intro v
  obtain ⟨w, hw⟩ := (show v.val ∈ (toCocode O.val).range by
    rw [range_toCocode]; exact v.property)
  exact ⟨w, Subtype.ext hw⟩

lemma toSupportedSpace_equivariant (O : Octad) (g : octadStabilizer O)
    (v : BinaryPermutation.core O.val) :
    toSupportedSpace O (BinaryPermutation.coreRepresentation O.val (coordinateAction O g) v) =
      pairRepresentation O g (toSupportedSpace O v) :=
  Subtype.ext (toCocode_equivariant O g v)

lemma spaceToW_equivariant (O : Octad) (g : octadStabilizer O)
    (v : supportedPairSpace O.val) :
    spaceToW O (pairRepresentation O g v) =
      Atlas.Order20160A8.DeletedEight.quotientPerm (coordinateActionEight O g) (spaceToW O v) := by
  obtain ⟨w, rfl⟩ := toSupportedSpace_surjective O v
  rw [← toSupportedSpace_equivariant]
  change spaceToW O ⟨toCocode O.val _, _⟩ =
    Atlas.Order20160A8.DeletedEight.quotientPerm _ (spaceToW O ⟨toCocode O.val w, _⟩)
  rw [spaceToW_apply_core, spaceToW_apply_core]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  funext i
  change w.val ((coordinateAction O g).symm ((indexEquiv O).symm i)) =
    w.val ((indexEquiv O).symm ((indexEquiv O)
      ((coordinateAction O g).symm ((indexEquiv O).symm i))))
  rw [Equiv.symm_apply_apply]

/-- The actual action, in standard split orthogonal coordinates. -/
def splitAction (O : Octad) : octadStabilizer O →*
    Atlas.Order20160A8.O_DPlus 3 Bit :=
  Atlas.Order20160A8.DeletedEight.orthogonalHom.comp (coordinateActionEight O)

lemma spaceToW_formEquiv (O : Octad) (x : ClassicalOrthogonal.VectorD 3 Bit) :
    spaceToW O (formEquiv O x) = Atlas.Order20160A8.DeletedEight.splitIsometry x :=
  (spaceToW O).apply_symm_apply _

private lemma splitIsometry_action (p : Equiv.Perm (Fin 8))
    (x : ClassicalOrthogonal.VectorD 3 Bit) :
    Atlas.Order20160A8.DeletedEight.splitIsometry
      ((Atlas.Order20160A8.DeletedEight.orthogonalHom p).val x) =
    Atlas.Order20160A8.DeletedEight.quotientPerm p
      (Atlas.Order20160A8.DeletedEight.splitIsometry x) :=
  Atlas.Order20160A8.DeletedEight.splitIsometry.apply_symm_apply _

/-- The chosen isometry intertwines the native action with its explicit
orthogonal action. -/
lemma formEquiv_equivariant (O : Octad) (g : octadStabilizer O)
    (x : ClassicalOrthogonal.VectorD 3 Bit) :
    formEquiv O ((splitAction O g).val x) = pairRepresentation O g (formEquiv O x) := by
  apply (spaceToW O).injective
  rw [spaceToW_equivariant, spaceToW_formEquiv, spaceToW_formEquiv]
  exact splitIsometry_action _ _

lemma quadratic_invariant (O : Octad) (g : octadStabilizer O)
    (v : supportedPairSpace O.val) : quadratic O (pairRepresentation O g v) = quadratic O v := by
  change Atlas.Order20160A8.DeletedEight.quotientQuadratic
      (spaceToW O (pairRepresentation O g v)) =
    Atlas.Order20160A8.DeletedEight.quotientQuadratic (spaceToW O v)
  rw [spaceToW_equivariant]
  exact (Atlas.Order20160A8.DeletedEight.permutationIsometry _).map_app _

/-- The action kernel is the intrinsic two-core of the octad stabilizer. -/
lemma splitAction_ker (O : Octad) :
    (splitAction O).ker = pCore 2 (octadStabilizer O) := by
  rw [← coordinateActionEight_ker]
  ext g
  change Atlas.Order20160A8.DeletedEight.orthogonalHom (coordinateActionEight O g) = 1 ↔ _
  rw [← Atlas.Order20160A8.DeletedEight.orthogonalHom.map_one]
  exact Atlas.Order20160A8.DeletedEight.orthogonalHom_injective.eq_iff

/-- The native action has the full alternating deleted-module image. -/
lemma splitAction_range (O : Octad) :
    (splitAction O).range = (alternatingGroup (Fin 8)).map
      Atlas.Order20160A8.DeletedEight.orthogonalHom := by
  rw [splitAction, MonoidHom.range_comp, coordinateActionEight_range]

/-- The actual quotient acts faithfully as this orthogonal subgroup. -/
def quotientEquivSplitImage (O : Octad) :
    (octadStabilizer O ⧸ pCore 2 (octadStabilizer O)) ≃* (splitAction O).range :=
  (QuotientGroup.quotientMulEquivOfEq (splitAction_ker O).symm).trans
    (QuotientGroup.quotientKerEquivRange (splitAction O))

lemma quotientEquivSplitImage_mk (O : Octad) (g : octadStabilizer O) :
    (quotientEquivSplitImage O (QuotientGroup.mk g)).val = splitAction O g := rfl

/-- The intrinsic quotient identified with its eight-coordinate alternating group. -/
def quotientEquivAltEight (O : Octad) :
    (octadStabilizer O ⧸ pCore 2 (octadStabilizer O)) ≃* alternatingGroup (Fin 8) :=
  (QuotientGroup.quotientMulEquivOfEq (coordinateActionEight_ker O).symm).trans
    ((QuotientGroup.quotientKerEquivRange (coordinateActionEight O)).trans
      (MulEquiv.subgroupCongr (coordinateActionEight_range O)))

lemma quotientEquivAltEight_mk (O : Octad) (g : octadStabilizer O) :
    (quotientEquivAltEight O (QuotientGroup.mk g)).val = coordinateActionEight O g := rfl

/-- The quotient's faithful action in standard split coordinates. -/
def quotientSplitAction (O : Octad) :
    (octadStabilizer O ⧸ pCore 2 (octadStabilizer O)) →* Atlas.Order20160A8.O_DPlus 3 Bit :=
  (splitAction O).range.subtype.comp (quotientEquivSplitImage O).toMonoidHom

lemma quotientSplitAction_mk (O : Octad) (g : octadStabilizer O) :
    quotientSplitAction O (QuotientGroup.mk g) = splitAction O g := rfl

/-- The quotient's faithful action on the literal supported quadratic space. -/
def quotientIsometryAction (O : Octad) :
    (octadStabilizer O ⧸ pCore 2 (octadStabilizer O)) →*
      Atlas.Order20160A8.isometrySubgroup (quadratic O) :=
  (Atlas.Order20160A8.isometryGroupTransport (formEquiv O)).toMonoidHom.comp
    (quotientSplitAction O)

lemma quotientIsometryAction_injective (O : Octad) :
    Function.Injective (quotientIsometryAction O) := by
  intro a b hab
  apply (quotientEquivSplitImage O).injective
  apply Subtype.ext
  apply (Atlas.Order20160A8.isometryGroupTransport (formEquiv O)).injective
  exact hab

private lemma transport_apply {F V₁ V₂ : Type} [Field F]
    [AddCommGroup V₁] [AddCommGroup V₂] [Module F V₁] [Module F V₂]
    {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (e : Q₁.IsometryEquiv Q₂) (g : Atlas.Order20160A8.isometrySubgroup Q₁) (v : V₂) :
    (Atlas.Order20160A8.isometryGroupTransport e g).val v = e (g.val (e.symm v)) := rfl

lemma quotientIsometryAction_mk (O : Octad) (g : octadStabilizer O)
    (v : supportedPairSpace O.val) :
    (quotientIsometryAction O (QuotientGroup.mk g)).val v = pairRepresentation O g v := by
  simp only [quotientIsometryAction, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, quotientSplitAction_mk]
  rw [transport_apply, formEquiv_equivariant,
    QuadraticMap.IsometryEquiv.apply_symm_apply]

lemma pairRepresentation_isIrreducible (O : Octad) :
    Representation.IsIrreducible (pairRepresentation O) := by
  have hn : 5 ≤ Fintype.card O.val := by
    rw [Fintype.card_coe, m24Blocks_card _ O.property]; decide
  let := BinaryPermutation.alternatingNatural_isIrreducible (Ω := O.val) hn
  let E := naturalEquiv O
  have : Nontrivial (supportedPairSpace O.val) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_supportedPairSpace]; decide)
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro S
  let T : Subrepresentation (BinaryPermutation.alternatingNaturalRepresentation (Ω := O.val)) :=
    ⟨S.toSubmodule.comap E.toLinearMap, by
      intro d w hw
      have hd : d.val ∈ (coordinateAction O).range := by
        rw [coordinateAction_range]; exact d.property
      obtain ⟨g, hg⟩ := hd
      change E (BinaryPermutation.naturalRepresentation O.val d.val w) ∈ S
      rw [← hg, naturalEquiv_equivariant]
      exact S.apply_mem_toSubmodule g hw⟩
  rcases eq_bot_or_eq_top T with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.comap_injective_of_surjective E.surjective
    change T.toSubmodule = Submodule.comap E.toLinearMap ⊥
    rw [hb]
    ext w
    change w = 0 ↔ E w = 0
    exact E.map_eq_zero_iff.symm
  · right
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.comap_injective_of_surjective E.surjective
    change T.toSubmodule = Submodule.comap E.toLinearMap ⊤
    rw [ht]
    rfl

end MathieuCode.CocodeOctad
