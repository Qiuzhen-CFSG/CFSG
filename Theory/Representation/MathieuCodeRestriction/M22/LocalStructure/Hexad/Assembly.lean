module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag
public import Mathlib.Algebra.Module.ZMod

/-!
# Assembling the hexad cocode actions and code chief flag

The six literal hexad coordinates are numbered to connect the proved deleted
module to the chief-flag interface. The explicit cocode shear formula gives
the full axis radical. Its parameter isomorphism then identifies the axis
with the actual kernel conjugation module marked by the earlier H.14 input.
This constructs every intermediate cocode witness needed by the code duality
and cubic fixed-quotient arguments; none of those M22 action conclusions is
assumed.

The two permutation markings are kept distinct: one comes from the literal
six coordinates, the other from the earlier kernel conjugation model. The
remaining scalar and transvection premises concern M24 or the H.14 kernel
restriction. The geometric clause also retains the two earlier quintet fixed
dimensions, which the quintet source-theorem owner must supply.

The native inner A6 and outer S6 cocode identifications, including their
orthogonal dual descriptions and literal W/U actions, are re-exported through
`CocodeAction`. Normality throughout is relative to the hexad stabilizer.

Source: Aschbacher--Smith, H.15.2(2)--(6) and H.16.4, printed pp.398--399,403,
combined manuscript of 1 March 2004.
-/

public section
noncomputable section
open MathieuCode MathieuCode.Hexad Representation
namespace MathieuCode.Hexad.Assembly
open ChiefFlag ChiefFlag.Actions
open CocodeAction.SixPointModel

private def relabelFull {I J : Type*} (e : I ≃ J) :
    (I → ZMod 2) ≃ₗ[ZMod 2] (J → ZMod 2) :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm

private theorem relabel_constants {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J) :
    (BinaryPermutation.constants I).map (relabelFull e).toLinearMap =
      BinaryPermutation.constants J := by
  rw [BinaryPermutation.constants, Submodule.map_span, Set.image_singleton]
  rfl

private def relabelDeleted {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J) :
    BinaryPermutation.Deleted I ≃ₗ[ZMod 2] BinaryPermutation.Deleted J :=
  Submodule.Quotient.equiv _ _ (relabelFull e) (relabel_constants e)

private theorem relabelDeleted_equivariant {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (g : Equiv.Perm I) (v : BinaryPermutation.Deleted I) :
    relabelDeleted e (BinaryPermutation.deletedRepresentation I g v) =
      BinaryPermutation.deletedRepresentation J (e.permCongrHom g) (relabelDeleted e v) := by
  obtain ⟨w, rfl⟩ := (BinaryPermutation.constants I).mkQ_surjective v
  change (BinaryPermutation.constants J).mkQ
    (relabelFull e (BinaryPermutation.representation I g w)) =
      (BinaryPermutation.constants J).mkQ
        (BinaryPermutation.representation J (e.permCongrHom g) (relabelFull e w))
  congr 1
  ext j
  change w (g.symm (e.symm j)) = w (e.symm (e (g.symm (e.symm j))))
  rw [e.symm_apply_apply]

/-- Number the six actual coordinates outside the distinguished pair. -/
@[expose] def coordinateNumbering : H ≃ Fin 6 := Fintype.equivFinOfCardEq card_H

/-- The literal coordinate action with labels in `Fin 6`. -/
@[expose] def sixPointMap : ChiefFlag.Stabilizer →* Equiv.Perm (Fin 6) :=
  coordinateNumbering.permCongrHom.toMonoidHom.comp outerCoordinateAction

variable (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)

/-- The actual cocode fixed space as the six-point deleted representation. -/
def fixedEquivSix : U.toSubmodule ≃ₗ[ZMod 2] BinaryPermutation.Deleted (Fin 6) :=
  (fixedEquiv h h24.displacement h24.fixed_finrank).trans (relabelDeleted coordinateNumbering)

theorem fixedEquivSix_equivariant (g : ChiefFlag.Stabilizer) (v : U.toSubmodule) :
    fixedEquivSix h h24 (U.toRepresentation g v) =
      BinaryPermutation.deletedRepresentation (Fin 6) (sixPointMap g) (fixedEquivSix h h24 v) := by
  exact (congrArg (relabelDeleted coordinateNumbering)
    (fixedEquiv_equivariant h h24.displacement h24.fixed_finrank g v)).trans
      (relabelDeleted_equivariant coordinateNumbering _ _)

include h in
theorem sixPointMap_ker : sixPointMap.ker = Kernel.subgroupOf ChiefFlag.Stabilizer := by
  ext g
  change coordinateNumbering.permCongrHom (outerCoordinateAction g) = 1 ↔ _
  rw [map_eq_one_iff]
  · exact SetLike.ext_iff.mp (coordinateAction_ker h.injective h.kernel_image) g
  · exact coordinateNumbering.permCongrHom.injective

theorem sixPointMap_surjective : Function.Surjective sixPointMap :=
  coordinateNumbering.permCongrHom.surjective.comp
    (MonoidHom.range_eq_top.mp outerCoordinateAction_range)

open CocodeAction.Transvections
variable (ht : AmbientTransvectionInput m22SourceOctad)

abbrev outerAxis : Submodule (ZMod 2) (M22Cocode ⧸ U.toSubmodule) :=
  cocodeAxis

@[expose] def outerAxisSubrepresentation : Subrepresentation U.quotientRepresentation :=
  axisSubrepresentation h h24.displacement ht

@[expose] def outerParity : (M22Cocode ⧸ U.toSubmodule) →ₗ[ZMod 2] ZMod 2 := by
  change (M22Cocode ⧸ fixed (MonoidHom.id m22PairStabilizer) Kernel) →ₗ[ZMod 2] ZMod 2
  exact parity h h24.displacement ht

theorem outerParity_ker : (outerParity h h24 ht).ker = outerAxis :=
  parity_ker h h24.displacement ht

@[expose] def outerParameter : Kernel ≃* Multiplicative outerAxis := by
  change Kernel ≃* Multiplicative (axis (MonoidHom.id m22PairStabilizer) Kernel)
  exact transvectionEquiv h h24.displacement ht

theorem outer_kernel_action (a : Kernel) (x : M22Cocode ⧸ U.toSubmodule) :
    cocodeKernelAction a x = x + outerParity h h24 ht x • (outerParameter h h24 ht a).toAdd.val :=
  kernel_action h h24.displacement ht a x

/-- A faithful parameterization by all shear vectors gives the entire axis radical. -/
private theorem full_radical_of_shears {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : G →* BinaryLinear.GL V) (W : Submodule (ZMod 2) V)
    (l : V →ₗ[ZMod 2] ZMod 2) (e : G ≃* Multiplicative W)
    (hl : l.ker = W) (hs : Function.Surjective l)
    (haction : ∀ a x, ρ a x = x + l x • (e a).toAdd.val) :
    ρ.range = BinaryLinear.radical W := by
  ext t
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      have hp : l x = 0 := by
        rw [← hl] at hx
        exact hx
      rw [haction, hp, zero_smul, add_zero]
    · intro x
      rw [haction, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (e a).toAdd.property
  · intro htmem
    have hp : l ≠ 0 := by
      intro he
      obtain ⟨x, hx⟩ := hs 1
      rw [he, LinearMap.zero_apply] at hx
      exact zero_ne_one hx
    have htaxis : t ∈ BinaryTransvectionGroups.axisRootGroup ⊤ l := by
      refine ⟨Subgroup.mem_top _, ?_⟩
      rwa [hl]
    obtain ⟨_, b, hb, he⟩ := (BinaryTransvectionGroups.mem_axisRootGroup_iff hp).mp htaxis
    have hbaxis : b ∈ W := by rw [← hl]; exact hb
    obtain ⟨a, ha⟩ := e.surjective (Multiplicative.ofAdd (⟨b, hbaxis⟩ : W))
    refine ⟨a, ?_⟩
    ext x
    rw [haction, ha, he]
    rfl

include h h24 ht in
/-- Full transvections in the exact linear-action interface consumed by code duality. -/
theorem axisAction_full : cocodeKernelAction.range = BinaryLinear.radical outerAxis :=
  full_radical_of_shears cocodeKernelAction outerAxis (outerParity h h24 ht)
    (outerParameter h h24 ht) (outerParity_ker h h24 ht)
    (parity_surjective h h24.displacement ht) (outer_kernel_action h h24 ht)

/-- The earlier H.14 kernel module, specified independently of the code and
cocode. The marking is a group isomorphism with the actual intrinsic core,
and its equation is literal conjugation in the pair stabilizer. -/
structure KernelConjugationInput where
  quotientMap : ChiefFlag.Stabilizer →* Equiv.Perm (Fin 6)
  quotientMap_surjective : Function.Surjective quotientMap
  quotientMap_ker : quotientMap.ker = Kernel.subgroupOf ChiefFlag.Stabilizer
  marking : Multiplicative (BinaryPermutation.natural (Fin 6)) ≃* Kernel
  conjugation : ∀ (g : ChiefFlag.Stabilizer) v,
    (marking (Multiplicative.ofAdd
      (BinaryPermutation.naturalRepresentation (Fin 6) (quotientMap g) v))).val =
      g.val * (marking (Multiplicative.ofAdd v)).val * g.val⁻¹

variable (k : KernelConjugationInput)

@[expose] def axisKernelAddEquiv : outerAxis ≃+ BinaryPermutation.natural (Fin 6) :=
  (MulEquiv.toAdditiveLeft (transvectionEquiv h h24.displacement ht)).symm.trans
    (MulEquiv.toAdditiveLeft k.marking.symm)

/-- The constructed intertwiner from the cocode axis to the marked kernel. -/
@[expose] def axisKernelEquiv : outerAxis ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
  LinearEquiv.ofBijective ((axisKernelAddEquiv h h24 ht k).toAddMonoidHom.toZModLinearMap 2)
    (axisKernelAddEquiv h h24 ht k).bijective

theorem axisKernelEquiv_marking (v : outerAxis) :
    k.marking (Multiplicative.ofAdd (axisKernelEquiv h h24 ht k v)) =
      (transvectionEquiv h h24.displacement ht).symm (Multiplicative.ofAdd v) :=
  k.marking.apply_symm_apply _

theorem axisKernelEquiv_equivariant (g : ChiefFlag.Stabilizer) (v : outerAxis) :
    axisKernelEquiv h h24 ht k ((outerAxisSubrepresentation h h24 ht).toRepresentation g v) =
      BinaryPermutation.naturalRepresentation (Fin 6) (k.quotientMap g)
        (axisKernelEquiv h h24 ht k v) := by
  let a := (transvectionEquiv h h24.displacement ht).symm (Multiplicative.ofAdd v)
  have he := axisAction_conjugation h h24.displacement ht g a
  have hav : (transvectionEquiv h h24.displacement ht a).toAdd = v :=
    congrArg Multiplicative.toAdd ((transvectionEquiv h h24.displacement ht).apply_symm_apply _)
  rw [hav] at he
  have he' := congrArg (fun w : outerAxis =>
    (transvectionEquiv h h24.displacement ht).symm (Multiplicative.ofAdd w)) he
  simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply] at he'
  have hm : k.marking (Multiplicative.ofAdd
      (axisKernelEquiv h h24 ht k ((outerAxisSubrepresentation h h24 ht).toRepresentation g v))) =
      (transvectionEquiv h h24.displacement ht).symm
        (Multiplicative.ofAdd ((outerAxisSubrepresentation h h24 ht).toRepresentation g v)) :=
    axisKernelEquiv_marking h h24 ht k _
  apply Multiplicative.ofAdd.injective
  apply k.marking.injective
  apply Subtype.val_injective
  exact (congrArg Subtype.val hm).trans ((congrArg Subtype.val he').symm.trans
    ((k.conjugation g (axisKernelEquiv h h24 ht k v)).trans
      (congrArg (fun z : Kernel => g.val * z.val * g.val⁻¹)
        (axisKernelEquiv_marking h h24 ht k v))).symm)

/-- The H.15.2 action witnesses are constructed from the proved cocode
transfers and the independent H.14 conjugation marking. -/
@[expose] def cocodeActionData (h : OuterRestrictionInput m22SourceOctad)
    (h24 : AmbientFixedInput m22SourceOctad)
    (ht : AmbientTransvectionInput m22SourceOctad) (k : KernelConjugationInput) :
    CocodeActionData (BinaryPermutation.natural (Fin 6)) where
  quotientMap := sixPointMap
  quotientMap_surjective := sixPointMap_surjective
  quotientMap_ker := sixPointMap_ker h
  fixedEquiv := fixedEquivSix h h24
  fixedEquiv_equivariant := fixedEquivSix_equivariant h h24
  axis := outerAxisSubrepresentation h h24 ht
  axis_space := rfl
  kernelRepresentation := (BinaryPermutation.naturalRepresentation (Fin 6)).comp k.quotientMap
  kernelMarking := k.marking
  kernelMarking_equivariant := k.conjugation
  axisEquiv := axisKernelEquiv h h24 ht k
  axisEquiv_equivariant := axisKernelEquiv_equivariant h h24 ht k
  axisAction_full := axisAction_full h h24 ht

/-- The earlier group marking supplies the kernel model; it is not identified
with the separate six-coordinate marking without an intertwiner. -/
@[expose] def kernelModel (h : OuterRestrictionInput m22SourceOctad)
    (h24 : AmbientFixedInput m22SourceOctad)
    (ht : AmbientTransvectionInput m22SourceOctad) (k : KernelConjugationInput) :
    KernelModel (cocodeActionData h h24 ht k) where
  quotientMap := k.quotientMap
  quotientMap_surjective := k.quotientMap_surjective
  quotientMap_ker := k.quotientMap_ker
  naturalEquiv := LinearEquiv.refl _ _
  naturalEquiv_equivariant := fun _ _ => rfl

/-- All code clauses, with the intermediate M22 cocode-action witnesses
discharged. The remaining premises are the specified earlier M24, H.14,
and quintet dimension facts. -/
theorem code_clauses (h : OuterRestrictionInput m22SourceOctad)
    (h24 : AmbientFixedInput m22SourceOctad)
    (ht : AmbientTransvectionInput m22SourceOctad) (k : KernelConjugationInput)
    (hQ : QuintetDimensions) :
    CodeChiefActions (cocodeActionData h h24 ht k) h h24 ∧
      Module.finrank (ZMod 2) quintetFixedAnnihilator = 9 ∧
      codeCommutator Kernel ≤ quintetFixedAnnihilator ∧
      ¬ codeCommutator Kernel ≤ Representation.BinaryOffender.fixedSpace m22OuterCodeRepresentation
        (m22OuterQuintetKernel m22SourceSextet) ∧
      fixedCodeQuotient = commutatorImage :=
  code_chief_flag (cocodeActionData h h24 ht k) (kernelModel h h24 ht k) h h24 hQ

end MathieuCode.Hexad.Assembly
