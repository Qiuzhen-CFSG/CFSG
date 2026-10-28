module
public import Theory.GroupTheory.WreathTwoSylowCentralizer
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.CoordinateModel
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Centralization.Reductions

/-!
# Actual automizer coordinates and dual-core transport

The compatible faithful wreath action embeds the actual induced automizer of
any `A ≤ M` into the literal coordinate actor, with range exactly the image
of `A`. Equivariance transports every fixed subgroup, the Chapter E dual
core, and their intersection; conjugating the actor uses its actual vector
action for the same transport.

For the nonnormalizing conjugate in 15.3.46(4), the earlier reduction gives
image rank greater than one. The concrete dihedral Sylow centralizer bound
then gives image order four. The kernel index formula proves `|C_A(V)|=4`.
The remaining core sizes are delegated only to the separate finite coordinate
calculation; none is a hypothesis of the natural-action interface.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.46(4), printed p.1141; E.3.30–32, pp.237–238; Definition F.4.41, p.294.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization.CoreGeometry
open Subgroup
attribute [local instance] orthogonalAction

/-- The literal action, viewed as a homomorphism into vector automorphisms. -/
def coordinateAction : OrthogonalActor →* MulAut OrthogonalVector :=
  MulDistribMulAction.toMulAut _ _

theorem coordinateAction_injective : Function.Injective coordinateAction := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := FourGroupMatrixCoordinates.naturalAction_faithful
  let _ := orthogonalAction
  let _ : FaithfulSMul OrthogonalActor OrthogonalVector :=
    RegularWreathProduct.functionModule_faithful _ _ _
  intro a b hab
  exact FaithfulSMul.eq_of_smul_eq_smul (fun v => MulEquiv.congr_fun hab v)

variable {G : Type*} [Group G] {M V A : Subgroup G}
variable (d : CFSG.Quasithin.Chapter15.Section03.NaturalOrthogonalAction M V)

/-- The automizer action after changing vector coordinates. -/
def transportedAction : ChapterE.inducedAutomizer V A →* MulAut OrthogonalVector :=
  (MulAut.congr d.coordinates).toMonoidHom.comp
    ((ChapterE.Automizer V).subtype.comp (ChapterE.inducedAutomizer V A).subtype)

theorem transportedAction_mem_range (hAM : A ≤ M)
    (a : ChapterE.inducedAutomizer V A) : transportedAction d a ∈ coordinateAction.range := by
  obtain ⟨n, hn, ha⟩ := a.property
  refine ⟨d.actor ⟨n, hAM hn⟩, ?_⟩
  apply MulEquiv.ext
  intro w
  obtain ⟨v, rfl⟩ := d.coordinates.surjective w
  change (d.actor ⟨n, hAM hn⟩) • d.coordinates v =
    d.coordinates ((a : ChapterE.Automizer V).val (d.coordinates.symm (d.coordinates v)))
  rw [d.coordinates.symm_apply_apply, ← ha]
  exact (d.compatible ⟨n, hAM hn⟩ v).symm

/-- The actual induced automizer embedded in the faithful coordinate actor. -/
noncomputable def inducedCoordinateHom (hAM : A ≤ M) :
    ChapterE.inducedAutomizer V A →* OrthogonalActor :=
  (MonoidHom.ofInjective coordinateAction_injective).symm.toMonoidHom.comp
    ((transportedAction d).codRestrict coordinateAction.range
      (transportedAction_mem_range d hAM))

theorem coordinateAction_inducedCoordinateHom (hAM : A ≤ M)
    (a : ChapterE.inducedAutomizer V A) :
    coordinateAction (inducedCoordinateHom d hAM a) = transportedAction d a :=
  MonoidHom.apply_ofInjective_symm coordinateAction_injective _

theorem inducedCoordinateHom_injective (hAM : A ≤ M) :
    Function.Injective (inducedCoordinateHom d hAM) := by
  intro a b hab
  have ht := congrArg coordinateAction hab
  rw [coordinateAction_inducedCoordinateHom, coordinateAction_inducedCoordinateHom] at ht
  apply Subtype.ext
  apply Subtype.ext
  exact (MulAut.congr d.coordinates).injective ht

theorem inducedCoordinateHom_compatible (hAM : A ≤ M)
    (a : ChapterE.inducedAutomizer V A) (v : V) :
    d.coordinates ((a : ChapterE.Automizer V).val v) =
      inducedCoordinateHom d hAM a • d.coordinates v := by
  have ht := MulEquiv.congr_fun (coordinateAction_inducedCoordinateHom d hAM a)
    (d.coordinates v)
  change inducedCoordinateHom d hAM a • d.coordinates v =
    d.coordinates ((a : ChapterE.Automizer V).val
    (d.coordinates.symm (d.coordinates v))) at ht
  change _ = inducedCoordinateHom d hAM a • d.coordinates v
  simpa only [d.coordinates.symm_apply_apply] using ht.symm

/-- Its range is exactly the image of `A` under the compatible actor map. -/
theorem inducedCoordinateHom_range (hAM : A ≤ M) :
    (inducedCoordinateHom d hAM).range = (A.subgroupOf M).map d.actor := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨n, hn, ha⟩ := a.property
    refine ⟨⟨n, hAM hn⟩, hn, ?_⟩
    apply coordinateAction_injective
    rw [coordinateAction_inducedCoordinateHom]
    apply MulEquiv.ext
    intro w
    obtain ⟨v, rfl⟩ := d.coordinates.surjective w
    change d.actor ⟨n, hAM hn⟩ • d.coordinates v =
      d.coordinates ((a : ChapterE.Automizer V).val (d.coordinates.symm (d.coordinates v)))
    rw [d.coordinates.symm_apply_apply, ← ha]
    exact (d.compatible ⟨n, hAM hn⟩ v).symm
  · rintro _ ⟨m, hm, rfl⟩
    let n : normalizer (V : Set G) := ⟨m, d.normalizes m.property⟩
    let a : ChapterE.inducedAutomizer V A :=
      ⟨V.normalizerMonoidHom.rangeRestrict n, ⟨n, hm, rfl⟩⟩
    refine ⟨a, ?_⟩
    apply coordinateAction_injective
    rw [coordinateAction_inducedCoordinateHom]
    apply MulEquiv.ext
    intro w
    obtain ⟨v, rfl⟩ := d.coordinates.surjective w
    change d.coordinates (V.normalizerMonoidHom n
      (d.coordinates.symm (d.coordinates v))) = d.actor m • d.coordinates v
    rw [d.coordinates.symm_apply_apply]
    exact d.compatible m v

end CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization.CoreGeometry

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization.CoreGeometry
open Subgroup ChapterE
section Transfer
variable {R S H K : Type*} [Group R] [Group S] [Group H] [Group K]
  (ρ : R →* MulAut H) (σ : S →* MulAut K) (e : R ≃* S) (f : H ≃* K)
  (he : ∀ r h, f (ρ r h) = σ (e r) (f h))

include he

private theorem map_actionCentralizer (X : Subgroup R) :
    (actionCentralizer ρ X).map (f : H →* K) =
      actionCentralizer σ (X.map (e : R →* S)) := by
  ext k
  constructor
  · rintro ⟨h, hh, rfl⟩ s ⟨r, hr, rfl⟩
    change σ (e r) (f h) = f h
    rw [← he, hh r hr]
  · intro hk
    refine ⟨f.symm k, ?_, f.apply_symm_apply k⟩
    intro r hr
    apply f.injective
    rw [he, f.apply_symm_apply]
    exact hk (e r) ⟨r, hr, rfl⟩

private theorem map_dualGeneratedCore (n : ℕ) :
    (dualGeneratedCore ρ n).map (f : H →* K) = dualGeneratedCore σ n := by
  apply le_antisymm
  · rw [dualGeneratedCore, Subgroup.map_iSup]
    apply iSup_le
    intro X
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hX
    rw [map_actionCentralizer ρ σ e f he]
    exact actionCentralizer_le_dualGeneratedCore σ (by rwa [index_map_equiv])
  · apply dualGeneratedCore_le
    intro Y hY
    have hmap : (Y.map (e.symm : S →* R)).map (e : R →* S) = Y := by
      rw [map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.symm_trans_self,
        MulEquiv.coe_monoidHom_refl, map_id]
    rw [← hmap, ← map_actionCentralizer ρ σ e f he]
    apply map_mono
    exact actionCentralizer_le_dualGeneratedCore ρ (by rwa [index_map_equiv])
end Transfer
end CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization.CoreGeometry

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization.CoreGeometry
open Subgroup ChapterE
attribute [local instance] orthogonalAction
variable {G : Type*} [Group G] {M V A : Subgroup G}
variable (d : CFSG.Quasithin.Chapter15.Section03.NaturalOrthogonalAction M V)

/-- The faithful coordinate image of the actual induced automizer. -/
noncomputable def coordinateImage (hAM : A ≤ M) : Subgroup OrthogonalActor :=
  (inducedCoordinateHom d hAM).range

/-- The genuine equivalence between the induced automizer and its coordinate image. -/
noncomputable def coordinateImageEquiv (hAM : A ≤ M) :
    inducedAutomizer V A ≃* coordinateImage d hAM :=
  MonoidHom.ofInjective (inducedCoordinateHom_injective d hAM)

/-- The action of a coordinate subgroup on the literal four-space. -/
def imageAction (J : Subgroup OrthogonalActor) : J →* MulAut OrthogonalVector :=
  coordinateAction.comp J.subtype

/-- The dual core, at one, computed in the literal four-space. -/
noncomputable def imageCore (J : Subgroup OrthogonalActor) : Subgroup OrthogonalVector :=
  dualGeneratedCore (imageAction J) 1

/-- Coordinates identify the actual dual core with the core of its actual image. -/
theorem coordinate_core (hAM : A ≤ M) :
    (dualGeneratedCore ((Automizer V).subtype.comp (inducedAutomizer V A).subtype) 1).map
      d.coordinates.toMonoidHom = imageCore (coordinateImage d hAM) := by
  apply map_dualGeneratedCore _ _ (coordinateImageEquiv d hAM) d.coordinates
  intro a v
  exact inducedCoordinateHom_compatible d hAM a v

/-- The same coordinates identify the fixed subgroup of the whole image. -/
theorem coordinate_fixed (hAM : A ≤ M) :
    (actionCentralizer ((Automizer V).subtype.comp (inducedAutomizer V A).subtype) ⊤).map
      d.coordinates.toMonoidHom =
        actionCentralizer (imageAction (coordinateImage d hAM)) ⊤ := by
  have he := map_actionCentralizer
    ((Automizer V).subtype.comp (inducedAutomizer V A).subtype)
    (imageAction (coordinateImage d hAM)) (coordinateImageEquiv d hAM) d.coordinates
    (inducedCoordinateHom_compatible d hAM) ⊤
  simp only [Subgroup.map_equiv_top] at he
  exact he

/-- Cardinality transport for the ambient dual core. -/
theorem card_ambient_core (hAM : A ≤ M) :
    Nat.card (automizerDualCore V (inducedAutomizer V A) 1) =
      Nat.card (imageCore (coordinateImage d hAM)) := by
  rw [automizerDualCore, card_map_of_injective V.subtype_injective,
    ← coordinate_core d hAM, card_map_of_injective d.coordinates.injective]

include d in
private theorem ambient_fixed (hAM : A ≤ M) :
    (actionCentralizer ((Automizer V).subtype.comp (inducedAutomizer V A).subtype) ⊤).map
      V.subtype = V ⊓ centralizer (A : Set G) := by
  apply core_actionCentralizer_map (hAM.trans d.normalizes)
  ext a
  constructor
  · intro ha
    exact ⟨⟨a, ha⟩, mem_top _, rfl⟩
  · rintro ⟨a, _, rfl⟩
    exact a.property

/-- Cardinality transport for fixed points inside the ambient dual core. -/
theorem card_ambient_core_fixed (hAM : A ≤ M) :
    Nat.card (automizerDualCore V (inducedAutomizer V A) 1 ⊓
      centralizer (A : Set G) : Subgroup G) =
    Nat.card (imageCore (coordinateImage d hAM) ⊓
      actionCentralizer (imageAction (coordinateImage d hAM)) ⊤ : Subgroup OrthogonalVector) := by
  rw [← coordinate_core d hAM, ← coordinate_fixed d hAM,
    ← map_inf _ _ _ d.coordinates.injective,
    card_map_of_injective d.coordinates.injective]
  rw [← card_map_of_injective (K := dualGeneratedCore
    ((Automizer V).subtype.comp (inducedAutomizer V A).subtype) 1 ⊓
    actionCentralizer ((Automizer V).subtype.comp (inducedAutomizer V A).subtype) ⊤)
    V.subtype_injective, map_inf _ _ _ V.subtype_injective, ambient_fixed d hAM]
  change Nat.card (automizerDualCore V (inducedAutomizer V A) 1 ⊓ centralizer (A : Set G) :
    Subgroup G) = Nat.card (automizerDualCore V (inducedAutomizer V A) 1 ⊓
      (V ⊓ centralizer (A : Set G)) : Subgroup G)
  rw [← inf_assoc, inf_eq_left.mpr (automizerDualCore_le _ _ _)]

/-- Properness of the ambient core excludes the full coordinate core. -/
theorem imageCore_ne_top (hAM : A ≤ M)
    (hproper : automizerDualCore V (inducedAutomizer V A) 1 < V) :
    imageCore (coordinateImage d hAM) ≠ ⊤ := by
  intro he
  have htop : dualGeneratedCore
      ((Automizer V).subtype.comp (inducedAutomizer V A).subtype) 1 = ⊤ := by
    apply map_injective (f := d.coordinates.toMonoidHom) d.coordinates.injective
    rw [coordinate_core d hAM, he, map_top_of_surjective _ d.coordinates.surjective]
  apply hproper.ne
  rw [automizerDualCore, htop]
  ext v
  constructor
  · rintro ⟨w, _, rfl⟩; exact w.property
  · intro hv; exact ⟨⟨v, hv⟩, mem_top _, rfl⟩

include d in
/-- The image cardinal is the exact centralizer index, before taking logarithms. -/
theorem card_inducedAutomizer (hAM : A ≤ M) :
    Nat.card (inducedAutomizer V A) = (A ⊓ centralizer (V : Set G)).relIndex A := by
  unfold inducedAutomizer
  rw [← relIndex_ker, MonoidHom.ker_rangeRestrict, normalizerMonoidHom_ker,
    relIndex_subgroupOf (hAM.trans d.normalizes), inf_relIndex_left]

end CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization.CoreGeometry

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization.CoreGeometry
open Subgroup ChapterE
open scoped IsMulCommutative
variable {G : Type*} [Group G] {M V A : Subgroup G}
variable (d : CFSG.Quasithin.Chapter15.Section03.NaturalOrthogonalAction M V)

/-- Elementary abelianness is retained by the actual coordinate image. -/
theorem coordinateImage_elementary [IsElementaryAbelian 2 A] (hAM : A ≤ M) :
    IsElementaryAbelian 2 (coordinateImage d hAM) := by
  let _ := inducedAutomizer_elementary V A (hAM.trans d.normalizes)
  exact IsElementaryAbelian.of_surjective (coordinateImageEquiv d hAM).toMonoidHom
    (coordinateImageEquiv d hAM).surjective

/-- The coordinate image has exactly the same binary rank as the actual automizer. -/
theorem coordinateImage_rank (hAM : A ≤ M) :
    Representation.BinaryOffender.rank (coordinateImage d hAM) =
      Representation.BinaryOffender.rank (inducedAutomizer V A) := by
  unfold Representation.BinaryOffender.rank
  rw [← Nat.card_congr (coordinateImageEquiv d hAM).toEquiv]

/-- Every elementary subgroup of the concrete actor of rank greater than one
has order four, using the proved dihedral Sylow centralizer bound. -/
theorem card_four_of_coordinate_rank (J : Subgroup OrthogonalActor)
    [IsElementaryAbelian 2 J] (hr : 1 < Representation.BinaryOffender.rank J) :
    Nat.card J = 4 := by
  have hlo : 4 ≤ Nat.card J := by
    by_contra hn
    have hh := Nat.log_mono_right (b := 2) (show Nat.card J ≤ 3 by omega)
    norm_num at hh
    unfold Representation.BinaryOffender.rank at hr
    omega
  obtain ⟨S, hJS⟩ := (IsElementaryAbelian.isPGroup 2 J).exists_le_sylow
  have hJC : J ≤ centralizer (J : Set OrthogonalActor) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hhi := (card_le_of_le (le_inf hJS hJC)).trans
    (wreath_two_sylow_centralizer_le_of_card_ge_four S J hJS hlo).2
  exact Nat.le_antisymm hhi hlo

variable [Finite G] {T : Sylow 2 G} {P : Subgroup G} [IsElementaryAbelian 2 V]

/-- In the nonnormalizing source case the actual induced automizer has order four. -/
theorem card_inducedAutomizer_conjugate
    (q : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (k : OrthogonalCoordinateModel q P)
    (c : OrthogonalFusionCalculations T M V P q.form) (g : G)
    (hgT : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hn : ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    Nat.card (inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom)) = 4 := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAM : A ≤ M := hgT.trans h.sylow_le
  let _ := coordinateImage_elementary k.action hAM
  rw [Nat.card_congr (coordinateImageEquiv k.action hAM).toEquiv]
  apply card_four_of_coordinate_rank
  rw [coordinateImage_rank]
  exact one_lt_automizer_rank q h c g hgT hn

/-- The fixed subgroup `C_A(V)` has order four in the source's second case. -/
theorem card_conjugate_fixed
    (q : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (k : OrthogonalCoordinateModel q P)
    (c : OrthogonalFusionCalculations T M V P q.form) (g : G)
    (hgT : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hn : ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    Nat.card (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) : Subgroup G) = 4 := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let B := A ⊓ centralizer (V : Set G)
  have hBA : B ≤ A := inf_le_left
  have hindex : B.relIndex A = 4 := by
    rw [← card_inducedAutomizer k.action (hgT.trans h.sylow_le)]
    exact card_inducedAutomizer_conjugate q h k c g hgT hn
  have hA : Nat.card A = 16 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact k.action.card_vector
  have hmul := (B.subgroupOf A).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv, hA] at hmul
  change B.relIndex A * Nat.card B = 16 at hmul
  rw [hindex] at hmul
  change Nat.card B = 4
  omega
end CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization.CoreGeometry

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization.CoreGeometry
open Subgroup ChapterE
attribute [local instance] orthogonalAction

/-- Conjugating an actor subgroup transports its core by that actor's vector action. -/
theorem imageCore_conjugate (J : Subgroup OrthogonalActor) (a : OrthogonalActor) :
    (imageCore J).map (coordinateAction a).toMonoidHom =
      imageCore (J.map (MulAut.conj a).toMonoidHom) := by
  apply map_dualGeneratedCore _ _ ((MulAut.conj a).subgroupMap J) (coordinateAction a)
  intro j v
  change a • ((j : OrthogonalActor) • v) =
    (a * (j : OrthogonalActor) * a⁻¹) • (a • v)
  simp only [mul_smul, inv_smul_smul]

/-- The common fixed subgroup is transported by the same vector automorphism. -/
theorem imageFixed_conjugate (J : Subgroup OrthogonalActor) (a : OrthogonalActor) :
    (actionCentralizer (imageAction J) ⊤).map (coordinateAction a).toMonoidHom =
      actionCentralizer (imageAction (J.map (MulAut.conj a).toMonoidHom)) ⊤ := by
  have hcompat (j : J) (v : OrthogonalVector) :
      coordinateAction a (imageAction J j v) =
        imageAction (J.map (MulAut.conj a).toMonoidHom)
          ((MulAut.conj a).subgroupMap J j) (coordinateAction a v) := by
    change a • ((j : OrthogonalActor) • v) =
      (a * (j : OrthogonalActor) * a⁻¹) • (a • v)
    simp only [mul_smul, inv_smul_smul]
  have he := map_actionCentralizer (imageAction J)
    (imageAction (J.map (MulAut.conj a).toMonoidHom))
    ((MulAut.conj a).subgroupMap J) (coordinateAction a) hcompat ⊤
  have htop : (⊤ : Subgroup J).map
      ((MulAut.conj a).subgroupMap J).toMonoidHom = ⊤ :=
    map_top_of_surjective ((MulAut.conj a).subgroupMap J).toMonoidHom
      ((MulAut.conj a).subgroupMap J).surjective
  exact he.trans (congrArg (actionCentralizer
    (imageAction (J.map (MulAut.conj a).toMonoidHom))) htop)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization.CoreGeometry
