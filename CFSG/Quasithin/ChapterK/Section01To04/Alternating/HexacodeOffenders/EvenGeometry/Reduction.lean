module
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.ModelContract
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.RatioFromStrong
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Plane kernels and offender bounds in the even hexacode cover

The coordinate projection is injective on two-subgroups. The proved A₇
permutation bound therefore bounds their elementary rank by two. Fixed
spaces are F₄ subspaces, so faithfulness gives fixed codimension at least
two; hence there are no strong offenders, and every offender has order four
and binary fixed dimension four.

An even operator fixing such a plane pointwise has determinant one and
trivial action on the one-dimensional quotient. Its displacement lies in
the plane. Thus the pointwise plane kernel is elementary abelian and has
order at most four. This identifies every offender with its full pointwise
kernel in the literal field coordinates required by the source contract.
Quasisimplicity then supplies generation as soon as one offender exists.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, K.1.3,
printed p.453 (PDF p.464). The explicit Sylow witness is supplied separately.
The concrete code and cover are the attributed ATLAS ports in the imports.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes
namespace CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders.EvenGeometry

private def letters : Fin 6 ↪ Fin 7 := ⟨Fin.castSucc, Fin.castSucc_injective 6⟩

private noncomputable def permutation : HexEvenAutomorphisms →* Equiv.Perm (Fin 7) :=
  (Equiv.Perm.viaEmbeddingHom letters).comp
    (hexCoordinateSixHom.comp hexSign.ker.subtype)

theorem elementary_card_le_four (A : Subgroup HexEvenAutomorphisms)
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 4 := by
  let _ := hA
  have hf : Function.Injective (permutation.comp A.subtype) := by
    have h := injective_comp_subtype_of_coprime_ker hexEvenCoordinate
      (by rw [hexEven_kernel_card]; decide : Nat.Coprime 2 (Nat.card hexEvenCoordinate.ker))
      A (IsElementaryAbelian.isPGroup 2 A)
    intro a b he
    apply h
    apply Subtype.ext
    exact Equiv.Perm.viaEmbeddingHom_injective letters he
  have he : A.map permutation ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨g, _, rfl⟩
    change Equiv.Perm.sign (Equiv.Perm.viaEmbeddingHom letters
      (hexCoordinateSixHom g.val)) = 1
    rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding,
      Equiv.Perm.sign_extendDomain]
    exact g.property
  have hc := Representation.AlternatingSevenConjugatePair.ElementaryGeometry.elementary_even_card_le
    (IsElementaryAbelian.map permutation (A := A)) he
  have hcard : Nat.card (A.map permutation) = Nat.card A := by
    conv_lhs => rw [← A.range_subtype, ← MonoidHom.range_comp]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  rwa [hcard] at hc

theorem elementary_rank_le_two (A : Subgroup HexEvenAutomorphisms)
    (hA : IsElementaryTwo A) : rank A ≤ 2 := by
  have h := elementary_card_le_four A hA.2
  rw [hA.card_eq_two_pow_rank] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h

theorem fixedSpace_scalar_stable (A : Subgroup HexEvenAutomorphisms) :
    hexZ ∈ subspaceStabilizer Hexacode.action (fixedSpace Hexacode.evenAction A) := by
  intro v
  constructor
  · intro hv a
    apply (hexAction hexZ).injective
    exact (Hexacode.action_commutes_scalar a.val.val a.val.property v).symm.trans (hv a)
  · intro hv a
    change Hexacode.action a.val.val (Hexacode.action hexZ v) = Hexacode.action hexZ v
    rw [Hexacode.scalar_eq_omega_smul, Hexacode.action_even_smul _ a.val.property]
    rw [show Hexacode.action a.val.val v = v from hv a]


theorem fixedCodim_ge_two (A : Subgroup HexEvenAutomorphisms) (hA : A ≠ ⊥) :
    2 ≤ fixedCodim Hexacode.evenAction A := by
  have hd := Hexacode.scalarSubmodule_finrank _ (fixedSpace_scalar_stable A)
  have hs := fixedCodim_add_finrank Hexacode.evenAction A
  rw [hexacode_finrank] at hs
  have hp := fixedCodim_pos_of_faithful Hexacode.evenAction
    (fun _ _ h => Subtype.ext (Hexacode.action_injective h)) hA
  change 2 * Module.finrank Hexacode.F (Hexacode.scalarSubmodule
    (fixedSpace Hexacode.evenAction A) (fixedSpace_scalar_stable A)) =
      Module.finrank (ZMod 2) (fixedSpace Hexacode.evenAction A) at hd
  omega

theorem no_strong : ¬ IsStrongFFModule Hexacode.evenAction := by
  rintro ⟨A, hA, hlt⟩
  have := fixedCodim_ge_two A hA.1
  have := elementary_rank_le_two A hA
  omega

theorem offender_dimensions (A : Subgroup HexEvenAutomorphisms)
    (hA : IsOffender Hexacode.evenAction A) :
    rank A = 2 ∧ Nat.card A = 4 ∧ fixedCodim Hexacode.evenAction A = 2 ∧
      Module.finrank (ZMod 2) (fixedSpace Hexacode.evenAction A) = 4 := by
  have hlo := fixedCodim_ge_two A hA.1.1
  have hhi := elementary_rank_le_two A hA.1
  have hoff := hA.2
  have hr : rank A = 2 := by omega
  have hc : Nat.card A = 4 := by rw [hA.1.card_eq_two_pow_rank, hr]; norm_num
  have hs := fixedCodim_add_finrank Hexacode.evenAction A
  rw [hexacode_finrank] at hs
  exact ⟨hr, hc, by omega, by omega⟩

theorem generated_of_ff (hff : IsFFModule Hexacode.evenAction) :
    offenderSubgroup Hexacode.evenAction = ⊤ := by
  let _ := Hexacode.even_isQuasisimple
  let _ := offenderSubgroup_normal Hexacode.evenAction
  rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top
    (offenderSubgroup Hexacode.evenAction) with hc | ht
  · obtain ⟨A, hA⟩ := (isFFModule_iff_exists_bestOffender Hexacode.evenAction).mp hff
    have hd := card_dvd_of_le ((hA.le_offenderSubgroup Hexacode.evenAction).trans hc)
    rw [(offender_dimensions A (hA.isOffender _)).2.1, Hexacode.even_center_card] at hd
    norm_num at hd
  · exact ht


open ChapterB.QuasisimpleSource

/-- The fixed space in the actual field coordinates of the source contract. -/
noncomputable def fixedPlane (A : Subgroup HexEvenAutomorphisms) :
    Submodule BinaryField.four.Carrier (Fin 3 → BinaryField.four.Carrier) where
  carrier := {w | modelCoordinates.symm w ∈ fixedSpace Hexacode.evenAction A}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change modelCoordinates.symm (v + w) ∈ fixedSpace Hexacode.evenAction A
    simpa only [map_add] using (fixedSpace Hexacode.evenAction A).add_mem hv hw
  smul_mem' c w hw := by
    have hs : modelCoordinates.symm (c • w) =
        fieldEquiv.symm c • modelCoordinates.symm w := by
      apply modelCoordinates.injective
      rw [modelCoordinates.apply_symm_apply, modelCoordinates_smul,
        fieldEquiv.apply_symm_apply, modelCoordinates.apply_symm_apply]
    change modelCoordinates.symm (c • w) ∈ fixedSpace Hexacode.evenAction A
    rw [hs]
    intro a
    change Hexacode.action a.val.val (fieldEquiv.symm c • modelCoordinates.symm w) = _
    rw [Hexacode.action_even_smul _ a.val.property]
    exact congrArg (fun v => fieldEquiv.symm c • v) (hw a)

theorem fixedPlane_comap (A : Subgroup HexEvenAutomorphisms) :
    ((fixedPlane A).restrictScalars (ZMod 2)).comap modelCoordinates.toLinearMap =
      fixedSpace Hexacode.evenAction A := by
  ext v
  change modelCoordinates.symm (modelCoordinates v) ∈ fixedSpace Hexacode.evenAction A ↔ _
  rw [modelCoordinates.symm_apply_apply]

noncomputable def fixedPlaneBinaryEquiv (A : Subgroup HexEvenAutomorphisms) :
    fixedSpace Hexacode.evenAction A ≃ₗ[ZMod 2] fixedPlane A where
  toFun v := ⟨modelCoordinates v, by change modelCoordinates.symm (modelCoordinates v) ∈ fixedSpace Hexacode.evenAction A; simpa only [modelCoordinates.symm_apply_apply] using v.property⟩
  invFun w := ⟨modelCoordinates.symm w, w.property⟩
  left_inv v := Subtype.ext (modelCoordinates.symm_apply_apply v)
  right_inv w := Subtype.ext (modelCoordinates.apply_symm_apply w)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem fixedPlane_finrank (A : Subgroup HexEvenAutomorphisms)
    (hA : IsOffender Hexacode.evenAction A) :
    Module.finrank BinaryField.four.Carrier (fixedPlane A) = 2 := by
  have hb : Nat.card (fixedSpace Hexacode.evenAction A) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      (offender_dimensions A hA).2.2.2]
    norm_num
  have hp : Nat.card (fixedPlane A) = 16 :=
    (Nat.card_congr (fixedPlaneBinaryEquiv A).toEquiv).symm.trans hb
  rw [Module.natCard_eq_pow_finrank (K := BinaryField.four.Carrier),
    BinaryField.four.card_eq] at hp
  exact Nat.pow_right_injective (by decide : 1 < 4) hp

/-- A determinant-one even operator fixing a field plane has displacement in it. -/
theorem plane_displacement (U : Submodule (ZMod 2) hexacode)
    (hs : hexZ ∈ subspaceStabilizer Hexacode.action U)
    (hd : Module.finrank (ZMod 2) U = 4)
    (g : HexEvenAutomorphisms) (hg : ∀ v ∈ U, Hexacode.evenAction g v = v)
    (v : hexacode) : Hexacode.evenAction g v - v ∈ U := by
  let W := Hexacode.scalarSubmodule U hs
  let _ : Module.Free Hexacode.F W := Module.Free.of_divisionRing Hexacode.F W
  let _ : Module.Free Hexacode.F (hexacode ⧸ W) := Module.Free.of_divisionRing Hexacode.F (hexacode ⧸ W)
  let f := (Hexacode.evenFieldAction g).toLinearMap
  have hW : W ≤ W.comap f := by
    intro w hw
    change f w ∈ W
    rw [show f w = w from hg w hw]
    exact hw
  have hr : f.restrict hW = LinearMap.id := by
    apply LinearMap.ext
    intro w
    exact Subtype.ext (hg w w.property)
  have hdW : Module.finrank Hexacode.F W = 2 := by
    have h := Hexacode.scalarSubmodule_finrank U hs
    change 2 * Module.finrank Hexacode.F W = Module.finrank (ZMod 2) U at h
    rw [hd] at h
    omega
  have hdQ : Module.finrank Hexacode.F (hexacode ⧸ W) = 1 := by
    have h := W.finrank_quotient_add_finrank
    rw [Hexacode.field_finrank, hdW] at h
    omega
  have hdg : LinearMap.det f = 1 := by
    dsimp only [f]
    rw [← LinearEquiv.coe_det, Hexacode.evenFieldAction_det]
    rfl
  have he := LinearMap.det_eq_det_mul_det W f hW
  rw [hdg, hr, LinearMap.det_id, one_mul] at he
  obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
    hdQ (W.mapQ W f hW)
  rw [hc, LinearMap.det_smul, LinearMap.det_id, hdQ, pow_one, mul_one] at he
  have hq : W.mapQ W f hW = LinearMap.id := by rw [hc, ← he, one_smul]
  exact (Submodule.Quotient.eq W).mp
    (LinearMap.congr_fun hq (Submodule.Quotient.mk v))

/-- Pointwise plane kernels act quadratically on the whole hexacode. -/
theorem planeKernel_quadratic (U : Submodule (ZMod 2) hexacode)
    (hs : hexZ ∈ subspaceStabilizer Hexacode.action U)
    (hd : Module.finrank (ZMod 2) U = 4) :
    IsQuadratic Hexacode.evenAction (subspaceKernel Hexacode.evenAction U ⊤) := by
  intro a ha b hb v
  exact ha.2 _ (plane_displacement U hs hd b hb.2 v)

private theorem binary_add_self (v : hexacode) : v + v = 0 := by
  have h : (2 : ZMod 2) • v = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
  simpa only [two_smul] using h

/-- The whole pointwise kernel is elementary, including the possibly trivial case. -/
theorem planeKernel_elementary (U : Submodule (ZMod 2) hexacode)
    (hs : hexZ ∈ subspaceStabilizer Hexacode.action U)
    (hd : Module.finrank (ZMod 2) U = 4) :
    IsElementaryAbelian 2 (subspaceKernel Hexacode.evenAction U ⊤) := by
  let K := subspaceKernel Hexacode.evenAction U ⊤
  have hq := planeKernel_quadratic U hs hd
  have hsq (g : K) : g * g = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply Hexacode.action_injective
    apply LinearMap.ext
    intro v
    change Hexacode.evenAction g.val (Hexacode.evenAction g.val v) = v
    have h := hq g.val g.property g.val g.property v
    rw [map_sub] at h
    have hz := binary_add_self (Hexacode.evenAction g.val v)
    have hzv := binary_add_self v
    apply sub_eq_zero.mp
    calc
      _ = (Hexacode.evenAction g.val (Hexacode.evenAction g.val v) -
          Hexacode.evenAction g.val v) - (Hexacode.evenAction g.val v - v) +
          (Hexacode.evenAction g.val v + Hexacode.evenAction g.val v) - (v + v) := by abel
      _ = 0 := by rw [h, sub_self, hz, hzv]; simp
  have hi (g : K) : g⁻¹ = g := inv_eq_of_mul_eq_one_left (hsq g)
  exact {
    toIsMulCommutative := ⟨⟨fun x y => by
      calc x * y = (x * y)⁻¹ := (hi _).symm
           _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
           _ = y * x := by rw [hi, hi]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun g => by simpa only [pow_two] using hsq g) }

/-- The cubic cover's pointwise plane kernel has order at most four. -/
theorem planeKernel_card_le_four (U : Submodule (ZMod 2) hexacode)
    (hs : hexZ ∈ subspaceStabilizer Hexacode.action U)
    (hd : Module.finrank (ZMod 2) U = 4) :
    Nat.card (subspaceKernel Hexacode.evenAction U ⊤) ≤ 4 :=
  elementary_card_le_four _ (planeKernel_elementary U hs hd)

/-- Every offender is the full pointwise kernel of its fixed plane. -/
theorem offender_eq_kernel (A : Subgroup HexEvenAutomorphisms)
    (hA : IsOffender Hexacode.evenAction A) :
    A = subspaceKernel Hexacode.evenAction (fixedSpace Hexacode.evenAction A) ⊤ := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro a ha
    exact ⟨mem_top _, fun v hv => hv ⟨a, ha⟩⟩
  · rw [(offender_dimensions A hA).2.1]
    exact planeKernel_card_le_four _ (fixedSpace_scalar_stable A)
      (offender_dimensions A hA).2.2.2

/-- All best offenders have the literal plane-kernel form required by K.1.3. -/
theorem bestOffender_plane (A : Subgroup HexEvenAutomorphisms)
    (hA : IsBestOffender Hexacode.evenAction A) :
    ∃ P : Submodule BinaryField.four.Carrier (Fin 3 → BinaryField.four.Carrier),
      Module.finrank BinaryField.four.Carrier P = 2 ∧
      A = subspaceKernel Hexacode.evenAction
        ((P.restrictScalars (ZMod 2)).comap modelCoordinates.toLinearMap) ⊤ := by
  refine ⟨fixedPlane A, fixedPlane_finrank A (hA.isOffender _), ?_⟩
  rw [fixedPlane_comap]
  exact offender_eq_kernel A (hA.isOffender _)


/-- One actual four-group with a four-dimensional fixed space supplies the
remaining existence input; the universal offender classification is proved above. -/
theorem model_of_four (A : Subgroup HexEvenAutomorphisms)
    (he : IsElementaryAbelian 2 A) (hc : Nat.card A = 4)
    (hf : Module.finrank (ZMod 2) (fixedSpace Hexacode.evenAction A) = 4) :
    ModelCalculation Hexacode.evenAction ⊤ := by
  have hn : A ≠ ⊥ := by intro h; rw [h, Subgroup.card_bot] at hc; omega
  have hr : rank A = 2 := by rw [rank, hc]; decide
  have hsum := fixedCodim_add_finrank Hexacode.evenAction A
  rw [hexacode_finrank, hf] at hsum
  have hff : IsFFModule Hexacode.evenAction := ⟨A, ⟨hn, he⟩, by omega⟩
  exact ⟨generated_of_ff hff,
    quadraticRatio_eq_one_of_no_strong _ hff (fun B hB => no_strong ⟨B, hB⟩),
    bestOffender_plane⟩

end CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders.EvenGeometry
