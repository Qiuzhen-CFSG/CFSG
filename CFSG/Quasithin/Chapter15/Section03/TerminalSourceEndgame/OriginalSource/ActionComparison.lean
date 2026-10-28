module

public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.SourceControls
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.OrbitConstruction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.CoordinateLifting
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Comparing the source orthogonal actions

The original standard coordinates pull back the quadratic form. The public
wreath-coordinate theorem then supplies the intrinsic four-space coordinates.
Both action homomorphisms have the actual centralizer as kernel, so the
canonical quotient equivalence transports the residual image. The two definite
coordinate planes have the same normalizer in M; hence the original conjugating
element is retained without a new plane-marking assumption.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.66–68
and the final proof of 15.3.1, printed pp.1152–1155.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource

open Subgroup OrthogonalFourBinary Theory.AlgebraicGroup
open scoped IsMulCommutative
open AbelianAmalgam.GoldschmidtCore.LocalRelations

private theorem standard_nondegenerate : form.polarBilin.Nondegenerate := by
  change (∀ x : Space, (∀ y : Space, form.polarBilin x y = 0) → x = 0) ∧
    (∀ y : Space, (∀ x : Space, form.polarBilin x y = 0) → y = 0)
  decide +kernel

private def diagonal : Plane →ₗ[F] Space :=
  LinearMap.prod LinearMap.id LinearMap.id

private theorem standard_plus_type : ∃ W : Submodule F Space,
    Module.finrank F W = 2 ∧ ∀ w ∈ W, form w = 0 := by
  refine ⟨diagonal.range, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (f := diagonal)
      (fun x y h => congrArg Prod.fst h)]
    simp [Plane, Module.finrank_prod]
  · rintro _ ⟨v, rfl⟩
    have h : ∀ v : Plane, form (v, v) = 0 := by decide +kernel
    exact h v

variable {G : Type*} [Group G] {M V P : Subgroup G}

/-- The given standard coordinates already imply the required binary
elementary structure; it is not an additional source hypothesis. -/
theorem standard_elementary (d : NaturalAction V M) : IsElementaryAbelian 2 V := by
  let : IsElementaryAbelian 2 (Multiplicative Space) := {
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro v
      rw [pow_two]
      change v.toAdd + v.toAdd = 0
      exact CharTwo.add_self_eq_zero _ }
  exact IsElementaryAbelian.of_surjective d.coordinates.symm.toMonoidHom
    d.coordinates.symm.surjective

variable [IsElementaryAbelian 2 V]

noncomputable def standardLinearCoordinates (d : NaturalAction V M) :
    Additive V ≃ₗ[F] Space :=
  d.coordinates.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)

noncomputable def pulledForm (d : NaturalAction V M) : QuadraticForm F (Additive V) :=
  form.comp (standardLinearCoordinates d).toLinearMap

noncomputable def standardIsometry (d : NaturalAction V M) :
    (pulledForm d).IsometryEquiv form :=
  ⟨standardLinearCoordinates d, fun _ => rfl⟩

omit [IsElementaryAbelian 2 V] in
private theorem standard_coordinates_conjugate (d : NaturalAction V M) (m : M) (v : V) :
    d.coordinates (V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ v) =
      Multiplicative.ofAdd ((d.action m).val (d.coordinates v).toAdd) := by
  have h : d.coordinates.symm
      (Multiplicative.ofAdd ((d.action m).val (d.coordinates v).toAdd)) =
      V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ v :=
    Subtype.ext (d.intertwines m v)
  exact (congrArg d.coordinates h).symm.trans (d.coordinates.apply_symm_apply _)

/-- Pull back the original standard form and action, keeping its vector map. -/
noncomputable def quadraticAction (d : NaturalAction V M) :
    FusionCore.NaturalOrthogonalAction M V where
  normalizes := d.normalizes
  form := pulledForm d
  nondegenerate := by
    rw [pulledForm, QuadraticMap.polarBilin_comp]
    change (LinearMap.BilinForm.congr (standardLinearCoordinates d).symm
      form.polarBilin).Nondegenerate
    exact LinearMap.BilinForm.Nondegenerate.congr (standardLinearCoordinates d).symm
      standard_nondegenerate
  dimension := by
    simpa [Space, Plane, Module.finrank_prod] using (standardLinearCoordinates d).finrank_eq
  plusType := by
    obtain ⟨W, hdim, hW⟩ := standard_plus_type
    refine ⟨W.map (standardLinearCoordinates d).symm.toLinearMap, ?_, ?_⟩
    · exact ((standardLinearCoordinates d).symm.finrank_map_eq W).trans hdim
    · rintro v ⟨w, hw, rfl⟩
      change form (standardLinearCoordinates d ((standardLinearCoordinates d).symm w)) = 0
      rw [(standardLinearCoordinates d).apply_symm_apply]
      exact hW w hw
  preserves := by
    intro m v
    change form (d.coordinates (V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ v)).toAdd =
      form (d.coordinates v).toAdd
    rw [standard_coordinates_conjugate]
    exact (mem_quadraticIsometrySubgroup form _).mp (d.action m).property _
  full := by
    intro b
    let e := standardIsometry d
    let a : form.IsometryEquiv form := (e.symm.trans b).trans e
    let aa : OrthogonalFourBinary.TerminalLines.IsometryGroup :=
      ⟨a.toLinearEquiv, (mem_quadraticIsometrySubgroup form _).mpr a.map_app'⟩
    obtain ⟨m, hm⟩ := d.onto aa
    refine ⟨m, ?_⟩
    intro v
    rw [← d.intertwines, hm]
    apply congrArg (fun v : V => (v : G))
    apply d.coordinates.injective
    rw [d.coordinates.apply_symm_apply]
    change Multiplicative.ofAdd (e (b (e.symm (e (Additive.ofMul v))))) =
      d.coordinates (b (Additive.ofMul v)).toMul
    rw [e.symm_apply_apply]
    rfl

theorem quadraticAction_singular (d : NaturalAction V M) (v : V) :
    (quadraticAction d).form (Additive.ofMul v) = 0 ↔ d.singular v := Iff.rfl

theorem definite_of_standard (d : NaturalAction V M)
    (hPV : P ≤ V) (hPcard : Nat.card P = 4)
    (hP : ∀ p : P, p ≠ 1 → ¬ d.singular ⟨p, hPV p.property⟩) :
    FusionCore.IsDefinitePlane (quadraticAction d).form P := by
  refine ⟨hPV, hPcard, ?_⟩
  intro v hv hn
  have hne : (⟨v, hv⟩ : P) ≠ 1 := by
    intro he
    apply hn
    exact Subtype.ext (congrArg (fun x : P => (x : G)) he)
  exact hP ⟨v, hv⟩ hne

variable [Finite G]

theorem coordinates_from_standard (d : NaturalAction V M)
    (hP : FusionCore.IsDefinitePlane (quadraticAction d).form P) :
    Nonempty (FusionCore.OrthogonalCoordinateModel (quadraticAction d) P) :=
  FusionCore.orthogonalCoordinateModel_nonempty_of_isometry (quadraticAction d) hP
    (standardIsometry d)

/-- Canonical comparison of the actual action quotients through their common kernel. -/
noncomputable def actorComparison (d : NaturalAction V M)
    (w : NaturalOrthogonalAction M V) :
    OrthogonalFourBinary.TerminalLines.IsometryGroup ≃* OrthogonalActor :=
  (QuotientGroup.quotientKerEquivOfSurjective d.action d.onto).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ((action_ker d).trans w.ker_actor.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective w.actor w.onto))

omit [IsElementaryAbelian 2 V] [Finite G] in
theorem actorComparison_apply (d : NaturalAction V M)
    (w : NaturalOrthogonalAction M V) (m : M) :
    actorComparison d w (d.action m) = w.actor m := by
  let e := QuotientGroup.quotientKerEquivOfSurjective d.action d.onto
  have he : e (QuotientGroup.mk' d.action.ker m) = d.action m := rfl
  change (QuotientGroup.quotientKerEquivOfSurjective w.actor w.onto)
    (QuotientGroup.quotientMulEquivOfEq ((action_ker d).trans w.ker_actor.symm)
      (e.symm (d.action m))) = w.actor m
  rw [← he, e.symm_apply_apply]
  rfl

omit [IsElementaryAbelian 2 V] [Finite G] in
theorem residual_image_of_standard (d : NaturalAction V M)
    (w : NaturalOrthogonalAction M V) (Y : Subgroup G)
    (hY : actionImage d Y = pResidual 2 OrthogonalFourBinary.TerminalLines.IsometryGroup) :
    w.image Y = pResidual 2 OrthogonalActor := by
  have hmap : (actionImage d Y).map (actorComparison d w).toMonoidHom = w.image Y := by
    rw [actionImage, Subgroup.map_map]
    change (Y.subgroupOf M).map _ = (Y.subgroupOf M).map _
    congr 1
    apply MonoidHom.ext
    intro m
    exact actorComparison_apply d w m
  rw [← hmap, hY, map_pResidual_of_surjective 2 _ (actorComparison d w).surjective]

omit [Finite G] in
theorem conjugator_preserves_first_plane
    {T : Sylow 2 G} {q : FusionCore.NaturalOrthogonalAction M V}
    (k : FusionCore.OrthogonalCoordinateModel q P)
    (hTM : (T : Subgroup G) ≤ M) {s : G} (hs : s ∈ planeStabilizer T P) :
    s ∈ planeStabilizer T (k.action.plane 1) := by
  obtain ⟨i, hi⟩ := k.plane_eq
  have he : (normalizer (k.action.plane i : Set G)).subgroupOf M =
      (normalizer (k.action.plane 1 : Set G)).subgroupOf M := by
    rw [k.action.plane_normalizer_eq_comap, k.action.plane_normalizer_eq_comap,
      OrthogonalGeometry.setwise_plane_eq_ker, OrthogonalGeometry.setwise_plane_eq_ker]
  refine ⟨hs.1, ?_⟩
  exact (show (⟨s, hTM hs.1⟩ : M) ∈
    (normalizer (k.action.plane 1 : Set G)).subgroupOf M from
      he ▸ (show (⟨s, hTM hs.1⟩ : M) ∈
        (normalizer (k.action.plane i : Set G)).subgroupOf M from hi ▸ hs.2))

end CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource
