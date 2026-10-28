module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.LocalSetup
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Selection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Projection

/-!
# Actual residual coordinates and plane-point selection

The marked image of Y₊ is θ of the plane stabilizer, retaining its unipotent
radical. The point parabolic is a full preimage, so intersection commutes with
the marked image; finite residual transport then identifies the image of
O²(Y₊ ∩ P) with the two-residual of that model intersection. Coordinate
centrality is equivalent to ambient centrality by the actual conjugation action.

The two-group S ∩ L acts on the marked plane. Its action fixes zero, and the
plane has four elements, so there is a nonzero fixed point in that plane.
Projection also preserves centralization by S ∩ L through the exact central
supplement. These results do not establish noncentrality of the residual action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(6), 15.3.24, printed pp.1123–1124 and 1129–1130.
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers.Pure
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ProjectedAction
open Preparation
variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

/-- A full point preimage commutes with taking the marked image of an intersection. -/
theorem modelImage_point_intersection (h : NaturalDual d L) (B : Subgroup G) (x : Space 4) :
    modelImage (by decide) h.model (B ⊓ point h x) =
      modelImage (by decide) h.model B ⊓ pointStabilizer x := by
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl.1, rfl⟩, (mem_point h x l).mp hl.2⟩
  · rintro ⟨⟨l, hl, rfl⟩, hp⟩
    exact ⟨l, ⟨hl, (mem_point h x l).mpr hp⟩, rfl⟩

/-- The actual embedded two-residual maps to the embedded residual of the image. -/
theorem modelImage_residual [Finite G] (h : NaturalDual d L) {B : Subgroup G} (hBL : B ≤ L) :
    modelImage (by decide) h.model (Stellmacher.twoResidualAmbient B) =
      Stellmacher.twoResidualAmbient (modelImage (by decide) h.model B) := by
  let : Finite (LinearGroup 4) := Finite.of_surjective
    (linearAction (by decide) h.model) (linearAction_surjective (by decide) h.model)
  have hres : (Stellmacher.twoResidualAmbient B).subgroupOf L =
      (pResidual 2 (B.subgroupOf L)).map (B.subgroupOf L).subtype := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Stellmacher.twoResidualAmbient B ≤ L from
      (map_subtype_le _).trans hBL),
      map_embedded_pResidual, map_subgroupOf_eq_of_le hBL,
      ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  unfold modelImage
  rw [hres, map_embedded_pResidual,
    ComponentIntersection.twoResidualAmbient_eq_map_pResidual]

/-- The residual of Y₊ ∩ P has the full residual of the model intersection as image. -/
theorem modelImage_point_residual [Finite G] (h : NaturalDual d L) (x : Space 4) :
    modelImage (by decide) h.model (Stellmacher.twoResidualAmbient (d.Yplus ⊓ point h x)) =
      Stellmacher.twoResidualAmbient
        (modelImage (by decide) h.model d.Yplus ⊓ pointStabilizer x) := by
  rw [modelImage_residual h (inf_le_right.trans (point_le h x)),
    modelImage_point_intersection]

/-- The genuine local theta equality identifies Y₊ with the entire plane-theta image. -/
theorem modelImage_yplus [Finite G] {I : Subgroup G} (c : ComponentWitness d I)
    (h : NaturalDual d c.L) (plane : PlaneParabolic d c.L h.model)
    (hYL : d.Yplus ≤ c.L) (hθ : theta (d.MI I) = d.Yplus) :
    modelImage (by decide) h.model d.Yplus = theta (BinaryLinear.parabolic plane.plane) := by
  have hYML : d.Yplus ≤ d.M ⊓ c.L :=
    le_inf ((hθ ▸ theta_le (d.MI I)).trans inf_le_left) hYL
  have hY : d.Yplus = theta (d.M ⊓ c.L) := by
    apply le_antisymm
    · calc
        d.Yplus = theta d.Yplus := by rw [← hθ, theta_idempotent]
        _ ≤ theta (d.M ⊓ c.L) := theta_mono hYML
    · exact (theta_mono (inf_le_inf_left d.M (component_le c))).trans_eq hθ
  rw [hY, modelImage_theta _ _ inf_le_right, planeParabolic_image plane]

/-- Ambient commutation is exactly fixation of all coordinates by the actual image. -/
theorem commutator_eq_bot_iff_coordinates (h : NaturalDual d L) {A B : Subgroup G}
    (hAU : A ≤ spanCommutator d L) (hBL : B ≤ L) :
    ⁅A, B⁆ = ⊥ ↔ ∀ (u : spanCommutator d L), (u : G) ∈ A →
      ∀ g ∈ modelImage (by decide) h.model B,
        BinaryLinear.NaturalDualFlag.action g (h.coordinates u).toAdd = (h.coordinates u).toAdd := by
  constructor
  · intro hz u hu g hg
    obtain ⟨l, hl, rfl⟩ := hg
    have hc := (commutator_eq_bot_iff_le_centralizer.mp hz) hu l hl
    have he : commutatorAction d L l u = u := by
      apply Subtype.ext
      change (l : G) * u * (l : G)⁻¹ = (u : G)
      rw [hc, mul_inv_cancel_right]
    rw [← h.equivariant, he]
  · intro hh
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro u hu b hb
    let l : L := ⟨b, hBL hb⟩
    let v : spanCommutator d L := ⟨u, hAU hu⟩
    have he := hh v hu (linearAction (by decide) h.model l) ⟨l, hb, rfl⟩
    rw [← h.equivariant] at he
    have hv : commutatorAction d L l v = v :=
      h.coordinates.injective (congrArg Multiplicative.ofAdd he)
    have hc := congrArg Subtype.val hv
    change b * u * b⁻¹ = u at hc
    exact mul_inv_eq_iff_eq_mul.mp hc

theorem projectedCenter_centralizes_sylow
    [IsElementaryAbelian 2 (d.componentSpan L)]
    (hsplit : spanCommutator d L ⊔ d.Z = spanCommutator d L ⊔ centralSupplement d L) :
    ⁅projectedCenter d L, d.S ⊓ L⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mpr
  have hCZ : d.S ⊓ L ≤ L ⊓ centralizer (d.Z : Set G) :=
    le_inf inf_le_right ((inf_le_left.trans inf_le_left).trans
      (le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow d.T)))
  rw [← projectedCenter_centralizer d L hsplit] at hCZ
  exact hCZ.trans inf_le_right

/-- There is a nonzero point in the marked plane fixed by the actual S ∩ L. -/
theorem exists_plane_point (h : NaturalDual d L) (plane : PlaneParabolic d L h.model) :
    ∃ x : Space 4, x ∈ plane.plane ∧ x ≠ 0 ∧ d.S ⊓ L ≤ point h x := by
  let A := d.S ⊓ L
  let f : A →* LinearGroup 4 :=
    (linearAction (by decide) h.model).comp (inclusion (show A ≤ L from inf_le_right))
  have hf (a : A) : f a ∈ BinaryLinear.parabolic plane.plane := by
    have hm : (⟨a, a.property.2⟩ : L) ∈ (d.M ⊓ L).subgroupOf L :=
      ⟨d.sylow_le a.property.1.1, a.property.2⟩
    rw [plane.intersection] at hm
    exact hm
  let : MulAction A plane.plane := {
    smul a v := ⟨f a v, (hf a v).mpr v.property⟩
    one_smul v := Subtype.ext (by
      change f 1 v = v
      rw [map_one]; rfl)
    mul_smul a b v := Subtype.ext (by
      change f (a * b) v = f a (f b v)
      rw [map_mul]; rfl) }
  have hp : IsPGroup 2 A := d.T.isPGroup'.to_le (inf_le_left.trans inf_le_left)
  have hz : (0 : plane.plane) ∈ MulAction.fixedPoints A plane.plane := by
    intro a
    apply Subtype.ext
    exact (f a).map_zero
  have hcard : 2 ∣ Nat.card plane.plane := by
    let : Module.Finite (ZMod 2) plane.plane := Module.Finite.of_injective
      plane.plane.subtype Subtype.val_injective
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), plane.dimension]
    norm_num
  obtain ⟨v, hv, hv0⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point plane.plane hcard hz
  refine ⟨v, v.property, ?_, ?_⟩
  · intro he
    exact hv0 (Subtype.ext he.symm)
  · intro s hs
    apply (mem_point h (v : Space 4) ⟨s, hs.2⟩).mpr
    exact congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hv) ⟨s, hs⟩)

/-- The source residual acts through the two-residual of the marked plane-point intersection. -/
theorem modelImage_point_residual_plane [Finite G] {I : Subgroup G}
    (c : ComponentWitness d I) (h : NaturalDual d c.L)
    (plane : PlaneParabolic d c.L h.model)
    (hYL : d.Yplus ≤ c.L) (hθ : theta (d.MI I) = d.Yplus) (x : Space 4) :
    modelImage (by decide) h.model (Stellmacher.twoResidualAmbient (d.Yplus ⊓ point h x)) =
      Stellmacher.twoResidualAmbient
        (theta (BinaryLinear.parabolic plane.plane) ⊓ pointStabilizer x) := by
  rw [modelImage_point_residual, modelImage_yplus c h plane hYL hθ]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ProjectedAction

end
