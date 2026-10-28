module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Bounds
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Mathlib.LinearAlgebra.Projection
/-!
# The numerical dimension-five dual conclusion of B.4.9

An invariant complement gives explicit equivariant coordinates on the original
module as the marked natural module plus its dual. Pulling back the radical at
an actual three-space gives an elementary subgroup of order 64 with fixed
codimension five. Thus splitting supplies the strict-offender witness, rather
than assuming one. The elementary-rank bound and the two-factor budget then
force the exact global quadratic ratio 5/6. The lower bound needs no splitting.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9(2)(iv),
printed pp.94–95. Constructing the quadratic four-group that forces splitting
is a separate geometric obligation.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
open QuasisimpleSource BinaryLinear.OuterCyclic
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)

private noncomputable def splitPair (C : Subrepresentation ρ)
    (hC : IsCompl d.space.toSubmodule C.toSubmodule) :
    (d.space.toRepresentation.prod C.toRepresentation).Equiv ρ :=
  .mk (Submodule.prodEquivOfIsCompl _ _ hC) (by
    intro g
    apply LinearMap.ext
    intro v
    exact (map_add (ρ g) v.1.val v.2.val).symm)

private noncomputable def complementQuotient (C : Subrepresentation ρ)
    (hC : IsCompl d.space.toSubmodule C.toSubmodule) :
    C.toRepresentation.Equiv d.space.quotientRepresentation :=
  .mk (Submodule.quotientEquivOfIsCompl _ _ hC).symm (by
    intro g
    apply LinearMap.ext
    intro v
    rfl)

private theorem dual_intertwines (g : G)
    (φ : Module.Dual (ZMod 2) d.space.toSubmodule) :
    (coordinates d hF).linearEquiv.symm.dualMap (d.space.toRepresentation.dual g φ) =
      (groupEquiv d hF g).symm.dualMap
        ((coordinates d hF).linearEquiv.symm.dualMap φ) := by
  apply LinearMap.ext
  intro x
  change φ (d.space.toRepresentation g⁻¹ ((coordinates d hF).linearEquiv.symm x)) =
    φ ((coordinates d hF).linearEquiv.symm ((groupEquiv d hF g).symm x))
  congr 1
  apply (coordinates d hF).linearEquiv.injective
  rw [intertwines, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [map_inv]
  rfl

/-- Coordinates on the original split extension, compatible with the fixed
actor marking and the specified identification of its actual quotient. -/
noncomputable def splitCoordinates
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    (C : Subrepresentation ρ) (hC : IsCompl d.space.toSubmodule C.toSubmodule) :
    V ≃ₗ[ZMod 2] BinaryNaturalDual.CoordinateSpace 5 :=
  (splitPair d C hC).symm.toLinearEquiv.trans
    ((coordinates d hF).linearEquiv.prodCongr
      (((complementQuotient d C hC).trans e).toLinearEquiv.trans
        (coordinates d hF).linearEquiv.symm.dualMap))

/-- The two module coordinates use the same marked group isomorphism. -/
theorem splitCoordinates_intertwines
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    (C : Subrepresentation ρ) (hC : IsCompl d.space.toSubmodule C.toSubmodule)
    (g : G) (v : V) :
    splitCoordinates d hF e C hC (ρ g v) =
      BinaryNaturalDual.naturalDualRepresentation (groupEquiv d hF g)
        (splitCoordinates d hF e C hC v) := by
  let s := (splitPair d C hC).symm
  have hs := LinearMap.congr_fun (s.isIntertwining' g) v
  change s (ρ g v) = (d.space.toRepresentation g (s v).1,
    C.toRepresentation g (s v).2) at hs
  change ((coordinates d hF).linearEquiv (s (ρ g v)).1,
    (coordinates d hF).linearEquiv.symm.dualMap
      (((complementQuotient d C hC).trans e) (s (ρ g v)).2)) = _
  rw [hs, BinaryNaturalDual.naturalDualRepresentation_apply]
  apply Prod.ext
  · exact intertwines d hF g (s v).1
  · change (coordinates d hF).linearEquiv.symm.dualMap
      (((complementQuotient d C hC).trans e) (C.toRepresentation g (s v).2)) = _
    have hc := LinearMap.congr_fun
      (((complementQuotient d C hC).trans e).isIntertwining' g) (s v).2
    exact (congrArg (coordinates d hF).linearEquiv.symm.dualMap hc).trans
      (dual_intertwines d hF g _)

private theorem radical_strong :
    IsStrongOffender (BinaryNaturalDual.naturalDualRepresentation
      (V := Space 5)) (BinaryLinear.radical BinaryNaturalDual.FiveActors.U₀) := by
  let W := BinaryNaturalDual.FiveActors.U₀
  have hdim : Module.finrank (ZMod 2) W = 3 := BinaryNaturalDual.FiveActors.finrank_U₀
  have hbot : W ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hdim
    omega
  have htop : W ≠ ⊤ := by
    intro he
    rw [he, finrank_top] at hdim
    norm_num [Space] at hdim
  have hc : Nat.card (BinaryLinear.radical W) = 64 :=
    BinaryNaturalDual.FiveActors.card_radical W (by simp) hdim
  have hne : BinaryLinear.radical W ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hc
    omega
  have hr : rank (BinaryLinear.radical W) = 6 := by norm_num [rank, hc]
  have hfix : fixedSpace BinaryNaturalDual.naturalDualRepresentation
      (BinaryLinear.radical W) = W.prod W.dualAnnihilator := by
    simpa only [fixedSpace_comp_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using
      BinaryNaturalDual.fixedSpace_radical W hbot htop
  have hd := fixedCodim_add_finrank (BinaryNaturalDual.naturalDualRepresentation
    (V := Space 5)) (BinaryLinear.radical W)
  rw [hfix, BinaryNaturalDual.finrank_prod_dualAnnihilator] at hd
  have hspace : Module.finrank (ZMod 2) (BinaryNaturalDual.Space (Space 5)) = 10 := by
    simp [BinaryNaturalDual.Space, Module.finrank_prod, Subspace.dual_finrank_eq, Space]
  rw [hspace, show Module.finrank (ZMod 2) (Space 5) = 5 by simp [Space]] at hd
  have hcost : fixedCodim (BinaryNaturalDual.naturalDualRepresentation
      (V := Space 5)) (BinaryLinear.radical W) = 5 := by omega
  exact ⟨⟨hne, inferInstance⟩, by
    change fixedCodim (BinaryNaturalDual.naturalDualRepresentation
      (V := Space 5)) (BinaryLinear.radical W) < rank (BinaryLinear.radical W)
    rw [hcost, hr]
    decide⟩

include hF in
/-- An actual radical, transported back to the original group, is a strict
 offender once the extension splits. Its literal matrix image is retained. -/
theorem strong_radical_of_splits
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    (hsplit : d.Splits) : ∃ A : Subgroup G,
      A.map (groupEquiv d hF).toMonoidHom =
        BinaryLinear.radical BinaryNaturalDual.FiveActors.U₀ ∧
      IsStrongOffender ρ A := by
  obtain ⟨C, hC⟩ := hsplit
  let f := groupEquiv d hF
  let R := BinaryLinear.radical BinaryNaturalDual.FiveActors.U₀
  let A := R.map f.symm.toMonoidHom
  have hR := radical_strong
  have he : A.map f.toMonoidHom = R := by
    simp [A, Subgroup.map_map]
  have hA : IsElementaryTwo A := by
    refine ⟨?_, IsElementaryAbelian.map f.symm.toMonoidHom⟩
    intro hbot
    have hb : R = ⊥ := by rw [← he, hbot, Subgroup.map_bot]
    exact hR.1.1 hb
  refine ⟨A, he, hA, ?_⟩
  rw [fixedCodim_map_equivariant ρ BinaryNaturalDual.naturalDualRepresentation
    f.toMonoidHom (splitCoordinates d hF e C hC)
    (splitCoordinates_intertwines d hF e C hC), he]
  have hr := rank_map_injective f.toMonoidHom f.injective A
  rw [he] at hr
  rw [← hr]
  exact hR.2


include hF in
/-- Splitting discharges the strict-FF premise of the ratio calculation. -/
theorem strong_of_splits
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    (hsplit : d.Splits) : IsStrongFFModule ρ := by
  obtain ⟨A, _, hA⟩ := strong_radical_of_splits d hF e hsplit
  exact ⟨A, hA⟩

open scoped ENNReal
variable [FiniteDimensional (ZMod 2) V]
include hF in
/-- The lower ratio bound holds even before the extension is split. -/
theorem dual_ratio_lower_bound
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual) :
    (5 : ℝ≥0∞) / 6 ≤ quadraticRatio ρ := by
  let : Finite G := Finite.of_injective (groupEquiv d hF) (groupEquiv d hF).injective
  refine le_iInf fun A => le_iInf fun hA => ?_
  by_cases hs : IsStrongOffender ρ A
  · obtain ⟨hr, hc, _⟩ := dual_strong_costs d hF e hs
    simp only [actionRatio, hr, hc, Nat.cast_ofNat, le_refl]
  · have hge : 1 ≤ actionRatio ρ A := by
      apply le_of_not_gt
      intro hlt
      exact hs ⟨hA.1, (actionRatio_lt_one_iff ρ hA.1).mp hlt⟩
    exact (by rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]; norm_num : (5 : ℝ≥0∞) / 6 ≤ 1).trans hge

include hF in
/-- Once splitting is proved, no further rank or strict-offender premise
is needed for the numerical conclusion of B.4.9(2)(iv). -/
theorem dual_ratio_of_splits
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    (hsplit : d.Splits) : quadraticRatio ρ = 5 / 6 := by
  let : Finite G := Finite.of_injective (groupEquiv d hF) (groupEquiv d hF).injective
  exact d.dual_ratio_of_rank_bound e (fun A hA => rank_le_six d hF hA)
    (strong_of_splits d hF e hsplit)

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
