module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.SeedGeneration
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Action
public import Theory.GroupTheory.SylowSeedCentralizer

/-!
# The literal moved-seed centralizer

Sylow averaging gives C_X(U∩ZS) = C_X(ZS), where
U = [⟨ZS^X⟩,X]. Passing through X → X/O₂(X) therefore identifies the
image of the original M₁ with the pointwise kernel of its actual additive
seed. No abstractly isomorphic replacement of M₁ is used.

Source: Aschbacher--Smith, 15.2.23, printed p.1116, using B.2.14.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 PlaneUniquenessPreceding
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The centralizer of the original moved seed is exactly M₁. -/
theorem U_seed_centralizer
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) :
    X ⊓ centralizer ((U X ZS ⊓ ZS : Subgroup G) : Set G) = M1 X ZS := by
  let S := planeSylow T ZS
  have hSI : S ≤ I :=
    (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  let := d.plane_span_elementary hI hfit hXI
  obtain ⟨P,hP⟩ := (show Chapter1.IsSylowIn 2 S I from d.sylow_in_escape hI).restrict
    (show S ≤ X ⊔ S from le_sup_right) (sup_le hXI hSI)
  exact centralizer_moved_omegaCenter_eq X S ZS d.omega_center
    (hSI.trans hn)
    ((d.plane_span_le_planeParabolicCore hI hfit hXI).trans
      (d.planeParabolicCore_le_plane hI)) P hP

/-- The original centralizer maps onto the seed fixer in X/O₂(X). -/
theorem M1_image_eq_seedKernel
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) :
    letI := U_elementary d hI hfit hXI
    let σ := U_representation d hI hfit hXI hn
    let Z := AddSubgroup.toZModSubmodule 2 (ZS.subgroupOf (U X ZS)).toAddSubgroup
    ((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) =
      subspaceKernel σ Z ⊤ := by
  let := U_elementary d hI hfit hXI
  dsimp only
  let q := QuotientGroup.mk' (pCore 2 X)
  ext a
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) a
  constructor
  · rintro ⟨y,hy,he⟩
    rw [← he]
    refine ⟨mem_top _, ?_⟩
    intro u hu
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [U_representation_apply]
    have hh : (u.toMul : G) * (y : G) = (y : G) * (u.toMul : G) := hy.2 _ hu
    rw [← hh, mul_inv_cancel_right]
  · intro ha
    refine ⟨x, ?_, rfl⟩
    change (x : G) ∈ M1 X ZS
    rw [← U_seed_centralizer d hI hfit hXI hn]
    refine ⟨x.property, ?_⟩
    intro u hu
    let v : Additive (U X ZS) := Additive.ofMul ⟨u,hu.1⟩
    have he := congrArg (fun w : Additive (U X ZS) => (w.toMul : G)) (ha.2 v hu.2)
    rw [U_representation_apply] at he
    change (x : G) * u * (x : G)⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
