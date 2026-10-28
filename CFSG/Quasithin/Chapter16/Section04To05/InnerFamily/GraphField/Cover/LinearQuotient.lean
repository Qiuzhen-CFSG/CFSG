module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Actions
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Endgame
public import Theory.Representation.ElementaryAbelianAction
public import Theory.LinearAlgebra.SpecialLinearDeterminantKernel
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The linear quotient in the noncentral cover branch

The action in this file is the action of the *actual* overgroup
`N_T(E)Y = coverOvergroup T r z` on the actual residual
`D = residual L r`.  Its kernel is first identified with the relative
centralizer.  After the source calculation has supplied the reverse
centralizer inclusion, this becomes precisely `E`; no ambient normality is
used.

The residual is an elementary abelian group of order nine, so its full
automorphism group is canonically identified with `GL₂(3)`.  The source
noncentral action calculation is recorded in the weakest useful form: the
determinant kernel (the `SL₂(3)` image) lies in the action image, and one
image element has nontrivial determinant.  A short determinant argument then
proves surjectivity onto the actual `GL₂(3)`, and the quotient equivalence is
constructed from the action map and its exact kernel.

Thus this module does not assume a faithful quotient or a pre-existing
`GL₂(3)` identification.  The two model-action facts just described remain
the explicit source inputs consumed by the final graph-field assembly.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1191.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open Matrix

namespace CFSG.Quasithin.Chapter16.Intersections.GraphField

variable {G : Type*} [Group G] [Finite G]

local notation "CoverGL" => Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)

/-! ## The actual action and its coordinates -/

/-- Conjugation of the actual residual by the actual cover overgroup.

The containment hypothesis is deliberately explicit: it is the source
normalization statement needed before an action on `D` can be formed. -/
def coverResidualAction (T : Sylow 2 G) (r z : G) (D : Subgroup G)
    (hD : coverOvergroup T r z ≤ normalizer (D : Set G)) :
    coverOvergroup T r z →* MulAut D :=
  D.normalizerMonoidHom.comp (inclusion hD)

omit [Finite G] in
/-- The kernel of the actual residual action is the relative centralizer. -/
theorem coverResidualAction_kernel (T : Sylow 2 G) (r z : G) (D : Subgroup G)
    (hD : coverOvergroup T r z ≤ normalizer (D : Set G)) :
    (coverResidualAction T r z D hD).ker =
      (centralizer (D : Set G)).subgroupOf (coverOvergroup T r z) := by
  ext x
  change D.normalizerMonoidHom (inclusion hD x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  rfl

omit [Finite G] in
/-- The linear automorphism model of an elementary abelian group of order nine. -/
noncomputable def coverResidualAutomorphismEquiv (D : Subgroup G)
    (hD : IsElementaryAbelian 3 D) (h9 : Nat.card D = 9) :
    MulAut D ≃* CoverGL := by
  letI : IsElementaryAbelian 3 D := hD
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : CommGroup D := IsMulCommutative.instCommGroup
  have hpow : 3 ^ Module.finrank (ZMod 3) (Additive D) = 3 ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive D)
    change Nat.card D = _ at hsize
    simpa only [Nat.card_zmod, h9, show (9 : ℕ) = 3 ^ 2 by decide] using hsize.symm
  have hdim : Module.finrank (ZMod 3) (Additive D) = 2 :=
    Nat.pow_right_injective (by decide : 1 < 3) hpow
  let autLinear : MulAut D ≃* ((Additive D) ≃ₗ[ZMod 3] (Additive D)) :=
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let b : Module.Basis (Fin 2) (ZMod 3) (Additive D) :=
    Module.finBasisOfFinrankEq (ZMod 3) (Additive D) hdim
  exact autLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Additive D)).symm.trans
      (Matrix.GeneralLinearGroup.toLin' b).symm)

/-- The actual action written in the concrete matrix coordinates. -/
noncomputable def coverMatrixAction (T : Sylow 2 G) (r z : G) (D : Subgroup G)
    (hD : IsElementaryAbelian 3 D) (h9 : Nat.card D = 9)
    (hDN : coverOvergroup T r z ≤ normalizer (D : Set G)) :
    coverOvergroup T r z →* CoverGL :=
  (coverResidualAutomorphismEquiv D hD h9).toMonoidHom.comp
    (coverResidualAction T r z D hDN)

/-- Passing to matrix coordinates does not change the action kernel. -/
theorem coverMatrixAction_kernel_eq
    (T : Sylow 2 G) (r z : G) (D : Subgroup G)
    (hD : IsElementaryAbelian 3 D) (h9 : Nat.card D = 9)
    (hDN : coverOvergroup T r z ≤ normalizer (D : Set G))
    {K : Subgroup (coverOvergroup T r z)}
    (hK : (coverResidualAction T r z D hDN).ker = K) :
    (coverMatrixAction T r z D hD h9 hDN).ker = K := by
  let e := coverResidualAutomorphismEquiv D hD h9
  let a := coverResidualAction T r z D hDN
  let f := coverMatrixAction T r z D hD h9 hDN
  ext x
  change f x = 1 ↔ x ∈ K
  constructor
  · intro hx
    change e (a x) = 1 at hx
    have he : e (a x) = e 1 := hx.trans (map_one e).symm
    have hax : a x = 1 := e.injective he
    have hxA : x ∈ a.ker := MonoidHom.mem_ker.mpr hax
    exact hK ▸ hxA
  · intro hx
    have hax : a x = 1 := MonoidHom.mem_ker.mp (hK ▸ hx)
    change e (a x) = 1
    simp only [hax, map_one]

/-! ## The `SL₂(3)` image alternative and full surjectivity -/

private theorem units_eq_of_ne_one {u v : (ZMod 3)ˣ}
    (hu : u ≠ 1) (hv : v ≠ 1) : u = v := by
  decide +revert

private theorem cover_matrix_range_eq_top_of_determinant
    {A : Type*} [Group A] (f : A →* CoverGL)
    (hSL : (Matrix.GeneralLinearGroup.det : CoverGL →* (ZMod 3)ˣ).ker ≤ f.range)
    (hdet : ∃ a ∈ f.range,
      Matrix.GeneralLinearGroup.det a ≠ 1) :
    f.range = ⊤ := by
  obtain ⟨a, ha, ha1⟩ := hdet
  apply top_unique
  intro x _hx
  by_cases hx1 : Matrix.GeneralLinearGroup.det x = 1
  · apply hSL
    exact MonoidHom.mem_ker.mpr hx1
  · have hdet_eq : Matrix.GeneralLinearGroup.det x =
        Matrix.GeneralLinearGroup.det a := by
      exact units_eq_of_ne_one hx1 ha1
    have hxa : x * a⁻¹ ∈
        (Matrix.GeneralLinearGroup.det : CoverGL →* (ZMod 3)ˣ).ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, hdet_eq, mul_inv_cancel]
    have hxa' : x * a⁻¹ ∈ f.range := hSL hxa
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using f.range.mul_mem hxa' ha

/-- The quotient by the exact residual-action kernel is the actual matrix
quotient.  The `hSL` premise is precisely the restricted `SL₂(3)` image
alternative; `hdet` supplies the one determinant-nontrivial actor from the
two-local part of the source argument. -/
theorem coverGeneralLinear_of_matrix_action
    (T : Sylow 2 G) (r z : G) (D : Subgroup G)
    (hD : IsElementaryAbelian 3 D) (h9 : Nat.card D = 9)
    (hDN : coverOvergroup T r z ≤ normalizer (D : Set G))
    {K : Subgroup (coverOvergroup T r z)}
    (hK : (coverResidualAction T r z D hDN).ker = K)
    (hSL : (Matrix.GeneralLinearGroup.det : CoverGL →* (ZMod 3)ˣ).ker ≤
      (coverMatrixAction T r z D hD h9 hDN).range)
    (hdet : ∃ a ∈ (coverMatrixAction T r z D hD h9 hDN).range,
      Matrix.GeneralLinearGroup.det a ≠ 1)
    (hKE : K = (fourGroup r z).subgroupOf (coverOvergroup T r z)) :
    CoverGeneralLinear T r z := by
  let M := coverOvergroup T r z
  let f := coverMatrixAction T r z D hD h9 hDN
  have hfK : f.ker = K := coverMatrixAction_kernel_eq T r z D hD h9 hDN hK
  have hfTop : f.range = ⊤ := cover_matrix_range_eq_top_of_determinant f hSL hdet
  let _ : K.Normal := hfK ▸ inferInstance
  have hquot : (M ⧸ K) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hfK.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  have htop : f.range ≃* CoverGL :=
    (MulEquiv.subgroupCongr hfTop).trans Subgroup.topEquiv
  have hquotE : (M ⧸ (fourGroup r z).subgroupOf M) ≃* CoverGL := by
    have hKE' : K = (fourGroup r z).subgroupOf M := by simpa [M] using hKE
    exact (QuotientGroup.quotientMulEquivOfEq hKE'.symm).trans (hquot.trans htop)
  exact ⟨hquotE⟩

/-- The noncentral branch of the source action calculation.  The hypothesis
`hdet_of_noncentral` is the exact determinant-nontrivial conclusion of that
calculation; the theorem itself performs the `SL₂(3)`-to-`GL₂(3)` passage and
the quotient construction. -/
theorem coverGeneralLinear_of_noncentralizing
    (T : Sylow 2 G) (r z : G) (D : Subgroup G)
    (hD : IsElementaryAbelian 3 D) (h9 : Nat.card D = 9)
    (hDN : coverOvergroup T r z ≤ normalizer (D : Set G))
    (hnc : ¬ coverY T r z ≤ centralizer (D : Set G))
    {K : Subgroup (coverOvergroup T r z)}
    (hK : (coverResidualAction T r z D hDN).ker = K)
    (hSL : (Matrix.GeneralLinearGroup.det : CoverGL →* (ZMod 3)ˣ).ker ≤
      (coverMatrixAction T r z D hD h9 hDN).range)
    (hdet_of_noncentral : ¬ coverY T r z ≤ centralizer (D : Set G) →
      ∃ a ∈ (coverMatrixAction T r z D hD h9 hDN).range,
        Matrix.GeneralLinearGroup.det a ≠ 1)
    (hKE : K = (fourGroup r z).subgroupOf (coverOvergroup T r z)) :
    CoverGeneralLinear T r z := by
  exact coverGeneralLinear_of_matrix_action T r z D hD h9 hDN hK hSL
    (hdet_of_noncentral hnc) hKE

/-! ## Exact kernel from the source centralizer calculation -/

omit [Finite G] in
/-- The marked four-group acts trivially on the actual residual. -/
theorem fourGroup_subgroupOf_le_coverResidualAction_kernel
    (T : Sylow 2 G) (r z : G) (D : Subgroup G)
    (hDN : coverOvergroup T r z ≤ normalizer (D : Set G))
    (hDcentral : D ≤ centralizer (fourGroup r z : Set G)) :
    (fourGroup r z).subgroupOf (coverOvergroup T r z) ≤
      (coverResidualAction T r z D hDN).ker := by
  rw [coverResidualAction_kernel]
  intro e he
  have heE : (e : G) ∈ fourGroup r z := mem_subgroupOf.mp he
  apply mem_centralizer_iff.mpr
  intro d hd
  exact (mem_centralizer_iff.mp (hDcentral hd) (e : G) heE).symm

omit [Finite G] in
/-- The exact kernel follows once the source proves that the relative
centralizer has no element beyond `E`. -/
theorem coverResidualAction_kernel_eq_fourGroup
    (T : Sylow 2 G) (r z : G) (D : Subgroup G)
    (hDN : coverOvergroup T r z ≤ normalizer (D : Set G))
    (hDcentral : D ≤ centralizer (fourGroup r z : Set G))
    (hC : (centralizer (D : Set G)).subgroupOf (coverOvergroup T r z) ≤
      (fourGroup r z).subgroupOf (coverOvergroup T r z)) :
    (coverResidualAction T r z D hDN).ker =
      (fourGroup r z).subgroupOf (coverOvergroup T r z) := by
  apply le_antisymm
  · rw [coverResidualAction_kernel]
    exact hC
  · exact fourGroup_subgroupOf_le_coverResidualAction_kernel T r z D hDN hDcentral

variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- In the source setup the residual `D = Lᵣ` centralizes the marked
four-group, so the marked subgroup acts trivially on `D` under the actual
cover action. -/
theorem residual_fourGroup_subgroupOf_le_coverResidualAction_kernel
    (h : IntersectionSetup T z L g R) (_hr : r ∈ R)
    (hDN : coverOvergroup T r z ≤ normalizer (residual L r : Set G)) :
    (fourGroup r z).subgroupOf (coverOvergroup T r z) ≤
      (coverResidualAction T r z (residual L r) hDN).ker := by
  exact fourGroup_subgroupOf_le_coverResidualAction_kernel T r z (residual L r) hDN
    (residual_le_fourGroup_centralizer h)

end CFSG.Quasithin.Chapter16.Intersections.GraphField
