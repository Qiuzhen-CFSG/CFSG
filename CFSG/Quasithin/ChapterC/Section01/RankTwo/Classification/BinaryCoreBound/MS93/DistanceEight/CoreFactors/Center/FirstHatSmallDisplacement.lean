module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.CommutatorRows
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Small core displacement on the first hat layer

The full commutator rows map the actual core onto Hom(first dual,H).
Evaluation at any nonzero first-dual vector is onto H, which has order four.
Consequently an element of the first hat whose commutators with the core
lie in a subgroup of order at most two must lie in the original Z-layer.

The subgroup form is the terminal layer step in the no-new-center argument
for a quotient of the original large binary core by its first fixed line.
It uses the literal core and marked first-hat quotient; no equality of the
whole component-fixed factor with H, or action of the original ambient
two-core on that factor, is required.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(ii),(iv), printed
pp.898--899; Aschbacher--Smith 15.3.31, printed p.1132.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
open Higher DistanceFour.Linear

private theorem evaluation_onto {E : Type*} [Group E] [IsElementaryAbelian 2 E]
    (v : W) (hv : v ≠ 0) :
    Function.Surjective (fun f : Multiplicative W →* E => f (Multiplicative.ofAdd v)) := by
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hv
  intro e
  let l : W →ₗ[ZMod 2] Additive E := f.smulRight (Additive.ofMul e)
  refine ⟨(Representation.BinaryThreeHom.homEquivLinear (T := E)).symm (Multiplicative.ofAdd l), ?_⟩
  change (f v • Additive.ofMul e).toMul = e
  rw [hf,one_smul]
  rfl

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- A first-hat element with core displacement of order at most two lies in Z. -/
theorem first_hat_mem_Z_of_small_core_displacement
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Early.SourcePath R (alpha R))
    (A : Subgroup (FreeAmalgam R)) (hAK : A ≤ core R (alpha R))
    (hcard : Nat.card A ≤ 2)
    {x : FreeAmalgam R} (hx : x ∈ hatV R (alpha R) (p.walk.getVert 6))
    (hdisp : ∀ y ∈ core R (alpha R), ⁅x,y⁆ ∈ A) : x ∈ Z R (alpha R) := by
  let := H_elementary_of_central R (alpha R)
    (geometry.V_local _ rfl common.large_distance) (earlier.centrality _ rfl)
  obtain ⟨s⟩ := Quotients.FirstDirect.markedDualSection common earlier p
  let x' : hatV R (alpha R) (p.walk.getVert 6) := ⟨x,hx⟩
  by_contra hxZ
  have hxne : (s.quotient x').toAdd ≠ 0 := by
    intro he
    have hk : x' ∈ s.quotient.ker := MonoidHom.mem_ker.mpr
      (Multiplicative.toAdd.injective he)
    rw [s.kernel] at hk
    exact hxZ hk
  have hHA : H R (alpha R) ≤ A := by
    intro h hh
    obtain ⟨f,hf⟩ := evaluation_onto (s.quotient x').toAdd hxne (⟨h,hh⟩ : H R (alpha R))
    obtain ⟨y,hy⟩ := coreCommutatorRow_surjective common earlier p s f
    have he : ⁅(y : FreeAmalgam R),x⁆ = h := by
      rw [← coreCommutatorRow_apply common earlier p s y x',hy]
      exact congrArg Subtype.val hf
    rw [← he,← commutatorElement_inv]
    exact A.inv_mem (hdisp y y.property)
  let : Finite (core R (alpha R)) := DistanceTwo.finite_core (alpha R)
  let : Finite A := Finite.of_injective (inclusion hAK) (inclusion_injective hAK)
  have hlo := Early.First.Layer.H_card_lower common earlier (alpha R) rfl
  have hhi := card_le_of_le hHA
  omega

/-- Apply the pointwise row obstruction to an actual first-hat subgroup. -/
theorem first_hat_small_core_displacement_le_Z
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Early.SourcePath R (alpha R))
    (D A : Subgroup (FreeAmalgam R))
    (hD : D ≤ hatV R (alpha R) (p.walk.getVert 6))
    (hAK : A ≤ core R (alpha R)) (hcard : Nat.card A ≤ 2)
    (hdisp : ⁅D,core R (alpha R)⁆ ≤ A) : D ≤ Z R (alpha R) := by
  intro x hx
  exact first_hat_mem_Z_of_small_core_displacement common earlier p A hAK hcard
    (hD hx) (fun y hy => hdisp (commutator_mem_commutator hx hy))
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
