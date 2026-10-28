module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Assembly.Marked
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.CartanFixed
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Movement by the original Cartan and symplectic plane residual

The original Cartan fixes only C_V(L). Once the preceding shadow theorem
makes that kernel trivial, coprime action gives [V,X]=V. For the literal
plane residual L₂, lift the block-diagonal SL₂ matrix [[0,1],[1,1]] through
the marked quotient. Its displacement is invertible on the full natural
four-space. The same original projection, now injective, lifts each vector
as a commutator, giving [V,L₂]=V.

These are the two movement inputs of the symplectic closure argument and
are applied in Assembly/Distance.lean. All conjugations use the single
published symplectic alignment; the actual solvable residual L₂ is retained.
No core equality or terminal closure conclusion is used, and q=4 is included.
Source: Aschbacher--Smith 11.5.7, printed pp.782--784, in particular its first
symplectic paragraph and final plane-normalizer step.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation Matrix
open scoped MatrixGroups commutatorElement
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} {E : Geometry D}

namespace Symplectic.MarkedFlag

/-- The actual Cartan moves the full seed when its preceding central kernel vanishes. -/
theorem cartan_commutator (m : Symplectic.MarkedFlag E) (hX : IsCartan T L E.X)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) : ⁅V,E.X⁆ = V := by
  let := D.elementary
  have hfix : V ⊓ centralizer (E.X : Set G) = ⊥ := by
    apply bot_unique
    rw [← hc]
    exact le_inf inf_le_left
      (Normalizers.PointCohomology.PointGeometry.sp4_cartan_fixed_le D E.input m.action hX)
  have hcop : Nat.Coprime (Nat.card E.X) (Nat.card V) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr hX.odd).pow_right n
  let := (IsElementaryAbelian.isPGroup 2 V).isNilpotent
  have he := eq_commutator_sup_centralizer_of_solvable_coprime V E.X
    ((hX.1.trans inf_le_left).trans D.normalizes) inferInstance hcop
  simpa only [hfix,sup_bot_eq] using he.symm

private def planeCubic {F : Type*} [Field F] [CharP F 2] : Sp F :=
  Plane.leviSp ⟨!![0,1;1,1], by simp [det_fin_two,CharTwo.neg_eq]⟩

private theorem planeCubic_mem {F : Type*} [Field F] [CharP F 2] :
    (planeCubic : Sp F) ∈ planeLocal :=
  (Plane.levi (F := F) ⟨!![0,1;1,1], by simp [det_fin_two,CharTwo.neg_eq]⟩).property

private theorem planeCubic_displacement {F : Type*} [Field F] [CharP F 2]
    (v : Vector F) : (planeCubic (F := F)) • ((planeCubic (F := F)) • v) -
      (planeCubic (F := F)) • v = v := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [planeCubic,Plane.leviSp,
      Matrix.mulVec,Matrix.mul_apply,dotProduct,
      Fintype.sum_sum_type,Fin.sum_univ_two,
      adjugate_fin_two,CharTwo.neg_eq,sub_eq_add_neg,add_assoc,
      CharTwo.add_self_eq_zero]
  all_goals
    first
    | exact CharTwo.add_cancel_left _ _
    | rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero]

/-- The original plane residual moves the entire seed, in the same marked coordinates. -/
theorem plane_commutator (m : Symplectic.MarkedFlag E)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) : ⁅V,E.L₂⁆ = V := by
  let s := (Sp4.alignment m.action)⁻¹
  let π := Symplectic.Terminal.markedProjection E m s
  let q := Symplectic.Terminal.RadicalGeometry.componentQuotient m
  let a : Sp E.input.field.Carrier := planeCubic
  obtain ⟨l,hl,hq⟩ := (show a ∈
      (E.L₂.subgroupOf L).map ((MulAut.conj s).toMonoidHom.comp q) from
        m.plane_local_image.symm ▸ planeCubic_mem)
  have hreal (x : V) :
      (π (V.normalizerMonoidHom (inclusion D.normalizes l) x)).toAdd =
        a • (π x).toAdd := by
    change s • (show Vector E.input.field.Carrier from
      ((Coordinates.sp4 m.action).projection
        (V.normalizerMonoidHom (inclusion D.normalizes l) x)).toAdd) = _
    rw [(Coordinates.sp4 m.action).projection_component_conjugation]
    change s • (q l • (show Vector E.input.field.Carrier from
      ((Coordinates.sp4 m.action).projection x).toAdd)) = _
    have hq' : s * q l * s⁻¹ = a := hq
    rw [← hq']
    change s • (q l • (show Vector E.input.field.Carrier from
      ((Coordinates.sp4 m.action).projection x).toAdd)) =
      (s * q l * s⁻¹) • (s • (show Vector E.input.field.Carrier from
        ((Coordinates.sp4 m.action).projection x).toAdd))
    simp only [mul_smul,inv_smul_smul]
  have hL₂ : E.L₂ ≤ L := (localResidual_le E.V₂).trans inf_le_left
  apply le_antisymm
    (le_normalizer_iff_commutator_le_left.mp (hL₂.trans D.normalizes))
  intro v hv
  let v' : V := ⟨v,hv⟩
  obtain ⟨x,hx⟩ := Symplectic.Terminal.markedProjection_surjective E m s
    (Multiplicative.ofAdd (a • (π v').toAdd))
  let y := V.normalizerMonoidHom (inclusion D.normalizes l) x * x⁻¹
  have hy : y = v' := by
    apply Symplectic.Terminal.markedProjection_injective E m s hc
    apply Multiplicative.toAdd.injective
    change (π (_ * x⁻¹)).toAdd = (π v').toAdd
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,
      ← sub_eq_add_neg]
    rw [hreal,hx]
    exact planeCubic_displacement _
  have hmem : (y : G) ∈ ⁅E.L₂,V⁆ := commutator_mem_commutator hl x.property
  rw [commutator_comm,hy] at hmem
  exact hmem

end Symplectic.MarkedFlag
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
