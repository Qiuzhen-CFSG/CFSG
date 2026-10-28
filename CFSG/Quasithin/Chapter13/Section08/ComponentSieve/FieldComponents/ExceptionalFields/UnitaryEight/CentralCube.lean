module
public import Theory.SpecificGroups.SU3.UnitaryEight.CentralCube
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight.Borel
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The scalar center fixes every Borel-invariant binary plane

Sylow conjugacy places an order-nine element in the two-residual of the
specified SU₃(8) Borel, with its cube generating the actual scalar center.
Its permutation action on four vectors has order dividing both nine and
24, so the cube fixes the plane pointwise. This calculation applies to any
representation and does not require a natural-module identification.
The original source application propagates this fixation through the seed
orbit and uses the faithful quotient action.
Source: Aschbacher–Smith 13.8.20, printed pp.954–955.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source.Unitary
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight

theorem sylow_borel_central_cube {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1; 0,1,0; 1,0,0])
    (hcard : Nat.card E = 64) (hfixed : Nat.card {x : E // J.conj x = x} = 8)
    (P : Sylow 2 J.specialSubgroup) :
    ∃ t : J.specialSubgroup,
      t ∈ (pResidual 2 (normalizer (P : Set J.specialSubgroup))).map
        (normalizer (P : Set J.specialSubgroup)).subtype ∧
      orderOf t = 9 ∧ zpowers (t^3) = center J.specialSubgroup := by
  obtain ⟨u,hu,huo,huz⟩ := HermitianForm.UnitaryEightSeed.torus_central_cube J hJ hcard hfixed
  obtain ⟨_, _, P₀, hR, _, _, _, hN, _⟩ := standard_su_borel_data J 3 (by decide)
    (by simpa using hcard)
    (huppert_II_10_4_conj_eq_frobenius J 8 (by simpa using hcard) hfixed) hJ
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq J.specialSubgroup P₀ P
  have hm : (P₀ : Subgroup J.specialSubgroup).map (MulAut.conj c).toMonoidHom = P :=
    congrArg Sylow.toSubgroup hc
  have hn := Subgroup.map_equiv_normalizer_eq (P₀ : Subgroup J.specialSubgroup) (MulAut.conj c)
  rw [hm] at hn
  have ht : (hermitianTorusSU J hJ).range ≤ normalizer (P₀ : Set J.specialSubgroup) := by
    change suTorus J hJ ≤ normalizer ((P₀ : Subgroup J.specialSubgroup) : Set _)
    rw [hR,hN]
    exact le_sup_right
  let t := MulAut.conj c u
  have htN : t ∈ normalizer (P : Set J.specialSubgroup) := hn ▸ ⟨u,ht hu,rfl⟩
  have hto : orderOf t = 9 := ((MulAut.conj c).orderOf_eq u).trans huo
  refine ⟨t,⟨⟨t,htN⟩,mem_pResidual_of_orderOf_coprime ?_,rfl⟩,hto,?_⟩
  · rw [Subgroup.orderOf_mk,hto]; decide
  · have he : t^3 = u^3 := by
      rw [show t = MulAut.conj c u from rfl,←map_pow]
      change c * u^3 * c⁻¹ = u^3
      have hz : u^3 ∈ center J.specialSubgroup := huz ▸ mem_zpowers _
      rw [mem_center_iff.mp hz c,mul_inv_cancel_right]
    rw [he,huz]
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight

namespace Representation.BinaryOffender
variable {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
private theorem cube_fixes_four_space (ρ : Representation (ZMod 2) D U)
    (W : Submodule (ZMod 2) U) (hw : Nat.card W = 4)
    (t : D) (ht : t ∈ subspaceStabilizer ρ W) (ht9 : t^9 = 1) :
    ∀ v ∈ W, ρ (t^3) v = v := by
  let : Finite W := Nat.finite_of_card_ne_zero (by omega)
  let σ := stabilizerRepresentation ρ W
  let f : subspaceStabilizer ρ W →* Equiv.Perm W := {
    toFun := fun g => (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W
      (σ.asGroupHom g)).toEquiv
    map_one' := by ext v; simp [σ,stabilizerRepresentation]
    map_mul' := by intro a b; ext v; change ρ (a.val*b.val) v.val = ρ a.val (ρ b.val v.val); simp only [map_mul,Module.End.mul_apply] }
  let a : subspaceStabilizer ρ W := ⟨t,ht⟩
  have ha : a^9 = 1 := Subtype.ext ht9
  have ho : orderOf (f a) ∣ 9 := orderOf_dvd_of_pow_eq_one (by rw [←map_pow,ha,map_one])
  have hc : orderOf (f a) ∣ 24 := by simpa only [Nat.card_perm,hw,show Nat.factorial 4 = 24 from rfl] using orderOf_dvd_natCard (f a)
  have he : (f a)^3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_gcd ho hc)
  intro v hv
  have hh := congrArg (fun p : Equiv.Perm W => (p ⟨v,hv⟩).val) he
  rw [←map_pow] at hh
  exact hh
end Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight
open Representation Representation.BinaryOffender
variable {E U : Type*} [Field E] [Finite E] [AddCommGroup U] [Module (ZMod 2) U]

/-- The actual SU₃(8) center fixes any four-element subspace invariant under
 the two-residual of a Sylow normalizer, for every binary representation. -/
theorem center_fixes_four_space (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1; 0,1,0; 1,0,0])
    (hcard : Nat.card E = 64) (hfixed : Nat.card {x : E // J.conj x = x} = 8)
    (P : Sylow 2 J.specialSubgroup)
    (ρ : Representation (ZMod 2) J.specialSubgroup U)
    (W : Submodule (ZMod 2) U) (hW : Nat.card W = 4)
    (hs : (pResidual 2 (normalizer (P : Set J.specialSubgroup))).map
      (normalizer (P : Set J.specialSubgroup)).subtype ≤ subspaceStabilizer ρ W) :
    W ≤ fixedSpace ρ (center J.specialSubgroup) := by
  obtain ⟨t,ht,hto,htz⟩ := sylow_borel_central_cube J hJ hcard hfixed P
  rw [←htz]
  intro v hv
  rw [mem_fixedSpace_zpowers_iff]
  exact cube_fixes_four_space ρ W hW t (hs ht)
    (by simpa only [hto] using pow_orderOf_eq_one t) v hv
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight
