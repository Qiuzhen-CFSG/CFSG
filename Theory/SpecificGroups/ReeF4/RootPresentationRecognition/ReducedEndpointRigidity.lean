module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularSuzukiLast
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularLinearCommute

/-!
# Rigidity of the reduced last-root coefficient

The native last-root equation supplies the parameter-one candidate. Any other
candidate differs from it by one linear/central factor. Conjugation by the
simple Suzuki element turns that factor into a single linear root. Preserving
one adjacent-root commutation then forces its parameter to vanish by the
short mixed equation and native chart injectivity.

Source: the endpoint comparison of Fong--Seitz II (1974), Section 10,
(10.27)--(10.41), with the native triangular Suzuki convention.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup ReeF4
namespace ReeF4.RootPresentationRecognition.ReducedEndpointRigidity
open CentralCovers.TwoPrimary ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
variable (m : ℕ)
local notation "L" i:max a:max => (PositiveTables.pair m i a : Model m)
local notation "S" i:max a:max b:max => (PositiveTables.quartet m i a b : Model m)

private theorem pq_adjacent (i j : Fin 4)
    (h : (rootIndex (.inl i)).val + 1 = (rootIndex (.inr j)).val)
    (a b c : CoefficientField m) : Commute (L i a) (S j b c) :=
  AngularAdjacent.native_adjacent_commute m _ _ h
    (PositiveTables.rootChartEquiv m (.inl i) a)
    (PositiveTables.rootChartEquiv m (.inr j) (b,c))

private theorem qp_adjacent (i j : Fin 4)
    (h : (rootIndex (.inr i)).val + 1 = (rootIndex (.inl j)).val)
    (a b c : CoefficientField m) : Commute (S i a b) (L j c) :=
  AngularAdjacent.native_adjacent_commute m _ _ h
    (PositiveTables.rootChartEquiv m (.inr i) (a,b))
    (PositiveTables.rootChartEquiv m (.inl j) c)

private theorem pair_mul (i : Fin 4) (a b : CoefficientField m) :
    L i a * L i b = L i (a+b) := by
  rw [←Subgroup.coe_mul,PositiveTables.pair_mul]

private theorem quartet_mul (i : Fin 4) (a b d e : CoefficientField m) :
    S i a b * S i d e = S i (a+d) (b+e+titsEnd m a*d) := by
  rw [←Subgroup.coe_mul,PositiveTables.quartet_mul]

private def tail (α : CoefficientField m) : Model m :=
  S 2 1 1 * L 2 1 * S 1 0 1 * L 3 α * S 3 1 (1+α) * L 1 1

private theorem tail_factor (α : CoefficientField m) :
    tail m α = tail m 1 * (L 3 (α+1) * S 3 0 (α+1)) := by
  have hc := (AngularLinearCommute.linear_commute_family m 1 (α+1)).1
  have hd := pq_adjacent m 1 3 (by simp [rootIndex,positive_pair_indices,positive_quartet_indices]) 1 0 (α+1)
  have he := qp_adjacent m 3 3 (by simp [rootIndex,positive_pair_indices,positive_quartet_indices]) 1 0 (α+1)
  unfold tail
  simp only [CharTwo.add_self_eq_zero]
  symm
  calc
    _ = S 2 1 1 * L 2 1 * S 1 0 1 *
        (L 3 1 * L 3 (α+1)) * (S 3 1 0 * S 3 0 (α+1)) * L 1 1 := by
      simp only [mul_assoc]
      rw [hc.left_comm,hd.eq,he.left_comm]
    _ = _ := by
      rw [pair_mul,quartet_mul]
      simp only [add_zero,zero_add,map_one,mul_zero]
      rw [show 1+(α+1)=α by rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero],
        add_comm α 1]

private theorem tail_one :
    L 0 1 * tail m 1 = (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 := by
  have h := AngularSuzukiLast.main_right_coordinates m 1 1
  simp only [mul_one,map_one,one_pow] at h
  have hK : tail m 1 = (L 0 1)⁻¹ * (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 := by
    simpa only [tail,CharTwo.add_self_eq_zero] using h.symm
  rw [hK]
  group

private theorem perturbation_conjugate (δ : CoefficientField m) :
    S 0 1 0 * (L 3 δ * S 3 0 δ) * (S 0 1 0)⁻¹ = L 3 δ := by
  have h1 := AngularCoefficients.short_conjugate m 1 0 δ
  have h2 := AngularSuzukiNear.near_conjugate m 1 0 0 δ
  simp only [one_mul] at h1
  simp only [mul_zero,PositiveTables.pair_zero,Subgroup.coe_one,one_mul] at h2
  calc
    _ = (S 0 1 0 * L 3 δ * (S 0 1 0)⁻¹) *
      (S 0 1 0 * S 3 0 δ * (S 0 1 0)⁻¹) := by group
    _ = S 3 0 δ * L 3 δ * S 3 0 δ := by rw [h1,h2]
    _ = (S 3 0 δ * S 3 0 δ) * L 3 δ := by
      rw [mul_assoc,(qp_adjacent m 3 3
        (by simp [rootIndex,positive_pair_indices,positive_quartet_indices]) 0 δ δ).symm.eq,
        ←mul_assoc]
    _ = L 3 δ := by
      rw [←Subgroup.coe_mul,PositiveTables.quartet_mul]
      simp only [map_zero,zero_mul,CharTwo.add_self_eq_zero,
        PositiveTables.quartet_zero,Subgroup.coe_one,one_mul]

private theorem linear_parameter_zero (δ : CoefficientField m)
    (h : Commute (L 3 δ) (S 2 1 0)) : δ = 0 := by
  have he := AngularCoefficients.short_reflected_conjugate m 1 0 δ
  rw [h.eq,mul_inv_cancel_right,one_mul] at he
  have hs : S 1 0 δ = 1 := mul_right_cancel (he.symm.trans (one_mul _).symm)
  have hh : PositiveTables.rootChartEquiv m (.inr 1) (0,δ) =
      PositiveTables.rootChartEquiv m (.inr 1) (0,0) := by
    apply Subtype.ext
    change S 1 0 δ = S 1 0 0
    simpa only [PositiveTables.quartet_zero,Subgroup.coe_one] using hs
  exact congrArg Prod.snd ((PositiveTables.rootChartEquiv m (.inr 1)).injective hh)

/-- A single preserved root commutation forces the reduced endpoint parameter. -/
theorem reduced_endpoint_eq_one (α : CoefficientField m)
    (h : Commute
      (L 0 1 * (S 2 1 1 * L 2 1 * S 1 0 1 * L 3 α * S 3 1 (1+α) * L 1 1))
      ((S 0 1 0)⁻¹ * S 2 1 0 * S 0 1 0)) : α = 1 := by
  let u := S 0 1 0
  let A := u⁻¹ * L 0 1 * u
  let B := u⁻¹ * S 2 1 0 * u
  let D := L 3 (α+1) * S 3 0 (α+1)
  have hAB : Commute A B := by
    have hc := (qp_adjacent m 2 0 (by simp [rootIndex,positive_pair_indices,positive_quartet_indices]) 1 0 1).symm
    exact hc.map (MulAut.conj u⁻¹).toMonoidHom
  have hAD : Commute (A*D) B := by
    change Commute (L 0 1 * tail m α) B at h
    rw [tail_factor,←mul_assoc,tail_one] at h
    exact h
  have hDB : Commute D B := by
    change D*B = B*D
    apply mul_left_cancel (a := A)
    calc
      A*(D*B) = (A*D)*B := (mul_assoc _ _ _).symm
      _ = B*(A*D) := hAD.eq
      _ = A*(B*D) := by rw [←mul_assoc,hAB.symm.eq,mul_assoc]
  have hLD : Commute (L 3 (α+1)) (S 2 1 0) := by
    have hc := hDB.map (MulAut.conj u).toMonoidHom
    change Commute (u*D*u⁻¹) (u*B*u⁻¹) at hc
    have hb : u*B*u⁻¹ = S 2 1 0 := by dsimp [B]; group
    rw [hb] at hc
    exact (perturbation_conjugate m (α+1)) ▸ hc
  have hz := linear_parameter_zero m (α+1) hLD
  simpa only [CharTwo.neg_eq] using eq_neg_iff_add_eq_zero.mpr hz

end ReeF4.RootPresentationRecognition.ReducedEndpointRigidity
