module
public import Mathlib.Data.Set.Card
public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.Opposition

/-!
# The five point-sphere sizes of an octagon of order (2,4)

The local valences give row sum10 for the first distance matrix. Applying
row sums to the proved distance-matrix recurrences gives80,640,1024 for
the other distances. Thus the five sizes need no enumeration or additional
transitivity assumption. The binary Ree consumer retains literal point cosets.

Source: Aschbacher–Smith F.4.6 and J.5.5(2–3), printed p.446.
-/

public noncomputable section
namespace SimpleGraph.OctagonShortPaths.OrderTwoFourDatum
open SimpleGraph.OctagonOpposition
open scoped BigOperators
variable {V:Type*} [Fintype V] {G:SimpleGraph V} (D:OrderTwoFourDatum G)
attribute [local instance] Classical.propDecidable
local instance spherePointDecidableEq : DecidableEq D.Point := Classical.decEq _

private theorem row_one (u:D.Point) :
    (∑v, distanceMatrix D.pointDistance 1 u v)=10 := by
  simp only [distanceMatrix,D.pointDistance_eq_iff,Fin.val_one,mul_one]
  rw [D.point_sum_eq u (fun _=>1)]
  have h:=D.double_point_sum u u u.property u.property (fun _=>1)
  simpa only [dist_self,ite_true,mul_one] using h

private theorem row_mul (A B:Matrix D.Point D.Point ℤ) (r:ℤ)
    (hB:∀v,∑w,B v w=r) (u:D.Point) :
    (∑v,(A*B) u v)=(∑v,A u v)*r := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [←Finset.mul_sum,hB,Finset.sum_mul]

private theorem row_scalar (n:ℕ) (A:Matrix D.Point D.Point ℤ) (u:D.Point) :
    (∑v, ((n:Matrix D.Point D.Point ℤ)*A) u v)=n*(∑v,A u v) := by
  simp only [←nsmul_eq_mul,Matrix.smul_apply,←Finset.smul_sum]

private theorem row_nat (n:ℕ) (u:D.Point) :
    (∑v, (n:Matrix D.Point D.Point ℤ) u v)=n := by
  simp [Matrix.natCast_apply]

private theorem row_two (u:D.Point) :
    (∑v,distanceMatrix D.pointDistance 2 u v)=80 := by
  have h:=congrArg (fun A:Matrix D.Point D.Point ℤ=>∑v,A u v) D.recurrence.one
  rw [D.row_mul _ _ 10 D.row_one,D.row_one] at h
  simp only [Matrix.add_apply,Finset.sum_add_distrib] at h
  have hn:=D.row_nat 10 u
  norm_num only [Nat.cast_ofNat] at hn
  rw [hn,D.row_one] at h
  omega

private theorem row_three (u:D.Point) :
    (∑v,distanceMatrix D.pointDistance 3 u v)=640 := by
  have h:=congrArg (fun A:Matrix D.Point D.Point ℤ=>∑v,A u v) D.recurrence.two
  rw [D.row_mul _ _ 80 D.row_two,D.row_one] at h
  simp only [Matrix.add_apply,Finset.sum_add_distrib] at h
  have hn:=D.row_scalar 8 (distanceMatrix D.pointDistance 1) u
  norm_num only [Nat.cast_ofNat] at hn
  rw [hn,D.row_one,D.row_two] at h
  omega

private theorem row_four (u:D.Point) :
    (∑v,distanceMatrix D.pointDistance 4 u v)=1024 := by
  have h:=congrArg (fun A:Matrix D.Point D.Point ℤ=>∑v,A u v) D.recurrence.three
  rw [D.row_mul _ _ 640 D.row_three,D.row_one] at h
  simp only [Matrix.add_apply,Finset.sum_add_distrib] at h
  have h8:=D.row_scalar 8 (distanceMatrix D.pointDistance 2) u
  have h5:=D.row_scalar 5 (distanceMatrix D.pointDistance 4) u
  norm_num only [Nat.cast_ofNat] at h8 h5
  rw [h8,h5,D.row_two,D.row_three] at h
  omega

theorem point_sphere_card (u:D.Point) (i:Fin 5) :
    Nat.card {v:D.Point // D.pointDistance u v=i}=(![1,10,80,640,1024]:Fin 5→ℕ) i := by
  have he : (Nat.card {v:D.Point // D.pointDistance u v=i}:ℤ)=
      ∑v,distanceMatrix D.pointDistance i u v := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    simp [distanceMatrix,Finset.sum_boole]
  fin_cases i
  · have hz:{v:D.Point // D.pointDistance u v=0}≃({u}:Set D.Point):=
      Equiv.subtypeEquivRight (fun v=>by rw [D.pointDistance_zero]; exact eq_comm)
    change Nat.card {v:D.Point // D.pointDistance u v=0}=1
    rw [Nat.card_congr hz]; simp
  · change Nat.card {v:D.Point // D.pointDistance u v=1}=10
    change (Nat.card {v:D.Point // D.pointDistance u v=1}:ℤ)=
      ∑v,distanceMatrix D.pointDistance 1 u v at he
    rw [D.row_one] at he
    exact_mod_cast he
  · change Nat.card {v:D.Point // D.pointDistance u v=2}=80
    change (Nat.card {v:D.Point // D.pointDistance u v=2}:ℤ)=
      ∑v,distanceMatrix D.pointDistance 2 u v at he
    rw [D.row_two] at he
    exact_mod_cast he
  · change Nat.card {v:D.Point // D.pointDistance u v=3}=640
    change (Nat.card {v:D.Point // D.pointDistance u v=3}:ℤ)=
      ∑v,distanceMatrix D.pointDistance 3 u v at he
    rw [D.row_three] at he
    exact_mod_cast he
  · change Nat.card {v:D.Point // D.pointDistance u v=4}=1024
    change (Nat.card {v:D.Point // D.pointDistance u v=4}:ℤ)=
      ∑v,distanceMatrix D.pointDistance 4 u v at he
    rw [D.row_four] at he
    exact_mod_cast he

end SimpleGraph.OctagonShortPaths.OrderTwoFourDatum

namespace SimpleGraph.OctagonShortPaths
/-- The divisibility step selecting the opposite orbit in J.5.5. -/
theorem five_sphere_selection (T:Finset (Fin 5)) (h0:(0:Fin 5)∉T)
    (hp:0<∑i∈T,(![1,10,80,640,1024]:Fin 5→ℕ) i)
    (hd:256∣∑i∈T,(![1,10,80,640,1024]:Fin 5→ℕ) i) : T={4} := by
  have hc : ∀T:Finset (Fin 5),(0:Fin 5)∉T→
      0<∑i∈T,(![1,10,80,640,1024]:Fin 5→ℕ) i→
      256∣∑i∈T,(![1,10,80,640,1024]:Fin 5→ℕ) i→T={4} := by decide
  exact hc T h0 hp hd
end SimpleGraph.OctagonShortPaths
