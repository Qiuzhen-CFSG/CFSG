module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.ReducedEndpointRigidity
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.EndpointCoordinateReduction
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularSuzukiOppositeTable
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularNextTransforms
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularShortCompletion

/-!
# Native endpoint coefficient rigidity

Reflection first determines three endpoint coordinates by collecting the word
in the native triangular Suzuki charts. The involution relation fixes the
remaining central sum, and one adjacent-root commutation removes the final
linear perturbation through `ReducedEndpointRigidity`.

Source: Fong--Seitz II (1974), Section 10, (10.27)--(10.41).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup ReeF4
namespace ReeF4.RootPresentationRecognition.EndpointCoefficientRigidity
open CentralCovers.TwoPrimary ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
variable (m : ℕ)
local notation "L" i:max a:max => (PositiveTables.pair m i a : Model m)
local notation "S" i:max a:max b:max => (PositiveTables.quartet m i a b : Model m)

private theorem quartet_coe (i : Fin 4) (a b : CoefficientField m) :
    (PositiveTables.rootChartEquiv m (.inr i) (a,b) : Model m) = S i a b := rfl

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


private theorem pair_inv (i : Fin 4) (a : CoefficientField m) : (L i a)⁻¹ = L i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [pair_mul]
  simp only [CharTwo.add_self_eq_zero,PositiveTables.pair_zero,Subgroup.coe_one]

private theorem quartet_inv (i : Fin 4) (a b : CoefficientField m) :
    (S i a b)⁻¹ = S i a (b+titsEnd m a*a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [quartet_mul]
  have h : b+(b+titsEnd m a*a)+titsEnd m a*a=0 := by
    rw [←add_assoc b b,CharTwo.add_self_eq_zero,zero_add,CharTwo.add_self_eq_zero]
  simp only [h,CharTwo.add_self_eq_zero,PositiveTables.quartet_zero,Subgroup.coe_one]

private theorem move_left {G : Type*} [Group G] {x y z : G}
    (h : y⁻¹*x*y=z) : x*y=y*z := by rw [←h]; group

private theorem swap65 (y z a : CoefficientField m) :
    S 2 y z * L 2 a = L 2 a * S 2 y z :=
  (pq_adjacent m 2 2 (by simp [rootIndex,positive_pair_indices,positive_quartet_indices]) a y z).symm.eq

private theorem swap54 (y a b : CoefficientField m) :
    L 2 y * S 1 a b = S 1 a b * L 2 y :=
  (qp_adjacent m 1 2 (by simp [rootIndex,positive_pair_indices,positive_quartet_indices]) a b y).symm.eq

private theorem swap43 (y z a : CoefficientField m) :
    S 1 y z * L 3 a = L 3 a * S 1 y z :=
  (pq_adjacent m 3 1 (by simp [rootIndex,positive_pair_indices,positive_quartet_indices]) a y z).symm.eq

private theorem swap62 (y z a b : CoefficientField m) :
    S 2 y z * S 3 a b = S 3 a b * S 2 y z :=
  (AngularSuzukiCommute.suzuki_commute_family m a b y z).2.symm.eq

private theorem swap32 (y a b : CoefficientField m) :
    L 3 y * S 3 a b = S 3 a b * L 3 y :=
  (qp_adjacent m 3 3 (by simp [rootIndex,positive_pair_indices,positive_quartet_indices]) a b y).symm.eq

private theorem swap31 (y a : CoefficientField m) :
    L 3 y * L 1 a = L 1 a * L 3 y :=
  (AngularLinearCommute.linear_commute_family m a y).1.symm.eq

private theorem swap21 (y z a : CoefficientField m) :
    S 3 y z * L 1 a = L 1 a * S 3 y z :=
  (pq_adjacent m 1 3 (by simp [rootIndex,positive_pair_indices,positive_quartet_indices]) a y z).symm.eq

private theorem swap40 (y z a b : CoefficientField m) :
    S 1 y z * S 0 a b = S 0 a b * S 1 y z :=
  (AngularSuzukiCommute.suzuki_commute_family m a b y z).1.symm.eq

private theorem swap10 (y a b : CoefficientField m) :
    L 1 y * S 0 a b = S 0 a b * L 1 y :=
  (qp_adjacent m 0 1 (by simp [rootIndex,positive_pair_indices,positive_quartet_indices]) a b y).symm.eq

private theorem swap64 (y z a b : CoefficientField m) :
    S 2 y z * S 1 a b = S 1 a b * (L 2 (a*y)*S 2 y z) := by
  apply move_left
  have h := AngularSuzukiNear.near_terminal_conjugate m a (b+titsEnd m a*a) y z
  simpa only [←quartet_inv,inv_inv] using h

private theorem swap42 (y z a b : CoefficientField m) :
    S 1 y z * S 3 a b = S 3 a b * (L 3 (a*y)*S 1 y z) := by
  apply move_left
  have h := AngularSuzukiNear.near_middle_conjugate m a (b+titsEnd m a*a) y z
  simpa only [←quartet_inv,inv_inv] using h

private theorem swap20 (y z a b : CoefficientField m) :
    S 3 y z * S 0 a b = S 0 a b * (L 1 (a*y)*S 3 y z) := by
  apply move_left
  have h := AngularSuzukiNear.near_conjugate m a (b+titsEnd m a*a) y z
  simpa only [←quartet_inv,inv_inv] using h

private theorem swap30 (y a b : CoefficientField m) :
    L 3 y * S 0 a b = S 0 a b*(S 3 0 (a*y)*L 3 y) :=
  move_left (AngularCoefficients.short_inverse_conjugate m a b y)

private theorem swap63 (y z a : CoefficientField m) :
    S 2 y z * L 3 a = L 3 a*(S 1 0 (y*a)*S 2 y z) := by
  apply move_left
  rw [pair_inv]
  simpa only [pair_inv] using AngularCoefficients.short_reflected_conjugate m y z a

private theorem swap41 (y z a : CoefficientField m) :
    S 1 y z * L 1 a = L 1 a*(S 3 0 (y*a)*S 1 y z) := by
  apply move_left
  rw [pair_inv]
  simpa only [pair_inv] using AngularCoefficients.short_perpendicular_conjugate m y z a

private theorem swap61 (y z a : CoefficientField m) :
    S 2 y z * L 1 a = L 1 a*(S 3 0 (y*titsEnd m a)*L 3 (titsEnd m y*a)*
      S 1 0 ((z+titsEnd m y*y)*a)*S 2 y z) := by
  apply move_left
  rw [pair_inv]
  simpa only [pair_inv] using AngularNextTransforms.next_reflected_conjugate m y z a

private theorem swap60 :
    S 2 1 0 * S 0 1 0 = S 0 1 0*(S 3 1 0*S 1 1 1*L 2 1*S 2 1 0) := by
  apply move_left
  simpa only [map_one,one_mul,mul_one,quartet_inv,zero_add] using
    AngularSuzukiOppositeTable.main_inverse_conjugate m 1 1

private theorem swap53 (y a : CoefficientField m) :
    L 2 y * L 3 a = L 3 a * L 2 y :=
  (AngularLinearCommute.linear_commute_family m a y).2.2.1.symm.eq

private theorem swap51 (y a : CoefficientField m) :
    L 2 y * L 1 a = L 1 a * L 2 y :=
  (AngularLinearCommute.linear_commute_family m a y).2.1.symm.eq

private theorem swap52 (y a b : CoefficientField m) :
    L 2 y * S 3 a b = S 3 a b*(S 1 0 (a*y)*L 2 y) := by
  apply move_left
  have h := AngularCoefficients.short_shifted_conjugate m a (b+titsEnd m a*a) y
  simpa only [←quartet_inv,inv_inv] using h

private theorem field_two : (2 : CoefficientField m) = 0 := CharP.cast_eq_zero _ 2
private theorem field_three : (3 : CoefficientField m) = 1 := by
  calc (3 : CoefficientField m) = 2+1 := by norm_num
       _ = 1 := by rw [field_two,zero_add]

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem collect_middle (e t v w : CoefficientField m) :
    S 2 1 0 * L 2 1 * S 1 1 (1+w) * L 3 v * S 3 e (t+((titsEnd m e)*e)) =
      S 3 e (t+((titsEnd m e)*e)) * L 3 (e+v) * S 1 1 (1+v+w) * S 2 1 0 := by
  simp only [mul_assoc]
  rw [←mul_assoc (S 2 _ _) (L 2 _) _,swap65]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 2 _ _) (S 1 _ _) _,swap64]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 2 _) (S 1 _ _) _,swap54]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 2 _) (L 2 _) _,pair_mul m 2]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 2 _ _) (L 3 _) _,swap63]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (L 3 _) _,swap43]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (S 1 _ _) _,quartet_mul m 1]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [swap62]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (S 3 _ _) _,swap42]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 3 _) (S 3 _ _) _,swap32]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 3 _) (L 3 _) _,pair_mul m 3]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  all_goals try ring_nf
  all_goals try simp only [field_two,field_three,mul_zero,zero_mul,zero_add,add_zero]

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem collect_suffix (d e t v w : CoefficientField m) :
    S 3 e (t+((titsEnd m e)*e)) * L 3 (e+v) * S 1 1 (1+v+w) * S 2 1 0 * L 1 d =
      L 1 d * S 3 e ((titsEnd m d)+d+t+((titsEnd m e)*e)) * L 3 (d+e+v) * S 1 1 (1+d+v+w) * S 2 1 0 := by
  simp only [mul_assoc]
  rw [swap61]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (L 1 _) _,swap41]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 3 _) (L 1 _) _,swap31]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 3 _ _) (L 1 _) _,swap21]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 3 _) (S 3 _ _) _,swap32]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 3 _ _) (S 3 _ _) _,quartet_mul m 3]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (S 3 _ _) _,swap42]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 3 _) (S 3 _ _) _,swap32]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 3 _ _) (S 3 _ _) _,quartet_mul m 3]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (L 3 _) _,swap43]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 3 _) (L 3 _) _,pair_mul m 3]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (S 1 _ _) _,quartet_mul m 1]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  all_goals try ring_nf
  all_goals try simp only [field_two,field_three,mul_zero,zero_mul,zero_add,add_zero]

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem collect_first (d e t v w : CoefficientField m) :
    L 1 d * S 3 e ((titsEnd m d)+d+t+((titsEnd m e)*e)) * L 3 (d+e+v) * S 1 1 (1+d+v+w) * S 2 1 0 * S 0 1 0 =
      S 0 1 0 * L 1 (d+e) * S 3 (1+e) ((titsEnd m d)+(titsEnd m e)+e+t+v+((titsEnd m e)*e)) * L 3 (1+d+e+v) * S 1 0 (1+d+v+w) * L 2 1 * S 2 1 0 := by
  simp only [mul_assoc]
  rw [swap60]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (S 0 _ _) _,swap40]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 3 _) (S 0 _ _) _,swap30]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 3 _ _) (S 0 _ _) _,swap20]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 1 _) (S 0 _ _) _,swap10]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 1 _) (L 1 _) _,pair_mul m 1]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 3 _ _) (S 3 _ _) _,quartet_mul m 3]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (S 3 _ _) _,swap42]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 3 _) (S 3 _ _) _,swap32]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 3 _ _) (S 3 _ _) _,quartet_mul m 3]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 3 _) (L 3 _) _,pair_mul m 3]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (S 1 _ _) _,quartet_mul m 1]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  all_goals try ring_nf
  all_goals try simp only [field_two,field_three,mul_zero,zero_mul,zero_add,add_zero]

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem square_first (t v : CoefficientField m) :
    S 2 1 1 * L 2 1 * S 1 0 t * L 3 v =
      L 3 v * S 1 0 (t+v) * L 2 1 * S 2 1 1 := by
  simp only [mul_assoc]
  rw [←mul_assoc (S 2 _ _) (L 2 _) _,swap65]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 2 _ _) (S 1 _ _) _,swap64]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 2 _) (S 1 _ _) _,swap54]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [swap63]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 2 _) (L 3 _) _,swap53]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (L 3 _) _,swap43]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 2 _) (S 1 _ _) _,swap54]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (S 1 _ _) _,quartet_mul m 1]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  all_goals try ring_nf
  all_goals try simp only [field_two,field_three,mul_zero,zero_mul,zero_add,add_zero]

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem square_center (t v w : CoefficientField m) :
    L 3 v * S 1 0 (t+v) * L 2 1 * S 2 1 1 * S 2 0 1 * L 2 1 * S 1 0 (1+w) =
      L 3 v * S 1 0 (1+t+v+w) * S 2 1 0 := by
  simp only [mul_assoc]
  rw [←mul_assoc (S 2 _ _) (S 2 _ _) _,quartet_mul m 2]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 2 _ _) (L 2 _) _,swap65]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 2 _) (L 2 _) _,pair_mul m 2]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [swap64]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (S 1 _ _) _,quartet_mul m 1]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  all_goals try ring_nf
  all_goals try simp only [field_two,field_three,mul_zero,zero_mul,zero_add,add_zero]

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem square_next (t v w : CoefficientField m) :
    L 3 v * S 1 0 (1+t+v+w) * S 2 1 0 * S 3 1 w * L 2 1 * L 3 1 =
      S 3 1 w * L 3 (1+v) * S 1 0 (t+v+w) * L 2 1 * S 2 1 0 := by
  simp only [mul_assoc]
  rw [←mul_assoc (S 2 _ _) (S 3 _ _) _,swap62]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (S 3 _ _) _,swap42]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 3 _) (S 3 _ _) _,swap32]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 2 _ _) (L 2 _) _,swap65]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [swap63]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 2 _) (L 3 _) _,swap53]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (L 3 _) _,swap43]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 3 _) (L 3 _) _,pair_mul m 3]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 2 _) (S 1 _ _) _,swap54]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (S 1 _ _) _,quartet_mul m 1]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  all_goals try ring_nf
  all_goals try simp only [field_two,field_three,mul_zero,zero_mul,zero_add,add_zero]

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem square_last (t v w : CoefficientField m) :
    S 3 1 w * L 3 (1+v) * S 1 0 (t+v+w) * L 2 1 * S 2 1 0 * L 1 1 =
      L 1 1 * S 3 1 (1+w) * L 3 v * S 1 0 (1+t+v+w) * L 2 1 * S 2 1 0 := by
  simp only [mul_assoc]
  rw [swap61]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 2 _) (L 1 _) _,swap51]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (L 1 _) _,swap41]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 3 _) (L 1 _) _,swap31]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 3 _ _) (L 1 _) _,swap21]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 2 _) (S 3 _ _) _,swap52]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (S 3 _ _) _,swap42]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 3 _) (S 3 _ _) _,swap32]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 3 _ _) (S 3 _ _) _,quartet_mul m 3]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 2 _) (L 3 _) _,swap53]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (L 3 _) _,swap43]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 3 _) (L 3 _) _,pair_mul m 3]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (L 2 _) (S 1 _ _) _,swap54]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  rw [←mul_assoc (S 1 _ _) (S 1 _ _) _,quartet_mul m 1]
  all_goals try simp only [map_add,map_mul,map_pow,map_zero,map_one,titsEnd_twice,
    mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,PositiveTables.quartet_zero,Subgroup.coe_one,mul_assoc]
  all_goals try ring_nf
  all_goals try simp only [field_two,field_three,mul_zero,zero_mul,zero_add,add_zero]

private theorem reflected_collect (d e t v w : CoefficientField m) :
    S 2 1 0 * L 2 1 * S 1 1 (w+1) * L 3 v * S 3 e (t+titsEnd m e*e) * L 1 d * S 0 1 0 =
      S 0 1 0 * L 1 (d+e) * S 3 (e+1) (titsEnd m d+titsEnd m e*e+titsEnd m e+e+t+v) *
        L 3 (d+e+v+1) * S 1 0 (d+v+w+1) * L 2 1 * S 2 1 0 := by
  rw [add_comm w 1,collect_middle,collect_suffix,collect_first]
  ring_nf

local notation "K" s:max e:max t:max v:max w:max =>
  S 2 1 1 * L 2 s * S 1 e t * L 3 v * S 3 1 w * L 1 1

private theorem reflection_reduction (s e t v w : CoefficientField m)
    (h : S 2 1 0 * L 2 1 * S 1 1 (w+1) * L 3 v *
      S 3 e (t+titsEnd m e*e) * L 1 s =
        S 0 1 0 * (K s e t v w)⁻¹ * (S 0 1 0)⁻¹) :
    s=1 ∧ e=0 ∧ t=v+w := by
  have hp := congrArg (fun z => z * S 0 1 0) h
  simp only [mul_assoc,inv_mul_cancel,mul_one] at hp
  simp only [mul_inv_rev,pair_inv,quartet_inv,map_one,one_mul,
    CharTwo.add_self_eq_zero] at hp
  have hc : S 0 1 0 * L 1 1 * S 3 1 (w+1) * L 3 v *
      S 1 e (t+titsEnd m e*e) * L 2 s * S 2 1 0 =
    S 0 1 0 * L 1 (s+e) * S 3 (e+1) (titsEnd m s+titsEnd m e*e+titsEnd m e+e+t+v) *
      L 3 (s+e+v+1) * S 1 0 (s+v+w+1) * L 2 1 * S 2 1 0 := by
    calc
      _ = S 2 1 0 * L 2 1 * S 1 1 (w+1) * L 3 v *
          S 3 e (t+titsEnd m e*e) * L 1 s * S 0 1 0 := by
        simpa only [mul_assoc] using hp.symm
      _ = _ := reflected_collect m s e t v w
  exact EndpointCoordinateReduction.collected_endpoint_coefficients m s e t v w hc

private theorem square_collect (t v w : CoefficientField m) :
    S 2 1 1 * L 2 1 * S 1 0 t * L 3 v * S 2 0 1 * L 2 1 *
      S 1 0 (w+1) * S 3 1 w * L 2 1 * L 3 1 * L 1 1 =
    L 1 1 * S 3 1 (w+1) * L 3 v * S 1 0 (t+v+w+1) * L 2 1 * S 2 1 0 := by
  rw [square_first,add_comm w 1,square_center,square_next,square_last]
  ring_nf

private theorem reverse_conjugate {G : Type*} [Group G] {a b z : G}
    (h : a*b*a⁻¹=z*b) : b*a*b⁻¹=z⁻¹*a := by
  calc
    _ = z⁻¹*(z*b)*a*b⁻¹ := by group
    _ = z⁻¹*(a*b*a⁻¹)*a*b⁻¹ := by rw [h]
    _ = _ := by group

private theorem commute_of_conjugate {G : Type*} [Group G] {a b : G}
    (h : a*b*a⁻¹=b) : Commute a b := by
  change a*b=b*a
  have hh := congrArg (fun z => z*a) h
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

private theorem last_action (t v w : CoefficientField m) :
    L 0 1 * (K 1 0 t v w) * L 0 1 =
    L 1 1 * S 3 1 (w+1) * L 3 v * S 1 0 (t+v+w+1) * L 2 1 * S 2 1 0 := by
  let f := MulAut.conj (L 0 1)
  have h2 : f (S 2 1 1)=S 2 1 1 := by
    change L 0 1 * S 2 1 1 * (L 0 1)⁻¹ = S 2 1 1
    rw [(qp_adjacent m 2 0 (by simp [rootIndex,positive_pair_indices,positive_quartet_indices]) 1 1 1).symm.eq,
      mul_inv_cancel_right]
  have h5 : f (L 2 1)=L 2 1 := by
    change L 0 1 * L 2 1 * (L 0 1)⁻¹ = L 2 1
    rw [(AngularLinearCommute.linear_commute_family m 1 1).2.2.2.2.symm.eq,mul_inv_cancel_right]
  have h4 : f (S 1 0 t)=S 1 0 t := by
    have hh := AngularShortCompletion.short_terminal_conjugate m 0 t 1
    simp only [zero_mul,PositiveTables.quartet_zero,Subgroup.coe_one,one_mul] at hh
    have hc := commute_of_conjugate hh
    change L 0 1 * S 1 0 t * (L 0 1)⁻¹ = S 1 0 t
    rw [hc.symm.eq,mul_inv_cancel_right]
  have h3 : f (L 3 v)=L 3 v := by
    change L 0 1 * L 3 v * (L 0 1)⁻¹ = L 3 v
    rw [(AngularLinearCommute.linear_commute_family m v 1).2.2.2.1.symm.eq,mul_inv_cancel_right]
  have h6 : f (S 3 1 w)=S 2 0 1 * L 2 1 * S 1 0 (w+1) * S 3 1 w := by
    have hh := AngularNextTransforms.next_shifted_conjugate m 1 w 1
    simp only [map_one,mul_one] at hh
    simpa only [f,MulAut.conj_apply,mul_inv_rev,quartet_inv,pair_inv,
      map_zero,zero_mul,add_zero,mul_assoc] using reverse_conjugate hh
  have h1 : f (L 1 1)=L 2 1 * L 3 1 * L 1 1 := by
    have hh := AngularNextTransforms.last_linear_conjugate m 1 1
    simp only [map_one,mul_one] at hh
    simpa only [f,MulAut.conj_apply,mul_inv_rev,pair_inv,mul_assoc] using reverse_conjugate hh
  calc
    _ = f (K 1 0 t v w) := by simp only [f,MulAut.conj_apply,pair_inv]
    _ = S 2 1 1 * L 2 1 * S 1 0 t * L 3 v *
        (S 2 0 1 * L 2 1 * S 1 0 (w+1) * S 3 1 w) * (L 2 1 * L 3 1 * L 1 1) := by
      simp only [map_mul,h2,h5,h4,h3,h6,h1]
    _ = _ := by simpa only [mul_assoc] using square_collect m t v w

private theorem square_reduction (t v w : CoefficientField m)
    (h : (L 0 1 * (K 1 0 t v w))^2=1) : v+w=1 := by
  have hi : L 0 1 * (K 1 0 t v w) * L 0 1 = (K 1 0 t v w)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    simpa only [pow_two,mul_assoc] using h
  have he := (last_action m t v w).symm.trans hi
  simp only [mul_inv_rev,pair_inv,quartet_inv,map_one,map_zero,one_mul,zero_mul,
    add_zero,CharTwo.add_self_eq_zero] at he
  simp only [←mul_assoc] at he
  have h₁ : L 1 1 * S 3 1 (w+1) * L 3 v * S 1 0 (t+v+w+1) * L 2 1 =
      L 1 1 * S 3 1 (w+1) * L 3 v * S 1 0 t * L 2 1 := by
    exact mul_right_cancel he
  have h₂ : L 1 1 * S 3 1 (w+1) * L 3 v * S 1 0 (t+v+w+1) =
      L 1 1 * S 3 1 (w+1) * L 3 v * S 1 0 t := by
    exact mul_right_cancel h₁
  have hq : S 1 0 (t+v+w+1) = S 1 0 t := by
    exact mul_left_cancel h₂
  have hc : PositiveTables.rootChartEquiv m (.inr 1) (0,t+v+w+1) =
      PositiveTables.rootChartEquiv m (.inr 1) (0,t) := by
    apply Subtype.ext
    simpa only [quartet_coe m 1 0 (t+v+w+1),quartet_coe m 1 0 t] using hq
  have hv := congrArg Prod.snd ((PositiveTables.rootChartEquiv m (.inr 1)).injective hc)
  have hz : (v+w)+1=0 := add_left_cancel (show t+((v+w)+1)=t+0 by
    simpa only [add_assoc,add_zero] using hv)
  simpa only [CharTwo.neg_eq] using eq_neg_iff_add_eq_zero.mpr hz

/-- Reflection, involution, and one adjacent-root commutation fix the endpoint word. -/
theorem endpoint_coefficients (s e t v w : CoefficientField m)
    (hreflect : S 2 1 0 * L 2 1 * S 1 1 (w+1) * L 3 v *
      S 3 e (t+titsEnd m e*e) * L 1 s =
        S 0 1 0 * (K s e t v w)⁻¹ * (S 0 1 0)⁻¹)
    (hsquare : (L 0 1 * (K s e t v w))^2=1)
    (hcomm : Commute (L 0 1 * (K s e t v w))
      ((S 0 1 0)⁻¹ * S 2 1 0 * S 0 1 0)) :
    s=1 ∧ e=0 ∧ t=1 ∧ v=1 ∧ w=0 := by
  obtain ⟨hs,he,ht⟩ := reflection_reduction m s e t v w hreflect
  have hsquare' : (L 0 1 * (K 1 0 t v w))^2=1 := by
    simpa only [hs,he] using hsquare
  have hvw := square_reduction m t v w hsquare'
  have ht1 := ht.trans hvw
  have hw : w=1+v := by
    calc
      w = 0+w := by rw [zero_add]
      _ = (v+v)+w := by rw [CharTwo.add_self_eq_zero]
      _ = v+(v+w) := by rw [add_assoc]
      _ = v+1 := by rw [hvw]
      _ = 1+v := add_comm v 1
  have hcomm' : Commute (L 0 1 * (K 1 0 1 v (1+v)))
      ((S 0 1 0)⁻¹ * S 2 1 0 * S 0 1 0) := by
    simpa only [hs,he,ht1,hw] using hcomm
  have hv := ReducedEndpointRigidity.reduced_endpoint_eq_one m v hcomm'
  refine ⟨hs,he,ht1,hv,?_⟩
  rw [hw,hv,CharTwo.add_self_eq_zero]

end ReeF4.RootPresentationRecognition.EndpointCoefficientRigidity
