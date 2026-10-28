module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularSuzukiOpposite
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularSuzukiCommute
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularLinearCommute

/-!
# The full opposite Suzuki angular table

The native main-curve commutator is collected into angular order. Squaring
main curves supplies both omega actions because the Suzuki norm is surjective.
Decomposing the actor into its inverse main curve and an omega element then
gives the full `(0,6)` conjugation table, including both central parameters.
The final uniqueness theorem identifies the literal ordered-root table entry,
and its word theorem applies to every target realization.

Source: GLS3 Table 2.4 and 2.4.5(d); Fong--Seitz II (1974), Section 10,
(10.23)--(10.26), in the corrected native Suzuki chart. The calculation is
uniform at the binary field and uses `titsEnd`, without changing conventions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup ReeF4
namespace ReeF4.RootPresentationRecognition.AngularSuzukiOppositeTable
open CentralCovers.TwoPrimary ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.RadicalCoordinates.FixedCoordinates
variable (m : ℕ)
local notation "L" i:max a:max => (PositiveTables.pair m i a : Model m)
local notation "S" i:max a:max b:max => (PositiveTables.quartet m i a b : Model m)

private theorem field_two : (2 : CoefficientField m) = 0 := CharTwo.two_eq_zero
private theorem field_three : (3 : CoefficientField m) = 1 := by
  calc
    _ = (1 + 1 : CoefficientField m) + 1 := by norm_num
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

private theorem field_five : (5 : CoefficientField m) = 1 := by
  calc
    _ = ((1 + 1 : CoefficientField m) + (1 + 1)) + 1 := by norm_num
    _ = _ := by rw [CharTwo.add_self_eq_zero,zero_add]

private theorem collect_pair {G : Type*} [Group G] (P I J Y : G) :
    (P*I)*(J*Y)=P*(I*J)*Y := by simp only [mul_assoc]

private theorem qmul (i : Fin 4) (a b c d : CoefficientField m) :
    S i a b * S i c d = S i (a+c) (b+d+titsEnd m a*c) := by
  rw [←Subgroup.coe_mul,PositiveTables.quartet_mul]
private theorem qinv (i : Fin 4) (a b : CoefficientField m) :
    (S i a b)⁻¹ = S i a (b+titsEnd m a*a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [qmul]
  have h : b+(b+titsEnd m a*a)+titsEnd m a*a = 0 := by
    rw [←add_assoc b b,CharTwo.add_self_eq_zero,zero_add,CharTwo.add_self_eq_zero]
  simp only [h,CharTwo.add_self_eq_zero,PositiveTables.quartet_zero,Subgroup.coe_one]
private theorem lsq (i : Fin 4) (a : CoefficientField m) : L i a * L i a = 1 := by
  rw [←Subgroup.coe_mul,PositiveTables.pair_mul,CharTwo.add_self_eq_zero,
    PositiveTables.pair_zero,Subgroup.coe_one]
private theorem osq (i : Fin 4) (a : CoefficientField m) : S i 0 a * S i 0 a = 1 := by
  rw [qmul]
  simp only [map_zero,zero_mul,CharTwo.add_self_eq_zero,
    PositiveTables.quartet_zero,Subgroup.coe_one]
private theorem conj_swap {G : Type*} [Group G] {a b c : G}
    (h : a*b*a⁻¹ = c*b) : a*b = c*b*a := by
  calc _ = (a*b*a⁻¹)*a := by group
       _ = _ := by rw [h]
private theorem commute_of_conj {G : Type*} [Group G] {a b : G}
    (h : a*b*a⁻¹ = b) : Commute a b := by
  change a*b = b*a
  calc _ = (a*b*a⁻¹)*a := by group
       _ = _ := by rw [h]

private theorem reverse_swap {G : Type*} [Group G] {x y z : G}
    (h : x*y=z*y*x) (hz : z*z=1) : y*x=z*x*y := by
  calc
    _ = z*(z*(y*x)) := by simp only [←mul_assoc,hz,one_mul]
    _ = z*(x*y) := by rw [←mul_assoc z y x,←h]
    _ = _ := by group

private theorem middle_adjacent (a b d : CoefficientField m) :
    Commute (L 3 a) (S 1 b d) ∧ Commute (S 3 b d) (L 3 a) ∧
    Commute (S 1 b d) (L 2 a) := by
  have hp (i : Fin 4) (x : CoefficientField m) :
      L i x = mainElement m (![7,1,5,3] i) x := by
    rw [PositiveTables.pair_main]
    simp only [rootIndex,Sum.elim_inl,positive_pair_indices]
  have hs (i : Fin 4) (x y : CoefficientField m) :
      S i x y = blockPoint m (![0,4,6,2] i) x y := by
    rw [PositiveTables.quartet_blockPoint]
    simp only [rootIndex,Sum.elim_inr,positive_quartet_indices]
  simp only [hp,hs]
  change Commute (mainElement m 3 a) (blockPoint m 4 b d) ∧
    Commute (blockPoint m 2 b d) (mainElement m 3 a) ∧
    Commute (blockPoint m 4 b d) (mainElement m 5 a)
  constructor
  · exact AngularAdjacent.native_adjacent_commute m 3 4 (by decide)
      ⟨_,mainElement_mem_X m 3 a⟩ ⟨_,(mem_X_even m 4 (by decide) _).mpr ⟨b,d,rfl⟩⟩
  constructor
  · exact AngularAdjacent.native_adjacent_commute m 2 3 (by decide)
      ⟨_,(mem_X_even m 2 (by decide) _).mpr ⟨b,d,rfl⟩⟩ ⟨_,mainElement_mem_X m 3 a⟩
  · exact AngularAdjacent.native_adjacent_commute m 4 5 (by decide)
      ⟨_,(mem_X_even m 4 (by decide) _).mpr ⟨b,d,rfl⟩⟩ ⟨_,mainElement_mem_X m 5 a⟩

private theorem omega_middle_commute (a b d : CoefficientField m) :
    Commute (S 1 0 a) (S 1 b d) := by
  change _*_ = _*_
  rw [qmul,qmul]
  simp only [zero_add,add_zero,map_zero,zero_mul,mul_zero]
  rw [add_comm a d]

private theorem collect_inverse {G : Type*} [Group G] (A B C D Z Y : G)
    (hYC : Y*C = D*C*Y) (hYB : Y*B = Z*B*Y) (hYA : Commute Y A)
    (hCA : C*A = B*A*C) (hDA : D*A = Z*A*D)
    (hBA : Commute B A) (hBC : Commute B C) (hBD : Commute B D)
    (hBZ : Commute B Z) (hZA : Commute Z A) (hZC : Commute Z C)
    (hDC : Commute D C) (hZD : Commute Z D) (hB : B*B=1) (hZ : Z*Z=1) :
    Y*(C*B*A) = A*C*D*Y := by
  calc
    _ = D*C*Z*B*A*Y := by
      calc
        _ = (Y*C)*B*A := by group
        _ = (D*C*Y)*B*A := by rw [hYC]
        _ = D*C*(Y*B)*A := by group
        _ = D*C*(Z*B*Y)*A := by rw [hYB]
        _ = D*C*Z*B*(Y*A) := by group
        _ = _ := by rw [hYA.eq]; group
    _ = D*(C*A)*Z*B*Y := by
      simp only [mul_assoc]
      rw [hBA.left_comm,hZA.left_comm]
    _ = D*(B*A*C)*Z*B*Y := by rw [hCA]
    _ = B*(D*A)*C*Z*B*Y := by simp only [mul_assoc]; rw [hBD.symm.left_comm]
    _ = B*(Z*A*D)*C*Z*B*Y := by rw [hDA]
    _ = A*D*C*(Z*Z)*(B*B)*Y := by
      simp only [mul_assoc]
      rw [hBZ.left_comm,hBA.left_comm,hBD.left_comm,hBC.left_comm,hBZ.left_comm]
      rw [hZA.left_comm,hZD.left_comm,hZC.left_comm]
    _ = A*C*D*Y := by rw [hZ,hB,mul_one,mul_one]; simp only [mul_assoc]; rw [hDC.left_comm]

/-- The inverse main-curve action collects without a hidden central parameter. -/
theorem main_inverse_conjugate (a y : CoefficientField m) :
    (S 0 a 0)⁻¹ * S 2 y 0 * S 0 a 0 =
      S 3 (titsEnd m a*y) 0 *
        (S 1 (a*titsEnd m y) 0)⁻¹ * L 2 (a*titsEnd m y*y) * S 2 y 0 := by
  let t := titsEnd m a*y
  let v := a*titsEnd m y
  let w := (a*titsEnd m a)*(y*titsEnd m y)
  let A := S 3 t 0
  let B := L 3 w
  let C := (S 1 v 0)⁻¹
  let D := L 2 (v*y)
  let Z := S 1 0 (y*w)
  let Y := S 2 y 0
  have hw : t*v = w := by dsimp [t,v,w]; ring
  have hzw : t*(v*y) = y*w := by dsimp [t,v,w]; ring
  have hYC : Y*C = D*C*Y := by
    have hh := AngularSuzukiNear.near_terminal_conjugate m v (titsEnd m v*v) y 0
    have hc : S 1 v (titsEnd m v*v) = C := by dsimp [C]; rw [qinv,zero_add]
    rw [hc] at hh
    exact reverse_swap (conj_swap hh) (lsq m 2 (v*y))
  have hYB : Y*B = Z*B*Y :=
    reverse_swap (conj_swap (AngularCoefficients.short_reflected_conjugate m y 0 w))
      (osq m 1 (y*w))
  have hYA : Commute Y A := (AngularSuzukiCommute.suzuki_commute_family m t 0 y 0).2.symm
  have hZA : Commute Z A := by
    apply Commute.symm
    apply commute_of_conj
    simpa only [mul_zero,PositiveTables.pair_zero,Subgroup.coe_one,one_mul] using
      AngularSuzukiNear.near_middle_conjugate m t 0 0 (y*w)
  have hCA : C*A = B*A*C := by
    have h := AngularSuzukiNear.near_middle_conjugate m t (titsEnd m t*t) v (titsEnd m v*v)
    have hAi : S 3 t (titsEnd m t*t) = A⁻¹ := by dsimp [A]; rw [qinv,zero_add]
    have hCi : S 1 v (titsEnd m v*v) = C := by dsimp [C]; rw [qinv,zero_add]
    rw [hAi,hCi,inv_inv,hw] at h
    have he : A⁻¹*C*A = B*C := h
    calc C*A = A*(A⁻¹*C*A) := by group
         _ = A*(B*C) := by rw [he]
         _ = B*A*C := by simpa only [mul_assoc] using (middle_adjacent m w t 0).2.1.left_comm C
  have hDA : D*A = Z*A*D := by
    have h := AngularCoefficients.short_shifted_conjugate m t (titsEnd m t*t) (v*y)
    have hAi : S 3 t (titsEnd m t*t) = A⁻¹ := by dsimp [A]; rw [qinv,zero_add]
    rw [hAi,inv_inv,hzw] at h
    have he : A⁻¹*D*A = Z*D := h
    calc D*A = A*(A⁻¹*D*A) := by group
         _ = A*(Z*D) := by rw [he]
         _ = Z*A*D := by simpa only [mul_assoc] using hZA.symm.left_comm D
  have hh := collect_inverse A B C D Z Y hYC hYB hYA hCA hDA
    (middle_adjacent m w t 0).2.1.symm
    ((middle_adjacent m w v 0).1.inv_right)
    (AngularLinearCommute.linear_commute_family m w (v*y)).2.2.1
    ((middle_adjacent m w 0 (y*w)).1)
    hZA ((omega_middle_commute m (y*w) v 0).inv_right)
    ((middle_adjacent m (v*y) v 0).2.2.inv_left.symm)
    ((middle_adjacent m (v*y) 0 (y*w)).2.2) (lsq m 3 w) (osq m 1 (y*w))
  calc
    _ = Y*(C*B*A) := by
      rw [←AngularSuzukiOpposite.main_right_commutator m a y]
      dsimp [Y]
      group
    _ = _ := hh

private theorem pmul (i : Fin 4) (a b : CoefficientField m) :
    L i a*L i b = L i (a+b) := by rw [←Subgroup.coe_mul,PositiveTables.pair_mul]
private theorem pcomm (i : Fin 4) (a b : CoefficientField m) : Commute (L i a) (L i b) := by
  change _*_ = _*_
  rw [pmul,pmul,add_comm]

private theorem inner_collect {G : Type*} [Group G]
    (A B C D A' B' C' D' E Z : G)
    (hDA : D*A'=A'*Z*D) (hCA : C*A'=A'*E*C)
    (hBA : Commute B A') (hDB : Commute D B') (hZB : Commute Z B')
    (hCB : Commute C B') (hEB : Commute E B') (hDC : Commute D C')
    (hZC : Commute Z C') :
    (A*B*C*D)*(A'*B'*C'*D') = (A*A')*(B*B'*E)*(C*C'*Z)*(D*D') := by
  have hDA' (u : G) : D*(A'*u)=A'*(Z*(D*u)) := by rw [←mul_assoc,hDA]; group
  have hCA' (u : G) : C*(A'*u)=A'*(E*(C*u)) := by rw [←mul_assoc,hCA]; group
  simp only [mul_assoc]
  rw [hDA',hCA',hBA.left_comm,hDB.left_comm,hZB.left_comm,hCB.left_comm,
    hEB.left_comm,hDC.left_comm,hZC.left_comm]

/-- The four interior factors, already in angular order. -/
def inner (t r w v l s : CoefficientField m) : Model m :=
  S 3 t r*L 3 w*S 1 v l*L 2 s

private theorem inner_mul (T R W V J U t r w v l s : CoefficientField m) :
    inner m T R W V J U * inner m t r w v l s =
      inner m (T+t) (R+r+titsEnd m T*t) (W+w+t*V) (V+v)
        (J+l+titsEnd m V*v+t*U) (U+s) := by
  have hZA : Commute (S 1 0 (t*U)) (S 3 t r) := by
    apply Commute.symm
    apply commute_of_conj
    simpa only [mul_zero,PositiveTables.pair_zero,Subgroup.coe_one,one_mul] using
      AngularSuzukiNear.near_middle_conjugate m t r 0 (t*U)
  have hDA : L 2 U*S 3 t r = S 3 t r*S 1 0 (t*U)*L 2 U := by
    have h := reverse_swap (conj_swap (AngularCoefficients.short_shifted_conjugate m t r U))
      (osq m 1 (t*U))
    exact h.trans (by rw [hZA.eq])
  have hCA : S 1 V J*S 3 t r = S 3 t r*L 3 (t*V)*S 1 V J := by
    have h := reverse_swap (conj_swap (AngularSuzukiNear.near_middle_conjugate m t r V J))
      (lsq m 3 (t*V))
    exact h.trans (by rw [(middle_adjacent m (t*V) t r).2.1.symm.eq])
  have he := inner_collect (S 3 T R) (L 3 W) (S 1 V J) (L 2 U)
    (S 3 t r) (L 3 w) (S 1 v l) (L 2 s) (L 3 (t*V)) (S 1 0 (t*U))
    hDA hCA (middle_adjacent m W t r).2.1.symm
    (AngularLinearCommute.linear_commute_family m w U).2.2.1.symm
    (middle_adjacent m w 0 (t*U)).1.symm (middle_adjacent m w V J).1.symm
    (pcomm m 3 (t*V) w) (middle_adjacent m U v l).2.2.symm
    (omega_middle_commute m (t*U) v l)
  change _ = inner m (T+t) (R+r+titsEnd m T*t) (W+w+t*V) (V+v)
        (J+l+titsEnd m V*v+t*U) (U+s)
  rw [show inner m T R W V J U*inner m t r w v l s = _ from he]
  rw [qmul,pmul,pmul,qmul,qmul,pmul]
  simp only [add_zero,mul_zero,inner]

private theorem inner_source (t r w v l s : CoefficientField m) :
    inner m t r w v l s =
      inner m t r 0 0 0 0*inner m 0 0 w 0 0 0*
        inner m 0 0 0 v l 0*inner m 0 0 0 0 0 s := by
  simp only [inner_mul,add_zero,zero_add,map_zero,zero_mul,mul_zero]


private theorem inner_s3 (t r : CoefficientField m) : inner m t r 0 0 0 0 = S 3 t r := by
  simp only [inner,PositiveTables.quartet_zero,PositiveTables.pair_zero,Subgroup.coe_one,mul_one]
private theorem inner_l3 (w : CoefficientField m) : inner m 0 0 w 0 0 0 = L 3 w := by
  simp only [inner,PositiveTables.quartet_zero,PositiveTables.pair_zero,Subgroup.coe_one,mul_one,one_mul]
private theorem inner_s1 (v l : CoefficientField m) : inner m 0 0 0 v l 0 = S 1 v l := by
  simp only [inner,PositiveTables.quartet_zero,PositiveTables.pair_zero,Subgroup.coe_one,mul_one,one_mul]
private theorem inner_l2 (s : CoefficientField m) : inner m 0 0 0 0 0 s = L 2 s := by
  simp only [inner,PositiveTables.quartet_zero,PositiveTables.pair_zero,Subgroup.coe_one,one_mul]

private theorem inner_inverse_conjugate (a t r w v l s : CoefficientField m) :
    MulAut.conj ((S 0 a 0)⁻¹) (inner m t r w v l s) =
      L 1 (a*t)*inner m t (r+a*w) (w+titsEnd m a*s) v (l+a*titsEnd m s) s := by
  let f := MulAut.conj ((S 0 a 0)⁻¹)
  have h0 : f (inner m t r 0 0 0 0) = L 1 (a*t)*inner m t r 0 0 0 0 := by
    rw [inner_s3]
    change (S 0 a 0)⁻¹*S 3 t r*((S 0 a 0)⁻¹)⁻¹ = _
    rw [qinv]
    exact AngularSuzukiNear.near_conjugate m a _ t r
  have h1 : f (inner m 0 0 w 0 0 0) = inner m 0 (a*w) w 0 0 0 := by
    rw [inner_l3]
    change (S 0 a 0)⁻¹*L 3 w*S 0 a 0 = _
    rw [AngularCoefficients.short_inverse_conjugate]
    simp only [inner,PositiveTables.quartet_zero,PositiveTables.pair_zero,Subgroup.coe_one,mul_one]
  have h2 : f (inner m 0 0 0 v l 0) = inner m 0 0 0 v l 0 := by
    rw [inner_s1]
    change (S 0 a 0)⁻¹*S 1 v l*S 0 a 0 = S 1 v l
    rw [(AngularSuzukiCommute.suzuki_commute_family m a 0 v l).1.inv_left.eq]
    group
  have h3 : f (inner m 0 0 0 0 0 s) = inner m 0 0 (titsEnd m a*s) 0 (a*titsEnd m s) s := by
    rw [inner_l2]
    change (S 0 a 0)⁻¹*L 2 s*S 0 a 0 = _
    rw [AngularCoefficients.next_inverse_conjugate]
    simp only [zero_mul,inner,PositiveTables.quartet_zero,Subgroup.coe_one,one_mul]
  have h := congrArg f (inner_source m t r w v l s)
  rw [map_mul,map_mul,map_mul,h0,h1,h2,h3] at h
  calc
    _ = L 1 (a*t)*((inner m t r 0 0 0 0*inner m 0 (a*w) w 0 0 0)*
        inner m 0 0 0 v l 0*inner m 0 0 (titsEnd m a*s) 0 (a*titsEnd m s) s) := by
      rw [h]; group
    _ = _ := by simp only [inner_mul,add_zero,zero_add,map_zero,zero_mul,mul_zero]

private theorem opposite_conjugate_inner (y z t r w v l s : CoefficientField m) :
    MulAut.conj (S 2 y z) (inner m t r w v l s) =
      inner m t r w v (l+y*w) (s+v*y) := by
  let f := MulAut.conj (S 2 y z)
  have h0 : f (inner m t r 0 0 0 0) = inner m t r 0 0 0 0 := by
    rw [inner_s3]
    change S 2 y z*S 3 t r*(S 2 y z)⁻¹ = _
    rw [(AngularSuzukiCommute.suzuki_commute_family m t r y z).2.symm.eq]
    group
  have h1 : f (inner m 0 0 w 0 0 0) = inner m 0 0 w 0 (y*w) 0 := by
    rw [inner_l3]
    have h := reverse_swap (conj_swap (AngularCoefficients.short_reflected_conjugate m y z w))
      (osq m 1 (y*w))
    change S 2 y z*L 3 w*(S 2 y z)⁻¹ = _
    rw [h]
    simp only [inner,PositiveTables.quartet_zero,PositiveTables.pair_zero,Subgroup.coe_one,one_mul,mul_one]
    rw [mul_assoc,mul_inv_cancel,mul_one,(middle_adjacent m w 0 (y*w)).1.symm.eq]
  have h2 : f (inner m 0 0 0 v l 0) = inner m 0 0 0 v l (v*y) := by
    rw [inner_s1]
    have h := reverse_swap (conj_swap (AngularSuzukiNear.near_terminal_conjugate m v l y z))
      (lsq m 2 (v*y))
    change S 2 y z*S 1 v l*(S 2 y z)⁻¹ = _
    rw [h]
    simp only [inner,PositiveTables.quartet_zero,PositiveTables.pair_zero,Subgroup.coe_one,one_mul]
    rw [mul_assoc,mul_inv_cancel,mul_one,(middle_adjacent m (v*y) v l).2.2.symm.eq]
  have h3 : f (inner m 0 0 0 0 0 s) = inner m 0 0 0 0 0 s := by
    rw [inner_l2]
    have hc : Commute (L 2 s) (S 2 y z) := by
      rw [PositiveTables.pair_main,PositiveTables.quartet_blockPoint]
      simp only [rootIndex,Sum.elim_inl,Sum.elim_inr,positive_pair_indices,positive_quartet_indices]
      exact AngularAdjacent.native_adjacent_commute m 5 6 (by decide)
        ⟨_,mainElement_mem_X m 5 s⟩ ⟨_,(mem_X_even m 6 (by decide) _).mpr ⟨y,z,rfl⟩⟩
    change S 2 y z*L 2 s*(S 2 y z)⁻¹ = _
    rw [hc.symm.eq]
    group
  have h := congrArg f (inner_source m t r w v l s)
  rw [map_mul,map_mul,map_mul,h0,h1,h2,h3] at h
  change f (inner m t r w v l s) = _
  rw [h]
  simp only [inner_mul,add_zero,zero_add,map_zero,zero_mul,mul_zero]
  congr 1 <;> ring

private theorem qsquare (i : Fin 4) (a b : CoefficientField m) :
    S i a b*S i a b = S i 0 (titsEnd m a*a) := by
  rw [qmul]
  simp only [CharTwo.add_self_eq_zero,zero_add]

private theorem norm_surjective (z : CoefficientField m) :
    ∃ y : CoefficientField m, titsEnd m y*y=z := by
  by_cases hz : z=0
  · exact ⟨0,by simp only [map_zero,mul_zero,hz]⟩
  have ht : titsEnd m z ≠ 0 := (map_ne_zero (titsEnd m)).mpr hz
  refine ⟨titsEnd m z/z,?_⟩
  rw [map_div₀,titsEnd_twice]
  field_simp

private theorem inverse_main_inner (a y : CoefficientField m) :
    MulAut.conj ((S 0 a 0)⁻¹) (S 2 y 0) =
      inner m (titsEnd m a*y) 0 0 (a*titsEnd m y)
        (titsEnd m (a*titsEnd m y)*(a*titsEnd m y)) (a*titsEnd m y*y)*S 2 y 0 := by
  change (S 0 a 0)⁻¹*S 2 y 0*S 0 a 0 = _
  rw [main_inverse_conjugate,qinv,zero_add]
  simp only [inner,PositiveTables.pair_zero,Subgroup.coe_one,mul_one]

private theorem inverse_omega (a z : CoefficientField m) :
    MulAut.conj ((S 0 a 0)⁻¹) (S 2 0 z) =
      inner m 0 (a^2*titsEnd m a*z) (a*titsEnd m a*z) 0 0 (a*z)*S 2 0 z := by
  obtain ⟨y,rfl⟩ := norm_surjective m z
  let f := MulAut.conj ((S 0 a 0)⁻¹)
  let t := titsEnd m a*y
  let v := a*titsEnd m y
  let l := titsEnd m v*v
  let s := v*y
  let I := inner m t 0 0 v l s
  have h : f (S 2 y 0) = I*S 2 y 0 := inverse_main_inner m a y
  have hh := congrArg (fun g : Model m => g*g) h
  rw [←map_mul,qsquare] at hh
  have he : I*(MulAut.conj (S 2 y 0) I) =
      inner m 0 (a^2*titsEnd m a*(titsEnd m y*y))
        (a*titsEnd m a*(titsEnd m y*y)) 0 0 (a*(titsEnd m y*y)) := by
    dsimp only [I]
    rw [opposite_conjugate_inner,inner_mul]
    simp only [CharTwo.add_self_eq_zero,zero_add,add_zero,mul_zero]
    dsimp [t,v,l,s]
    rw [map_mul,titsEnd_twice,map_mul,titsEnd_twice]
    congr 1 <;> ring_nf <;> simp only [field_two,field_three,mul_zero,mul_one]
  calc
    _ = (I*S 2 y 0)*(I*S 2 y 0) := hh
    _ = (I*(MulAut.conj (S 2 y 0) I))*(S 2 y 0*S 2 y 0) := by
      simp only [MulAut.conj_apply]; group
    _ = _ := by rw [he,qsquare]

/-- Inverse conjugation by a main curve on the whole opposite Suzuki root. -/
theorem main_inverse_whole (a y z : CoefficientField m) :
    MulAut.conj ((S 0 a 0)⁻¹) (S 2 y z) =
      inner m (titsEnd m a*y) (a^2*titsEnd m a*z) (a*titsEnd m a*z)
        (a*titsEnd m y) (a*titsEnd m a*y*(z+y*titsEnd m y))
        (a*(z+y*titsEnd m y))*S 2 y z := by
  let f := MulAut.conj ((S 0 a 0)⁻¹)
  let I := inner m (titsEnd m a*y) 0 0 (a*titsEnd m y)
    (titsEnd m (a*titsEnd m y)*(a*titsEnd m y)) (a*titsEnd m y*y)
  let J := inner m 0 (a^2*titsEnd m a*z) (a*titsEnd m a*z) 0 0 (a*z)
  have hsplit : S 2 y z=S 2 y 0*S 2 0 z := by
    rw [qmul]; simp only [add_zero,zero_add,mul_zero]
  have he : I*(MulAut.conj (S 2 y 0) J) =
      inner m (titsEnd m a*y) (a^2*titsEnd m a*z) (a*titsEnd m a*z)
        (a*titsEnd m y) (a*titsEnd m a*y*(z+y*titsEnd m y))
        (a*(z+y*titsEnd m y)) := by
    dsimp only [I,J]
    rw [opposite_conjugate_inner,inner_mul]
    simp only [add_zero,zero_add,mul_zero]
    rw [map_mul,titsEnd_twice]
    congr 1 <;> ring
  calc
    _ = (I*S 2 y 0)*(J*S 2 0 z) := by
      rw [hsplit,map_mul,inverse_main_inner,inverse_omega]
    _ = (I*(MulAut.conj (S 2 y 0) J))*(S 2 y 0*S 2 0 z) := by
      simp only [MulAut.conj_apply]; group
    _ = _ := by rw [he,←hsplit]

private theorem reflected_adjacent (a b p : CoefficientField m) :
    Commute (S 0 a b) (L 1 p) ∧ Commute (L 1 p) (S 3 a b) := by
  rw [PositiveTables.quartet_blockPoint,PositiveTables.pair_main,PositiveTables.quartet_blockPoint]
  simp only [rootIndex,Sum.elim_inl,Sum.elim_inr,positive_pair_indices,positive_quartet_indices]
  constructor
  · exact AngularAdjacent.native_adjacent_commute m 0 1 (by decide)
      ⟨_,(mem_X_even m 0 (by decide) _).mpr ⟨a,b,rfl⟩⟩ ⟨_,mainElement_mem_X m 1 p⟩
  · exact AngularAdjacent.native_adjacent_commute m 1 2 (by decide)
      ⟨_,mainElement_mem_X m 1 p⟩ ⟨_,(mem_X_even m 2 (by decide) _).mpr ⟨a,b,rfl⟩⟩

private theorem main_conj_twice (d : CoefficientField m) (g : Model m) :
    MulAut.conj ((S 0 d 0)⁻¹) (MulAut.conj ((S 0 d 0)⁻¹) g) =
      MulAut.conj (S 0 0 (titsEnd m d*d)) g := by
  calc
    _ = MulAut.conj ((S 0 d 0*S 0 d 0)⁻¹) g := by simp only [MulAut.conj_apply,mul_inv_rev,inv_inv,mul_assoc]
    _ = _ := by rw [qsquare,qinv]; simp only [map_zero,zero_mul,add_zero]

private theorem omega_conjugate_inner (b t r w v l s : CoefficientField m) :
    MulAut.conj (S 0 0 b) (inner m t r w v l s) = inner m t (r+b*s) w v l s := by
  obtain ⟨d,rfl⟩ := norm_surjective m b
  rw [←main_conj_twice,inner_inverse_conjugate,map_mul,inner_inverse_conjugate]
  have hc : MulAut.conj ((S 0 d 0)⁻¹) (L 1 (d*t)) = L 1 (d*t) := by
    change (S 0 d 0)⁻¹*L 1 (d*t)*S 0 d 0 = _
    rw [(reflected_adjacent m d 0 (d*t)).1.inv_left.eq]
    group
  rw [hc,←mul_assoc,lsq,one_mul]
  congr 1 <;> ring_nf <;> simp only [field_two,mul_zero,add_zero]

/-- The omega subgroup acts with explicit native opposite-root coordinates. -/
theorem omega_whole_conjugate (b y z : CoefficientField m) :
    MulAut.conj (S 0 0 b) (S 2 y z) =
      L 1 (b*y)*inner m 0 (titsEnd m b*(z+y*titsEnd m y)) (b*z) 0
        (b*(titsEnd m z+y*(z+y*titsEnd m y))) 0*S 2 y z := by
  obtain ⟨d,rfl⟩ := norm_surjective m b
  rw [←main_conj_twice,main_inverse_whole,map_mul,inner_inverse_conjugate,main_inverse_whole]
  rw [collect_pair]
  rw [inner_mul]
  simp only [map_mul,map_add,titsEnd_twice]
  apply congrArg (fun g : Model m => g*S 2 y z)
  apply congrArg₂ (fun (p : CoefficientField m) (g : Model m) => L 1 p*g)
  · ring
  · simp only [CharTwo.add_self_eq_zero]
    congr 1 <;> ring_nf <;> simp only [field_two,field_three,field_five,mul_zero,mul_one,add_zero]

private theorem reflected_conjugate_inner (p t r w v l s : CoefficientField m) :
    MulAut.conj (L 1 p) (inner m t r w v l s) = inner m t (r+v*p) w v l s := by
  let f := MulAut.conj (L 1 p)
  have h0 : f (inner m t r 0 0 0 0) = inner m t r 0 0 0 0 := by
    rw [inner_s3]
    change L 1 p*S 3 t r*(L 1 p)⁻¹ = _
    rw [(reflected_adjacent m t r p).2.eq]
    group
  have h1 : f (inner m 0 0 w 0 0 0) = inner m 0 0 w 0 0 0 := by
    rw [inner_l3]
    change L 1 p*L 3 w*(L 1 p)⁻¹ = _
    rw [(AngularLinearCommute.linear_commute_family m p w).1.eq]
    group
  have h2 : f (inner m 0 0 0 v l 0) = inner m 0 (v*p) 0 v l 0 := by
    rw [inner_s1]
    change L 1 p*S 1 v l*(L 1 p)⁻¹ = _
    rw [AngularCoefficients.short_perpendicular_conjugate]
    simp only [inner,PositiveTables.pair_zero,Subgroup.coe_one,mul_one]
  have h3 : f (inner m 0 0 0 0 0 s) = inner m 0 0 0 0 0 s := by
    rw [inner_l2]
    change L 1 p*L 2 s*(L 1 p)⁻¹ = _
    rw [(AngularLinearCommute.linear_commute_family m p s).2.1.eq]
    group
  have h := congrArg f (inner_source m t r w v l s)
  rw [map_mul,map_mul,map_mul,h0,h1,h2,h3] at h
  change f (inner m t r w v l s) = _
  rw [h]
  simp only [inner_mul,add_zero,zero_add,map_zero,zero_mul,mul_zero]

private theorem inner_reflected_swap (p t r w v l s : CoefficientField m) :
    inner m t r w v l s*L 1 p = L 1 p*inner m t (r+v*p) w v l s := by
  have hinv : (L 1 p)⁻¹=L 1 p := inv_eq_of_mul_eq_one_right (lsq m 1 p)
  calc
    _ = L 1 p*(MulAut.conj (L 1 p) (inner m t r w v l s)) := by
      simp only [MulAut.conj_apply,hinv]
      rw [←mul_assoc,←mul_assoc,lsq,one_mul]
    _ = _ := by rw [reflected_conjugate_inner]

private theorem collect_reflected {G : Type*} [Group G] (I P J Y : G) :
    I*(P*J*Y)=(I*P)*J*Y := by simp only [mul_assoc]
private theorem collect_three {G : Type*} [Group G] (P I J Y : G) :
    P*I*J*Y=P*(I*J)*Y := by simp only [mul_assoc]

/-- The full native opposite Suzuki action in angular order. -/
theorem whole_conjugate (a b y z : CoefficientField m) :
    S 0 a b*S 2 y z*(S 0 a b)⁻¹ =
      L 1 ((b+a*titsEnd m a)*y)*
        inner m (titsEnd m a*y)
          (a*b*z+titsEnd m (b+a*titsEnd m a)*(z+y*titsEnd m y))
          (b*z) (a*titsEnd m y)
          (b*y*(z+y*titsEnd m y)+(b+a*titsEnd m a)*titsEnd m z)
          (a*(z+y*titsEnd m y))*S 2 y z := by
  let n := b+a*titsEnd m a
  have hsplit : S 0 a b=S 0 0 n*(S 0 a 0)⁻¹ := by
    rw [qinv,qmul]
    dsimp only [n]
    simp only [zero_add,map_zero,zero_mul,add_zero]
    rw [mul_comm a (titsEnd m a),add_assoc,CharTwo.add_self_eq_zero,add_zero]
  have hact : MulAut.conj (S 0 a b) (S 2 y z) =
      MulAut.conj (S 0 0 n) (MulAut.conj ((S 0 a 0)⁻¹) (S 2 y z)) := by
    rw [hsplit]
    simp only [MulAut.conj_apply,mul_inv_rev,inv_inv,mul_assoc]
  change MulAut.conj (S 0 a b) (S 2 y z) = _
  rw [hact,main_inverse_whole,map_mul,omega_conjugate_inner,omega_whole_conjugate,
    collect_reflected,inner_reflected_swap,collect_three,inner_mul]
  simp only [add_zero,zero_mul,mul_zero]
  dsimp only [n]
  apply congrArg (fun g : Model m => g*S 2 y z)
  apply congrArg (fun g : Model m => L 1 ((b+a*titsEnd m a)*y)*g)
  congr 1 <;> ring_nf <;> simp only [field_two,mul_zero,add_zero,zero_add]


open Theory.GroupTheory.OrderedRootPresentation

/-- The native angular coefficients for the opposite Suzuki pair `(0,6)`. -/
def tail06 (a b y z : CoefficientField m) :
    Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inr 0)) :=
  (PositiveTables.rootChartEquiv m (.inl 1) ((b+a*titsEnd m a)*y),
    PositiveTables.rootChartEquiv m (.inr 3)
      (titsEnd m a*y,a*b*z+titsEnd m (b+a*titsEnd m a)*(z+y*titsEnd m y)),
    PositiveTables.rootChartEquiv m (.inl 3) (b*z),
    PositiveTables.rootChartEquiv m (.inr 1)
      (a*titsEnd m y,b*y*(z+y*titsEnd m y)+(b+a*titsEnd m a)*titsEnd m z),
    PositiveTables.rootChartEquiv m (.inl 2) (a*(z+y*titsEnd m y)),
    PositiveTables.rootChartEquiv m (.inr 2) (y,z),1,PUnit.unit)

/-- The opposite table evaluates in every target root realization. -/
theorem tail06_word {G : Type*} [Group G]
    (f : ∀ i, AngularPresentation.Parameter m i →* G) (a b y z : CoefficientField m) :
    word (AngularPresentation.Parameter m) (fun k => f k)
      (tail sourceOrder (.inr 0)) (tail06 m a b y z) =
      f (.inl 1) (PositiveTables.rootChartEquiv m (.inl 1) ((b+a*titsEnd m a)*y)) *
        f (.inr 3) (PositiveTables.rootChartEquiv m (.inr 3)
          (titsEnd m a*y,a*b*z+titsEnd m (b+a*titsEnd m a)*(z+y*titsEnd m y))) *
        f (.inl 3) (PositiveTables.rootChartEquiv m (.inl 3) (b*z)) *
        f (.inr 1) (PositiveTables.rootChartEquiv m (.inr 1)
          (a*titsEnd m y,b*y*(z+y*titsEnd m y)+(b+a*titsEnd m a)*titsEnd m z)) *
        f (.inl 2) (PositiveTables.rootChartEquiv m (.inl 2) (a*(z+y*titsEnd m y))) *
        f (.inr 2) (PositiveTables.rootChartEquiv m (.inr 2) (y,z)) := by
  change _ * (_ * (_ * (_ * (_ * (_ * (f (.inl 0) 1 * 1)))))) = _
  simp only [tail06,map_one,mul_one,mul_assoc]
  rfl

/-- Native coordinate uniqueness fixes the final Suzuki table entry. -/
theorem table06 (hj : (.inr 2 : PositiveTables.Root) ∈ tail sourceOrder (.inr 0))
    (a b y z : CoefficientField m) :
    (AngularPresentation.table m).conjugate (.inr 0) (.inr 2) hj
      (PositiveTables.rootChartEquiv m (.inr 0) (a,b))
      (PositiveTables.rootChartEquiv m (.inr 2) (y,z)) = tail06 m a b y z := by
  apply AngularPresentation.conjugate_unique
  rw [tail06_word]
  change S 0 a b*S 2 y z*(S 0 a b)⁻¹ =
    L 1 ((b+a*titsEnd m a)*y)*
      S 3 (titsEnd m a*y) (a*b*z+titsEnd m (b+a*titsEnd m a)*(z+y*titsEnd m y))*
      L 3 (b*z)*
      S 1 (a*titsEnd m y) (b*y*(z+y*titsEnd m y)+(b+a*titsEnd m a)*titsEnd m z)*
      L 2 (a*(z+y*titsEnd m y))*S 2 y z
  simpa only [inner,mul_assoc] using whole_conjugate m a b y z

end ReeF4.RootPresentationRecognition.AngularSuzukiOppositeTable
