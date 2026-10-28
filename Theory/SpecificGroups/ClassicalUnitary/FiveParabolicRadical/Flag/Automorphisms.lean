module
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Sylow
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The seven-free Sylow automorphism group of PSU₅(4)

The literal flag coordinates have fourth power equal to a central matrix
whose only nonzero coordinate is the norm of the product of the two simple
root coordinates. Involution cosets mark the first root axis; the vanishing
of fourth powers marks the second. Every automorphism therefore preserves
both axes of the Frattini quotient.

An automorphism of order dividing seven fixes the fourth-power values,
which form a set of size at most four. Its action on a root axis has a
nonzero fixed vector, since the axis has fifteen nonzero vectors. The norm
identity then preserves fifth-power fibers on the other axis. These fibers
have at most five elements, so an order-seven permutation fixes each of
them pointwise. Both axes are fixed, and the Burnside basis kernel finishes
the argument. Sylow conjugacy transports this obstruction through the
literal projective unitary marking.

Source: the matrix groups of Aschbacher--Smith F.1.12(7), pp.263--264,
applied to the outer section in 4.4.10--11 and 12.1.9, pp.621,793.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.Flag.Automorphisms
open PlaneCore
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

omit [CharP F 2] in
private theorem act_x (t : Multiplicative F) (u : Parameters J) :
    ((Parameters.planeAction.comp (SpecialLinearGroup.upperUnipotentHom F)) t u).x =
      ![u.x 0 + t.toAdd * u.x 1, u.x 1] := by
  ext i
  fin_cases i <;> simp [SpecialLinearGroup.upperUnipotentHom,
    SpecialLinearGroup.transvection_coe, Parameters.planeAction_x,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem square_right (u : Coordinates J) : (u * u).right = 1 := by
  change Multiplicative.ofAdd (u.right.toAdd + u.right.toAdd) = 1
  rw [CharTwo.add_self_eq_zero]
  rfl

private theorem fourth_right (u : Coordinates J) : (u ^ 4).right = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  exact square_right J (u * u)

private theorem fourth_x (u : Coordinates J) : (u ^ 4).left.x = 0 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  rw [SemidirectProduct.mul_left,square_right,map_one,MulAut.one_apply,Parameters.mul_x]
  ext i
  exact CharTwo.add_self_eq_zero _

private theorem fourth_z (u : Coordinates J) :
    (u ^ 4).left.z = !![(u.right.toAdd * u.left.x 1) * J.conj (u.right.toAdd * u.left.x 1),0;0,0] := by
  have hr : (u * u).right = 1 := by
    change Multiplicative.ofAdd (u.right.toAdd + u.right.toAdd) = 1
    rw [CharTwo.add_self_eq_zero]
    rfl
  rw [show 4 = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  rw [SemidirectProduct.mul_left,hr,map_one,MulAut.one_apply]
  ext i j
  rw [Parameters.mul_z,CharTwo.add_self_eq_zero,zero_add]
  simp only [SemidirectProduct.mul_left, Parameters.mul_x, act_x]
  fin_cases i <;> fin_cases j <;>
    simp [CharTwo.add_self_eq_zero]
  rw [← add_assoc,CharTwo.add_self_eq_zero,zero_add]
  rw [← add_assoc,CharTwo.add_self_eq_zero,zero_add]

private theorem fourth_eq_iff (u : Coordinates J) :
    u ^ 4 = 1 ↔ u.right.toAdd = 0 ∨ u.left.x 1 = 0 := by
  constructor
  · intro h
    have hz := congrArg (fun v : Coordinates J => v.left.z 0 0) h
    rw [fourth_z] at hz
    change (u.right.toAdd * u.left.x 1) * J.conj (u.right.toAdd * u.left.x 1) = 0 at hz
    rcases mul_eq_zero.mp hz with hz | hz
    · exact mul_eq_zero.mp hz
    · exact mul_eq_zero.mp (J.conj.injective (hz.trans (map_zero J.conj).symm))
  · intro h
    apply SemidirectProduct.ext
    · apply Parameters.ext
      · exact fourth_x J u
      · rw [fourth_z]
        ext i j
        rcases h with h | h <;> fin_cases i <;> fin_cases j <;> simp [h]
    · exact fourth_right J u

private theorem toEquiv_seven {P : Type*} [Group P] (a : MulAut P) (ha : a^7 = 1) :
    a.toEquiv^7 = 1 := by
  have he (n : ℕ) : a.toEquiv^n = (a^n).toEquiv := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ,pow_succ,ih]; rfl
  rw [he,ha]
  rfl

private theorem small_seven_perm {X : Type*} [Finite X] (a : Equiv.Perm X)
    (ha : a ^ 7 = 1) (hc : Nat.card X < 7) : a = 1 := by
  have ho := (Nat.dvd_prime (by decide : Nat.Prime 7)).mp (orderOf_dvd_of_pow_eq_one ha)
  rcases ho with ho | ho
  · exact orderOf_eq_one_iff.mp ho
  · have hd := orderOf_dvd_natCard a
    rw [ho, Nat.card_perm] at hd
    exact ((Nat.Prime.dvd_factorial (by decide : Nat.Prime 7)).mp hd).not_gt hc |>.elim

private theorem small_invariant_fixed {X : Type*} (a : Equiv.Perm X)
    (ha : a ^ 7 = 1) (s : Set X) [Finite s] (hs : ∀ x, a x ∈ s ↔ x ∈ s)
    (hc : Nat.card s < 7) : ∀ x ∈ s, a x = x := by
  have he : a.subtypePerm hs = 1 := small_seven_perm _ (by simp only [Equiv.Perm.subtypePerm_pow,ha]; rfl) hc
  intro x hx
  exact congrArg Subtype.val (Equiv.congr_fun he ⟨x,hx⟩)

private def fourthValues : Set (Coordinates J) := Set.range (fun u => u ^ 4)

variable [Finite F]

private theorem fourthValues_card (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) : Nat.card (fourthValues J) ≤ 4 := by
  let f : fourthValues J → {x : F // J.conj x = x} := fun u =>
    ⟨u.val.left.z 0 0,by
      obtain ⟨v,hv⟩ := u.property
      rw [←hv,fourth_z]
      change J.conj (_ * J.conj _) = _
      rw [map_mul,J.conj_involutive,mul_comm]
      rfl⟩
  have hi : Function.Injective f := by
    rintro ⟨_,u,rfl⟩ ⟨_,v,rfl⟩ he
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply Parameters.ext
      · rw [fourth_x,fourth_x]
      · have hz := congrArg Subtype.val he
        change (u^4).left.z 0 0 = (v^4).left.z 0 0 at hz
        rw [fourth_z,fourth_z] at hz ⊢
        ext i j
        fin_cases i <;> fin_cases j <;> first | exact hz | rfl
    · rw [fourth_right,fourth_right]
  exact (Nat.card_le_card_of_injective f hi).trans_eq (fixed_card_four J hcard hconj)

private theorem fourth_fixed (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (a : MulAut (Coordinates J)) (ha : a ^ 7 = 1)
    (u : Coordinates J) : a (u ^ 4) = u ^ 4 := by
  let : Finite (Parameters J) := Finite.of_injective (fun u : Parameters J => (u.x,u.z))
    (fun _ _ h => Parameters.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let : Finite (Coordinates J) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  apply small_invariant_fixed a.toEquiv (toEquiv_seven a ha) (fourthValues J) ?_
    (lt_of_le_of_lt (fourthValues_card J hcard hconj) (by decide)) _ ⟨u,rfl⟩
  intro x
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨a.symm v,by change (a.symm v)^4 = x; rw [←map_pow]; exact congrArg a.symm hv |>.trans (a.symm_apply_apply x)⟩
  · rintro ⟨v,rfl⟩
    exact ⟨a v,(map_pow a v 4).symm⟩

private noncomputable def rootAction (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    MulAut (Coordinates J) →* MulAut (Multiplicative (F × F)) :=
  (MulAut.congr (frattiniEquiv J c hc hJ)).toMonoidHom.comp
    (quotientAut (frattini (Coordinates J)))

private theorem rootAction_apply (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (a : MulAut (Coordinates J)) (u : Coordinates J) :
    rootAction J c hc hJ a (rootCoordinates J u) = rootCoordinates J (a u) := by
  have he : rootCoordinates J u = frattiniEquiv J c hc hJ (QuotientGroup.mk' _ u) := rfl
  rw [he]
  change frattiniEquiv J c hc hJ
    (quotientAut (frattini (Coordinates J)) a
      ((frattiniEquiv J c hc hJ).symm (frattiniEquiv J c hc hJ (QuotientGroup.mk' _ u)))) = _
  rw [MulEquiv.symm_apply_apply,quotientAut_apply_mk]
  rfl

private theorem rootAction_first (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (a : MulAut (Coordinates J)) (v : Multiplicative (F × F)) (hv : v.toAdd.2 = 0) :
    (rootAction J c hc hJ a v).toAdd.2 = 0 := by
  have him : v ∈ rootCoordinates J '' {u : Coordinates J | u^2 = 1} := by
    rw [rootCoordinates_involution_image]; exact hv
  obtain ⟨u,hu,rfl⟩ := him
  rw [rootAction_apply]
  exact involution_secondRoot_zero J (a u) (by rw [← map_pow,hu,map_one])

private theorem rootAction_first_iff (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (a : MulAut (Coordinates J)) (v : Multiplicative (F × F)) :
    (rootAction J c hc hJ a v).toAdd.2 = 0 ↔ v.toAdd.2 = 0 := by
  refine ⟨fun h => ?_, rootAction_first J c hc hJ a v⟩
  have hh := rootAction_first J c hc hJ a⁻¹ _ h
  rw [map_inv,MulAut.inv_apply_self] at hh
  exact hh

private theorem rootAction_second (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (a : MulAut (Coordinates J)) (v : Multiplicative (F × F)) (hv : v.toAdd.1 = 0) :
    (rootAction J c hc hJ a v).toAdd.1 = 0 := by
  by_cases hy : v.toAdd.2 = 0
  · have he : v = 1 := Multiplicative.toAdd.injective (Prod.ext hv hy)
    rw [he,map_one]; rfl
  obtain ⟨u,rfl⟩ := rootCoordinates_surjective J c hc v
  have hu : u^4 = 1 := (fourth_eq_iff J u).mpr (Or.inl hv)
  have ha4 : (a u)^4 = 1 := by rw [←map_pow,hu,map_one]
  rw [rootAction_apply]
  rcases (fourth_eq_iff J (a u)).mp ha4 with h | h
  · exact h
  · exact (hy ((rootAction_first_iff J c hc hJ a _).mp
      (by rw [rootAction_apply]; exact h))).elim

private theorem perm_seven_of_intertwiner {X Y : Type*}
    (a : Equiv.Perm X) (b : Equiv.Perm Y) (f : Y → X)
    (hf : Function.Injective f) (he : ∀ y, f (b y) = a (f y)) (ha : a^7 = 1) : b^7 = 1 := by
  have hp (n : ℕ) (y : Y) : f ((b^n) y) = (a^n) (f y) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,he,ih]
  ext y
  apply hf
  rw [hp,ha]
  rfl

omit [CharP F 2] in
private theorem fixed_nonzero (hcard : Nat.card F = 16) (a : Equiv.Perm F)
    (ha : a^7 = 1) (h0 : a 0 = 0) : ∃ x : F, x ≠ 0 ∧ a x = x := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hs (x : F) : a x ≠ 0 ↔ x ≠ 0 := by simpa only [h0] using a.injective.ne_iff (x := x) (y := 0)
  let b : Equiv.Perm {x : F // x ≠ 0} := a.subtypePerm hs
  have hb : b^7^1 = 1 := by simp only [pow_one,b,Equiv.Perm.subtypePerm_pow,ha]; rfl
  have hc : Fintype.card {x : F // x ≠ 0} = 15 := by
    rw [Fintype.card_subtype_compl]
    have he : Fintype.card F = 16 := (Nat.card_eq_fintype_card).symm.trans hcard
    simp [he]
  obtain ⟨x,hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (by rw [hc]; decide : ¬7 ∣ Fintype.card {x : F // x ≠ 0}) hb
  exact ⟨x.val,x.property,congrArg Subtype.val hx⟩

omit [CharP F 2] in
private theorem fifth_fiber_card (z : F) : Nat.card {x : F // x^5 = z} ≤ 5 := by
  classical
  let f : {x : F // x^5 = z} → {x // x ∈ (Polynomial.nthRoots 5 z).toFinset} :=
    fun x => ⟨x.val, by simpa only [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by decide : 0 < 5)] using x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : {x // x ∈ (Polynomial.nthRoots 5 z).toFinset} => z.val) h)
  have hh : Nat.card {x // x ∈ (Polynomial.nthRoots 5 z).toFinset} ≤
      (Polynomial.nthRoots 5 z).card := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_coe]
    exact Multiset.toFinset_card_le _
  exact (Nat.card_le_card_of_injective f hf).trans (hh.trans (Polynomial.card_nthRoots 5 z))

omit [CharP F 2] in
private theorem norm_preserving_seven (a : Equiv.Perm F) (ha : a^7 = 1)
    (hn : ∀ x, (a x)^5 = x^5) : a = 1 := by
  ext x
  have hs (y : F) : (a y)^5 = x^5 ↔ y^5 = x^5 := by rw [hn]
  exact small_invariant_fixed a ha {y | y^5 = x^5} hs
    (lt_of_le_of_lt (fifth_fiber_card (x^5)) (by decide)) x rfl

private noncomputable def firstPerm
    (a : MulAut (Multiplicative (F × F)))
    (h : ∀ x : F, (a (Multiplicative.ofAdd (x,0))).toAdd.2 = 0) : Equiv.Perm F := by
  let f : F → F := fun x => (a (Multiplicative.ofAdd (x,0))).toAdd.1
  have hi : Function.Injective f := by
    intro x y he
    have hh := a.injective (Multiplicative.toAdd.injective (Prod.ext he ((h x).trans (h y).symm)))
    exact congrArg (fun v : Multiplicative (F × F) => v.toAdd.1) hh
  exact Equiv.ofBijective f ⟨hi,Finite.surjective_of_injective hi⟩

private noncomputable def secondPerm
    (a : MulAut (Multiplicative (F × F)))
    (h : ∀ x : F, (a (Multiplicative.ofAdd (0,x))).toAdd.1 = 0) : Equiv.Perm F := by
  let f : F → F := fun x => (a (Multiplicative.ofAdd (0,x))).toAdd.2
  have hi : Function.Injective f := by
    intro x y he
    have hh := a.injective (Multiplicative.toAdd.injective (Prod.ext ((h x).trans (h y).symm) he))
    exact congrArg (fun v : Multiplicative (F × F) => v.toAdd.2) hh
  exact Equiv.ofBijective f ⟨hi,Finite.surjective_of_injective hi⟩

private theorem rootAction_norm (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x^4)
    (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (a : MulAut (Coordinates J)) (ha : a^7 = 1) (v : Multiplicative (F × F)) :
    ((rootAction J c hc hJ a v).toAdd.1 * (rootAction J c hc hJ a v).toAdd.2)^5 =
      (v.toAdd.1 * v.toAdd.2)^5 := by
  obtain ⟨u,rfl⟩ := rootCoordinates_surjective J c hc v
  have hh := congrArg (fun v : Coordinates J => v.left.z 0 0) (fourth_fixed J hcard hconj a ha u)
  rw [map_pow,fourth_z,fourth_z] at hh
  rw [rootAction_apply]
  change ((a u).right.toAdd * (a u).left.x 1)^5 = (u.right.toAdd * u.left.x 1)^5
  change (_ * J.conj _) = (_ * J.conj _) at hh
  simpa only [hconj,←pow_succ'] using hh


private theorem rootAction_seven (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x^4)
    (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (a : MulAut (Coordinates J)) (ha : a^7 = 1) : rootAction J c hc hJ a = 1 := by
  let b := rootAction J c hc hJ a
  have h1 (x : F) : (b (Multiplicative.ofAdd (x,0))).toAdd.2 = 0 :=
    rootAction_first J c hc hJ a _ rfl
  have h2 (x : F) : (b (Multiplicative.ofAdd (0,x))).toAdd.1 = 0 :=
    rootAction_second J c hc hJ a _ rfl
  let f := firstPerm b h1
  let g := secondPerm b h2
  have hf (x : F) : b (Multiplicative.ofAdd (x,0)) = Multiplicative.ofAdd (f x,0) :=
    Multiplicative.toAdd.injective (Prod.ext rfl (h1 x))
  have hg (x : F) : b (Multiplicative.ofAdd (0,x)) = Multiplicative.ofAdd (0,g x) :=
    Multiplicative.toAdd.injective (Prod.ext (h2 x) rfl)
  have hb : b^7 = 1 := by rw [←map_pow,ha,map_one]
  have hf7 : f^7 = 1 := perm_seven_of_intertwiner b.toEquiv f
    (fun x => Multiplicative.ofAdd (x,0))
    (fun _ _ h => congrArg (fun v : Multiplicative (F × F) => v.toAdd.1) h)
    (fun x => (hf x).symm) (toEquiv_seven b hb)
  have hg7 : g^7 = 1 := perm_seven_of_intertwiner b.toEquiv g
    (fun x => Multiplicative.ofAdd (0,x))
    (fun _ _ h => congrArg (fun v : Multiplicative (F × F) => v.toAdd.2) h)
    (fun x => (hg x).symm) (toEquiv_seven b hb)
  have hg0 : g 0 = 0 := by
    have hh := hg 0
    rw [show (Multiplicative.ofAdd (0,0) : Multiplicative (F × F)) = 1 from rfl,map_one] at hh
    exact (congrArg (fun v : Multiplicative (F × F) => v.toAdd.2) hh).symm
  have hxy (x y : F) : b (Multiplicative.ofAdd (x,y)) = Multiplicative.ofAdd (f x,g y) := by
    rw [show Multiplicative.ofAdd (x,y) =
      (Multiplicative.ofAdd (x,0) : Multiplicative (F × F)) * Multiplicative.ofAdd (0,y) from by
        apply Multiplicative.toAdd.injective; simp]
    rw [map_mul,hf,hg]
    apply Multiplicative.toAdd.injective
    simp
  have hn (x y : F) : (f x * g y)^5 = (x*y)^5 := by
    have hh := rootAction_norm J hcard hconj c hc hJ a ha (Multiplicative.ofAdd (x,y))
    change ((b (Multiplicative.ofAdd (x,y))).toAdd.1 *
      (b (Multiplicative.ofAdd (x,y))).toAdd.2)^5 = _ at hh
    rw [hxy] at hh
    exact hh
  obtain ⟨y,hy,hgy⟩ := fixed_nonzero hcard g hg7 hg0
  have hfe : f = 1 := norm_preserving_seven f hf7 (by
    intro x
    have hh := hn x y
    rw [hgy,mul_pow,mul_pow] at hh
    exact (mul_right_cancel₀ (pow_ne_zero 5 hy)) hh)
  have hge : g = 1 := norm_preserving_seven g hg7 (by
    intro x
    simpa only [hfe,Equiv.Perm.one_apply,one_mul] using hn 1 x)
  apply MulEquiv.ext
  intro v
  have hh := hxy v.toAdd.1 v.toAdd.2
  change b v = v
  simpa only [hfe,hge,Equiv.Perm.one_apply,Prod.mk.eta,ofAdd_toAdd] using hh

/-- Fourth-power fibers exclude automorphisms of order seven in the actual
unitary flag coordinates. -/
theorem automorphism_seventh_power (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x^4)
    (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (a : MulAut (Coordinates J)) (ha : a^7 = 1) : a = 1 := by
  let : Finite (Parameters J) := Finite.of_injective (fun u : Parameters J => (u.x,u.z))
    (fun _ _ h => Parameters.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let : Finite (Coordinates J) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hq : a ∈ (quotientAut (frattini (Coordinates J))).ker := by
    apply (MulAut.congr (frattiniEquiv J c hc hJ)).injective
    change rootAction J c hc hJ a = (MulAut.congr (frattiniEquiv J c hc hJ)) 1
    rw [map_one]
    exact rootAction_seven J hcard hconj c hc hJ a ha
  have hp : IsPGroup 2 (Coordinates J) :=
    (unipotent_isPGroup J c hc hJ).of_equiv (coordinatesEquivUnipotent J c hc hJ).symm
  obtain ⟨n,hn⟩ := isPGroup_quotientAut_frattini_kernel hp ⟨a,hq⟩
  have hn' : a^(2^n) = 1 := congrArg Subtype.val hn
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 7 2).pow_right n)
    (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one hn'))


/-- Seven does not divide the automorphism order of the actual PSU₅(4)
Sylow coordinates. -/
theorem not_seven_dvd_coordinates_aut (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x^4)
    (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    ¬7 ∣ Nat.card (MulAut (Coordinates J)) := by
  let : Finite (Parameters J) := Finite.of_injective (fun u : Parameters J => (u.x,u.z))
    (fun _ _ h => Parameters.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let : Finite (Coordinates J) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  let : Finite (MulAut (Coordinates J)) := Finite.of_injective
    (fun a : MulAut (Coordinates J) => (a : Coordinates J → Coordinates J)) DFunLike.coe_injective
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro hd
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := MulAut (Coordinates J)) 7 hd
  have he := automorphism_seventh_power J hcard hconj c hc hJ a
    (ha ▸ pow_orderOf_eq_one a)
  rw [he,orderOf_one] at ha
  contradiction

/-- The obstruction applies to every Sylow in the marked projective group. -/
theorem not_seven_dvd_sylow_aut_of_equiv (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x^4) (hJ : J.form = 1)
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J) (P : Sylow 2 G) :
    ¬7 ∣ Nat.card (MulAut P) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := finite_projective J
  obtain ⟨c,hc⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective J 4
    hcard (fixed_card_four J hcard hconj) 1 (map_one _)
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let e₁ : P ≃* R := (P : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective
  let e₂ := R.equiv (unipotentSylowFour J hcard hconj c hc hJ)
  let e₃ := unipotentSylowFourEquivCoordinates J hcard hconj c hc hJ
  rw [Nat.card_congr (MulAut.congr (e₁.trans (e₂.trans e₃))).toEquiv]
  exact not_seven_dvd_coordinates_aut J hcard hconj c hc hJ

end Theory.SpecificGroups.UnitaryFive.Flag.Automorphisms
