module

public import Theory.GroupTheory.PGroup.NormalEightCriticalSubgroup
public import Theory.GroupTheory.PGroup.NormalEightCentralAction
public import Theory.GroupTheory.PGroup.HomocyclicDeepInvolution
public import Theory.GroupTheory.PGroup.ThreeInvolutionAutomorphism
public import Theory.GroupTheory.PGroup.ClassTwoThreeInvolutionExponent
public import Theory.GroupTheory.PGroup.HomocyclicLargeBaseFourthRoots

/-!
# Index two over a large homocyclic abelian critical subgroup

Let `C` be an abelian critical subgroup of a finite two-group with central
first omega of order four and no normal elementary abelian subgroup of
order at least eight. If `C` is homocyclic of rank two and exponent at least
eight, an ambient cubic automorphism acting freely on `C` forces `[P : C] = 2`.

First, a deep involution centralizing four-torsion belongs to `C`, by the
normal-eight obstruction. Thus the four-torsion centralizer has exactly the
three central involutions of `C`. The cubic automorphism is fixed-point-free
on this centralizer, so Neumann's theorem gives class at most two. The
three-involution exponent theorem makes a nonabelian such group have exponent
at most four, contradicting the elements of order at least eight in `C`.
Consequently the centralizer is abelian and self-centralization gives `C`.

Faithfulness on four-torsion makes the full conjugation image elementary
abelian of order at most four. An image of order four has unequal action-norm
fiber counts on the three involutions of `C`. Cubic symmetry makes these counts
equal, excluding that image. Noncommutativity excludes the trivial image.

Source: MacWilliams, *On 2-groups with no normal abelian subgroups of rank 3,
and their occurrence as Sylow 2-subgroups of finite simple groups*, Trans.
AMS 150 (1970), Case 1.2, assertions (xvii)–(xix), printed pp.377–379,
DOI 10.1090/S0002-9947-1970-0276324-3. The proof here replaces the metacyclicity
citation in (xvii) with the checked three-involution argument and uses the
binary matrix norm-profile calculation for the final index bound. The
exponent restriction is essential; no exponent-four conclusion is asserted.
-/

open Subgroup

namespace IsCriticalPSubgroup

/-- Involutions centralizing four-torsion belong to the large homocyclic critical subgroup. -/
public theorem involution_mem_of_fixing_four_torsion
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (n : ℕ) (hn : 3 ≤ n)
    (e : C ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (x : P) (hx : x ^ 2 = 1)
    (hfour : ∀ c : C, c ^ 4 = 1 → x * c * x⁻¹ = c) : x ∈ C := by
  let : C.Characteristic := hC.characteristic
  have hCC : centralizer (C : Set P) ≤ C := by
    rw [hC.centralizer_eq]
    exact map_subtype_le _
  let f : P →* MulAut C := MulAut.conjNormal
  have hdeep := IsPGroup.deep_involution_of_homocyclic_fixing_four_torsion n hn e (f x)
    (by rw [← map_pow, hx, map_one])
    (fun c hc => Subtype.ext (hfour c hc))
  apply IsPGroup.involution_mem_normal_abelian_of_central_action_of_no_normal_eight
    hno hZ C hCC x hx
  · intro g
    exact hdeep.1 (f g) (fun c hc =>
      IsPGroup.conjNormal_fixed_of_square_eq_one_of_no_normal_eight hno hZ C hCC g c hc)
  · intro c hc hi
    exact congrArg Subtype.val (hdeep.2 ⟨c, hc⟩ (Subtype.ext hi))

private theorem orbit_of_three_involutions
    {K : Type*} [Group K] [Finite K]
    (hthree : Nat.card {x : K // orderOf x = 2} = 3)
    (a : MulAut K) (hfree : MonoidHom.FixedPointFree a) :
    ∀ x y : K, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (a ^ k) x = y := by
  classical
  let I := {x : K // orderOf x = 2}
  let : Fintype I := Fintype.ofFinite I
  let e : I ≃ Fin 3 := Fintype.equivFinOfCardEq
    (by simpa only [Nat.card_eq_fintype_card] using hthree)
  let p : Equiv.Perm I := Equiv.Perm.subtypePerm a.toEquiv (fun x => by
    change orderOf (a x) = 2 ↔ orderOf x = 2
    rw [a.orderOf_eq])
  let f : Equiv.Perm (Fin 3) := (e.symm.trans p).trans e
  have hf (x : I) : f (e x) = e ⟨a x, (a.orderOf_eq x).trans x.property⟩ := by
    simp [f, p]
    rfl
  have hnf (i : Fin 3) : f i ≠ i := by
    obtain ⟨x, rfl⟩ := e.surjective i
    intro hi
    rw [hf] at hi
    have hx := hfree x (congrArg Subtype.val (e.injective hi))
    have ho := x.property
    rw [hx, orderOf_one] at ho
    omega
  have hsmall : ∀ f : Equiv.Perm (Fin 3), (∀ i, f i ≠ i) →
      ∀ i j, j = i ∨ j = f i ∨ j = f (f i) := by decide
  intro x y hx hy
  rcases hsmall f hnf (e ⟨x, hx⟩) (e ⟨y, hy⟩) with h | h | h
  · exact ⟨0, (congrArg Subtype.val (e.injective h)).symm⟩
  · rw [hf] at h
    exact ⟨1, by simpa using (congrArg Subtype.val (e.injective h)).symm⟩
  · rw [hf, hf] at h
    exact ⟨2, by simpa only [pow_two, MulAut.mul_apply] using (congrArg Subtype.val (e.injective h)).symm⟩

private theorem norm_fiber_card_eq
    {D : Type*} [Group D] [Finite D] (A : Subgroup (MulAut D))
    (a : MulAut D) (hnorm : ∀ b ∈ A, a * b * a⁻¹ ∈ A) (x : D) :
    Nat.card {t : A × D // (t.2 * ((t.1 : MulAut D) t.2)) ^ 2 = x} =
      Nat.card {t : A × D // (t.2 * ((t.1 : MulAut D) t.2)) ^ 2 = a x} := by
  classical
  let F : A × D → A × D := fun t =>
    (⟨a * t.1 * a⁻¹, hnorm t.1 t.1.property⟩, a t.2)
  have hi : Function.Injective F := by
    intro t u h
    apply Prod.ext
    · apply Subtype.ext
      apply (MulAut.conj a).injective
      exact congrArg (fun t : A × D => (t.1 : MulAut D)) h
    · exact a.injective (congrArg Prod.snd h)
  let E : A × D ≃ A × D := Equiv.ofBijective F ⟨hi, Finite.surjective_of_injective hi⟩
  apply Nat.card_congr (Equiv.subtypeEquiv E ?_)
  intro t
  change (t.2 * (t.1 : MulAut D) t.2) ^ 2 = x ↔
    (a t.2 * (a * (t.1 : MulAut D) * a⁻¹) (a t.2)) ^ 2 = a x
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  rw [← map_mul, ← map_pow, a.injective.eq_iff]

/-- Cubic symmetry forces faithfulness on four-torsion for a large homocyclic
abelian critical subgroup. -/
public theorem centralizer_four_torsion_eq
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (n : ℕ) (hn : 3 ≤ n)
    (e : C ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (a : MulAut P) (ha : orderOf a = 3)
    (hfree : ∀ c ∈ C, a c = c → c = 1) :
    centralizer (((omega C (p := 2) 2).map C.subtype : Subgroup P) : Set P) = C := by
  classical
  let : C.Characteristic := hC.characteristic
  let O := omega C (p := 2) 2
  let : O.Characteristic := omega_characteristic C 2
  let B := O.map C.subtype
  let : B.Characteristic := inferInstance
  let K := centralizer (B : Set P)
  let : K.Characteristic := inferInstance
  have hCK : C ≤ K := C.le_centralizer.trans (centralizer_le (map_subtype_le O))
  have hmem (x : K) (hx : x ^ 2 = 1) : (x : P) ∈ C := by
    apply hC.involution_mem_of_fixing_four_torsion hno hZ n hn e x
      (congrArg Subtype.val hx)
    intro c hc
    have hm : (c : P) ∈ B := ⟨c, subset_closure hc, rfl⟩
    rw [(x.property c hm).symm, mul_inv_cancel_right]
  have hcentral (x : K) (hx : x ^ 2 = 1) : x ∈ center K := by
    have hc := map_subtype_le _ (hC.mem_omega_center_of_square_eq_one hno hZ
      (hmem x hx) (congrArg Subtype.val hx))
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hc y)
  have hthree : Nat.card {x : K // orderOf x = 2} = 3 := by
    let ei : {x : K // orderOf x = 2} ≃ {x : C // orderOf x = 2} :=
      { toFun := fun x => ⟨⟨x.val, hmem x.val (by
          simpa only [x.property] using pow_orderOf_eq_one x.val)⟩,
          (orderOf_coe _).symm.trans ((orderOf_coe x.val).trans x.property)⟩
        invFun := fun x => ⟨⟨x.val, hCK x.val.property⟩,
          (orderOf_coe _).symm.trans ((orderOf_coe x.val).trans x.property)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr ei]
    exact hC.card_involutions_eq_three hno hZ
  let b := MulAut.characteristic K a
  have hbfree : MonoidHom.FixedPointFree b := by
    apply (hP.to_subgroup K).fixedPointFree_of_no_fixed_prime_order b
    intro x hx hfix
    have hx2 : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
    have he : (x : P) = 1 := hfree x (hmem x hx2) (congrArg Subtype.val hfix)
    exact (orderOf_eq_prime_iff.mp hx).2 (Subtype.ext he)
  have hlarge : ∃ c : C, c ^ 4 ≠ 1 := by
    let c := e.symm (Multiplicative.ofAdd 1, 1)
    refine ⟨c, ?_⟩
    intro hc
    have he := congrArg (fun c : C => (e c).1.toAdd) hc
    have hz : (4 : ZMod (2 ^ n)) = 0 := by
      simpa [c, map_pow, toAdd_pow, nsmul_eq_mul] using he
    have hd : 2 ^ n ∣ 4 := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hle : 8 ≤ 2 ^ n := by
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hn
    have := Nat.le_of_dvd (by decide : 0 < 4) hd
    omega
  have hbne : b ≠ 1 := by
    intro he
    obtain ⟨c, hc⟩ := hlarge
    have hfix : b (⟨c, hCK c.property⟩ : K) = ⟨c, hCK c.property⟩ := by rw [he]; rfl
    have hz := hbfree _ hfix
    have hc1 : c = 1 := Subtype.ext (congrArg (fun x : K => (x : P)) hz)
    exact hc (by rw [hc1, one_pow])
  have hb : orderOf b = 3 := by
    apply orderOf_eq_prime
    · change (MulAut.characteristic K a) ^ 3 = 1
      rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
    · exact hbne
  have hab : IsMulCommutative K := by
    by_contra hnonab
    have hexp := (hP.to_subgroup K).exponent_four_of_class_two_of_transitive_three_involutions
      hnonab hcentral hthree (by
        intro x y hx hy
        obtain ⟨i, hi⟩ := orbit_of_three_involutions hthree b hbfree x y hx hy
        exact ⟨b ^ i, hi⟩)
      (b.commutator_le_center_of_orderOf_eq_three_of_fixedPointFree hb hbfree)
    obtain ⟨c, hc⟩ := hlarge
    have hh : (c : P) ^ 4 = 1 := congrArg (fun x : K => (x : P))
      (hexp ⟨c, hCK c.property⟩)
    exact hc (Subtype.ext hh)
  let : IsMulCommutative K := hab
  apply le_antisymm _ hCK
  have hCC : centralizer (C : Set P) ≤ C := by
    rw [hC.centralizer_eq]
    exact map_subtype_le _
  exact (K.le_centralizer.trans (centralizer_le hCK)).trans hCC

/-- A nonabelian two-group with a large homocyclic abelian critical subgroup
and a fixed-point-free cubic action on it has index two over that subgroup. -/
public theorem index_eq_two_of_large_homocyclic
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnonab : ¬ IsMulCommutative P) {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (n : ℕ) (hn : 3 ≤ n)
    (e : C ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (a : MulAut P) (ha : orderOf a = 3)
    (hfree : ∀ c ∈ C, a c = c → c = 1) : C.index = 2 := by
  classical
  let : C.Characteristic := hC.characteristic
  let f : P →* MulAut C := MulAut.conjNormal
  let A := f.range
  have hCC : centralizer (C : Set P) ≤ C := by
    rw [hC.centralizer_eq]
    exact map_subtype_le _
  have hker : f.ker = C := by
    apply le_antisymm
    · intro x hx
      apply hCC
      intro c hc
      have hh := congrArg (fun b : MulAut C => (b ⟨c, hc⟩ : P))
        (MonoidHom.mem_ker.mp hx)
      change x * c * x⁻¹ = c at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro x hx
      apply MonoidHom.mem_ker.mpr
      ext c
      change x * (c : P) * x⁻¹ = c
      rw [(C.le_centralizer hx c c.property).symm, mul_inv_cancel_right]
  have hfix : ∀ b ∈ A, ∀ c : C, c ^ 2 = 1 → b c = c := by
    rintro b ⟨g, rfl⟩ c hc
    exact IsPGroup.conjNormal_fixed_of_square_eq_one_of_no_normal_eight hno hZ C hCC g c hc
  have hfaith : ∀ b ∈ A, (∀ c : C, c ^ 4 = 1 → b c = c) → b = 1 := by
    rintro b ⟨g, rfl⟩ hg
    apply MonoidHom.mem_ker.mp
    rw [hker, ← hC.centralizer_four_torsion_eq hP hno hZ n hn e a ha hfree]
    intro c hc
    obtain ⟨d, hd, rfl⟩ := hc
    have hdfix : f g d = d := by
      apply (closure_le ((f g).toMonoidHom.eqLocus (MonoidHom.id C))).mpr ?_ hd
      intro z hz
      exact hg z hz
    have hh := congrArg Subtype.val hdfix
    change g * (d : P) * g⁻¹ = d at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let : IsElementaryAbelian 2 A :=
    HomocyclicFourTorsion.elementary_of_homocyclic_four_torsion n hn e A hfix hfaith
  have hle : Nat.card A ≤ 4 :=
    HomocyclicFourTorsion.card_le_four_of_homocyclic_elementary_four_torsion n hn e A hfix hfaith
  have hi : C.index = Nat.card A :=
    (congrArg Subgroup.index hker).symm.trans (index_ker f)
  have hne1 : Nat.card A ≠ 1 := by
    intro h
    have htop : C = ⊤ := index_eq_one.mp (hi.trans h)
    have hCent : (⊤ : Subgroup P) ≤ center P := by
      intro x _
      apply mem_center_iff.mpr
      intro y
      exact C.le_centralizer (htop ▸ mem_top x) y (htop ▸ mem_top y)
    exact hnonab (center_eq_top_iff.mp (top_unique hCent))
  have hne4 : Nat.card A ≠ 4 := by
    intro h4
    obtain ⟨x, y, hx2, hx1, hy2, hy1, hneq⟩ :=
      HomocyclicFourNormProfile.exists_ne_norm_fiber_card_of_homocyclic n hn e A h4 hfix hfaith
    let r := MulAut.characteristic C a
    have hr : MonoidHom.FixedPointFree r := by
      intro c hc
      exact Subtype.ext (hfree c c.property (congrArg Subtype.val hc))
    obtain ⟨i, hxy⟩ := orbit_of_three_involutions
      (hC.card_involutions_eq_three hno hZ) r hr x y
      (orderOf_eq_prime hx2 hx1) (orderOf_eq_prime hy2 hy1)
    have hnorm : ∀ b ∈ A, (r ^ i) * b * (r ^ i)⁻¹ ∈ A := by
      rintro b ⟨g, rfl⟩
      refine ⟨(a ^ i) g, ?_⟩
      have he : r ^ i = MulAut.characteristic C (a ^ i) := (map_pow _ _ _).symm
      rw [he]
      ext c
      change (a ^ i) g * (c : P) * ((a ^ i) g)⁻¹ =
        (a ^ i) (g * (a ^ i)⁻¹ (c : P) * g⁻¹)
      simp only [map_mul, map_inv, MulAut.apply_inv_self]
    apply hneq
    rw [← hxy]
    exact norm_fiber_card_eq A (r ^ i) hnorm x
  have hdiv : 2 ∣ Nat.card A :=
    ((hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective).card_eq_or_dvd).resolve_left hne1
  rw [hi]
  have hpos : 0 < Nat.card A := Nat.card_pos
  omega

end IsCriticalPSubgroup
