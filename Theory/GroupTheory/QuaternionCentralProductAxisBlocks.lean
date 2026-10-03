module

public import Theory.GroupTheory.CyclicFourSubgroupAction
public import Theory.GroupTheory.QuaternionCentralProductFactors
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Tactic.FinCases

/-!
# The two triples of quaternion axes

For commuting quaternion factors of order eight with common involution, every
order-four element of their join lies in one factor.  Each factor has exactly
three cyclic subgroups of order four.  The resulting six axes are intrinsic in
pairs, since every automorphism maps a quaternion factor to one of the two
factors.  This gives the block-permutation input for the outer wreath action.

The central-product argument is the axis numbering used in Janko--Thompson,
Math. Z. 113 (1970), §4, printed p.390.
-/

namespace Subgroup

private abbrev Q := QuaternionGroup 2

private theorem q_axis_classification (x : Q) (hx : orderOf x = 4) :
    zpowers x = zpowers (QuaternionGroup.a 1) ∨
      zpowers x = zpowers (QuaternionGroup.xa 0) ∨
      zpowers x = zpowers (QuaternionGroup.xa 1) := by
  rcases x with x | x
  · fin_cases x
    · change orderOf (QuaternionGroup.a (n := 2) (0 : ZMod 4) : Q) = 4 at hx
      have h : orderOf (QuaternionGroup.a (n := 2) (0 : ZMod 4) : Q) = 1 := by simp
      omega
    · exact Or.inl (by
        change zpowers (QuaternionGroup.a (n := 2) (1 : ZMod 4)) =
          zpowers (QuaternionGroup.a 1)
        rfl)
    · change orderOf (QuaternionGroup.a (n := 2) (2 : ZMod 4) : Q) = 4 at hx
      have h : orderOf (QuaternionGroup.a (n := 2) (2 : ZMod 4) : Q) = 2 := by
        rw [QuaternionGroup.orderOf_a]
        change 4 / Nat.gcd 4 2 = 2
        decide
      omega
    · exact Or.inl (by
        change zpowers (QuaternionGroup.a (n := 2) (3 : ZMod 4)) =
          zpowers (QuaternionGroup.a 1)
        rw [show (QuaternionGroup.a (n := 2) (3 : ZMod 4) : Q) =
          (QuaternionGroup.a 1)⁻¹ by decide, zpowers_inv])
  · fin_cases x
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl (by
        change zpowers (QuaternionGroup.xa (n := 2) (2 : ZMod 4)) =
          zpowers (QuaternionGroup.xa 0)
        rw [show (QuaternionGroup.xa (n := 2) (2 : ZMod 4) : Q) =
          (QuaternionGroup.xa 0)⁻¹ by decide, zpowers_inv]))
    · exact Or.inr (Or.inr (by
        change zpowers (QuaternionGroup.xa (n := 2) (3 : ZMod 4)) =
          zpowers (QuaternionGroup.xa 1)
        rw [show (QuaternionGroup.xa (n := 2) (3 : ZMod 4) : Q) =
          (QuaternionGroup.xa 1)⁻¹ by decide, zpowers_inv]))

private def q_axis (i : Fin 3) : Q :=
  if i = 0 then QuaternionGroup.a 1
  else if i = 1 then QuaternionGroup.xa 0
  else QuaternionGroup.xa 1

private theorem zmod2_cases (l : Multiplicative (ZMod 2)) :
    l = 1 ∨ l = Multiplicative.ofAdd 1 := by
  revert l
  decide

private theorem q_axis_order (i : Fin 3) : orderOf (q_axis i) = 4 := by
  fin_cases i <;> simp [q_axis]

private theorem q_axis_noncomm (i j : Fin 3) (hij : i ≠ j) :
    q_axis i * q_axis j ≠ q_axis j * q_axis i := by
  fin_cases i <;> fin_cases j <;> simp [q_axis] at hij ⊢
  all_goals decide

private theorem q_axis_ne (i j : Fin 3) (hij : i ≠ j) :
    zpowers (q_axis i) ≠ zpowers (q_axis j) := by
  intro heq
  have hxi : q_axis i ∈ zpowers (q_axis j) := heq ▸ mem_zpowers _
  have hxj : q_axis j ∈ zpowers (q_axis j) := mem_zpowers _
  have : IsCyclic (zpowers (q_axis j)) := inferInstance
  have hc := (IsMulCommutative.is_comm (M := zpowers (q_axis j))).comm
    ⟨q_axis i, hxi⟩ ⟨q_axis j, hxj⟩
  exact q_axis_noncomm i j hij (congrArg Subtype.val hc)


private theorem quaternion_square_dichotomy_ext {G : Type*} [Group G] (B : Subgroup G)
    (e : B ≃* QuaternionGroup 2) (z : G) (hz : z ∈ B)
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (b : G) (hb : b ∈ B) :
    (b = 1 ∨ b = z) ∨ b ^ 2 = z := by
  have hfinite : ∀ z b : QuaternionGroup 2, z ≠ 1 → z ^ 2 = 1 →
      (b = 1 ∨ b = z) ∨ b ^ 2 = z := by decide
  let zz : B := ⟨z, hz⟩
  let bb : B := ⟨b, hb⟩
  have hz1' : e zz ≠ 1 := by
    intro hh
    apply hz1
    exact congrArg Subtype.val (e.injective (hh.trans e.map_one.symm))
  have hz2' : (e zz) ^ 2 = 1 := by
    rw [← map_pow]
    have hh : zz ^ 2 = 1 := Subtype.ext hz2
    rw [hh, map_one]
  rcases hfinite (e zz) (e bb) hz1' hz2' with (hb1 | hbz) | hb2
  · exact Or.inl (Or.inl (congrArg Subtype.val
      (e.injective (hb1.trans e.map_one.symm))))
  · exact Or.inl (Or.inr (congrArg Subtype.val (e.injective hbz)))
  · apply Or.inr
    have hh : bb ^ 2 = zz := e.injective (by rw [map_pow]; exact hb2)
    exact congrArg Subtype.val hh

private theorem order_four_mem_factor_ext {G : Type*} [Group G] [Finite G]
    (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (x : G) (hx : x ∈ B ⊔ C) (hx4 : orderOf x = 4) : x ∈ B ∨ x ∈ C := by
  obtain ⟨eB⟩ := hB
  obtain ⟨eC⟩ := hC
  obtain ⟨zz, hz1, _⟩ := (Nat.card_eq_two_iff' (1 : (B ⊓ C : Subgroup G))).mp hinter
  let z : G := zz
  have hz1' : z ≠ 1 := fun hh => hz1 (Subtype.ext hh)
  have hz2 : z ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := zz)
    rw [hinter] at hh
    exact congrArg Subtype.val hh
  have hnorm : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (hcomm b hb c hc).symm
  have hx' : x ∈ (↑(B ⊔ C) : Set G) := hx
  rw [coe_mul_of_left_le_normalizer_right B C hnorm] at hx'
  obtain ⟨b, hb, c, hc, rfl⟩ := hx'
  rcases quaternion_square_dichotomy_ext B eB z zz.property.1 hz1' hz2 b hb with
    (hb1 | hbz) | hb2
  · exact Or.inr (by simpa [hb1] using hc)
  · exact Or.inr (C.mul_mem (hbz ▸ zz.property.2) hc)
  rcases quaternion_square_dichotomy_ext C eC z zz.property.2 hz1' hz2 c hc with
    (hc1 | hcz) | hc2
  · exact Or.inl (by simpa [hc1] using hb)
  · exact Or.inl (B.mul_mem hb (hcz ▸ zz.property.1))
  have hsq : (b * c) ^ 2 = 1 := by
    rw [(show Commute b c from hcomm b hb c hc).mul_pow, hb2, hc2, ← pow_two, hz2]
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [hx4] at hdvd
  norm_num at hdvd

private theorem q_axis_exists (x : Q) (hx : orderOf x = 4) :
    ∃ i : Fin 3, zpowers x = zpowers (q_axis i) := by
  rcases q_axis_classification x hx with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

/-- The intrinsic six axes, numbered as two triples permuted by automorphisms. -/
public theorem exists_cyclicFourSubgroups_equiv_fin3_mul_zmod2
    {H : Type*} [Group H] [Finite H]
    (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hjoin : B ⊔ C = ⊤) :
    ∃ e : CyclicFourSubgroups H ≃ (Fin 3 × Multiplicative (ZMod 2)),
      ∀ a : MulAut H, ∃ q : Multiplicative (ZMod 2),
        ∀ D : CyclicFourSubgroups H,
          (e (cyclicFourAction a D)).2 = q * (e D).2 := by
  classical
  obtain ⟨eB⟩ := hB
  obtain ⟨eC⟩ := hC
  let φB : Q →* H := B.subtype.comp eB.symm.toMonoidHom
  let φC : Q →* H := C.subtype.comp eC.symm.toMonoidHom
  have hφB : Function.Injective φB := B.subtype_injective.comp eB.symm.injective
  have hφC : Function.Injective φC := C.subtype_injective.comp eC.symm.injective
  let axis (φ : Q →* H) (hφ : Function.Injective φ) (i : Fin 3) :
      CyclicFourSubgroups H :=
    ⟨zpowers (φ (q_axis i)), φ (q_axis i),
      (orderOf_injective φ hφ (q_axis i)).trans (q_axis_order i), rfl⟩
  have haxis_inj (φ : Q →* H) (hφ : Function.Injective φ) :
      Function.Injective (axis φ hφ) := by
    intro i j hij
    have he := congrArg Subtype.val hij
    change zpowers (φ (q_axis i)) = zpowers (φ (q_axis j)) at he
    rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers] at he
    have h := map_injective hφ he
    by_contra hn
    exact q_axis_ne i j hn h
  have haxisB (i : Fin 3) : (axis φB hφB i).val ≤ B :=
    zpowers_le.mpr (eB.symm (q_axis i)).property
  have haxisC (i : Fin 3) : (axis φC hφC i).val ≤ C :=
    zpowers_le.mpr (eC.symm (q_axis i)).property
  have hnoboth (D : CyclicFourSubgroups H) : ¬ (D.val ≤ B ∧ D.val ≤ C) := by
    rintro ⟨hb, hc⟩
    have hd : Nat.card D.val = 4 := by
      obtain ⟨x, hx, he⟩ := D.property
      rw [he, Nat.card_zpowers, hx]
    have h := card_le_of_le (le_inf hb hc)
    rw [hd, hinter] at h
    omega
  have hcross (i j : Fin 3) : axis φB hφB i ≠ axis φC hφC j := by
    intro h
    exact hnoboth _ ⟨haxisB i, h ▸ haxisC j⟩
  let f : (Fin 3 × Multiplicative (ZMod 2)) → CyclicFourSubgroups H :=
    fun x => if x.2 = 1 then axis φB hφB x.1 else axis φC hφC x.1
  have hf_inj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x.2 = 1 <;> by_cases hy : y.2 = 1
    · have hi : x.1 = y.1 := haxis_inj φB hφB (by simpa [f, hx, hy] using hxy)
      exact Prod.ext hi (hx.trans hy.symm)
    · exact (hcross x.1 y.1 (by simpa [f, hx, hy] using hxy)).elim
    · exact (hcross y.1 x.1 (by simpa [f, hx, hy] using hxy.symm)).elim
    · have hi : x.1 = y.1 := haxis_inj φC hφC (by simpa [f, hx, hy] using hxy)
      exact Prod.ext hi (((zmod2_cases x.2).resolve_left hx).trans
        ((zmod2_cases y.2).resolve_left hy).symm)
  have hsurj_factor (K : Subgroup H) (eK : K ≃* Q) (x : H) (hx : x ∈ K)
      (hx4 : orderOf x = 4) :
      ∃ i, zpowers x = zpowers ((K.subtype.comp eK.symm.toMonoidHom) (q_axis i)) := by
    let y : Q := eK ⟨x, hx⟩
    have hy : orderOf y = 4 := by
      rw [eK.orderOf_eq, ← orderOf_injective K.subtype K.subtype_injective]
      exact hx4
    obtain ⟨i, hi⟩ := q_axis_exists y hy
    refine ⟨i, ?_⟩
    have hh := congrArg (fun L : Subgroup Q => L.map (K.subtype.comp eK.symm.toMonoidHom)) hi
    simpa [MonoidHom.map_zpowers, y] using hh
  have hf_surj : Function.Surjective f := by
    intro D
    obtain ⟨x, hx4, hDx⟩ := D.property
    have hxjoin : x ∈ B ⊔ C := by rw [hjoin]; trivial
    rcases order_four_mem_factor_ext B C ⟨eB⟩ ⟨eC⟩ hinter hcomm x hxjoin hx4 with hxB | hxC
    · obtain ⟨i, hi⟩ := hsurj_factor B eB x hxB hx4
      refine ⟨(i, 1), Subtype.ext ?_⟩
      change (f (i, 1)).val = D.val
      simpa [f, axis, hDx, φB] using hi.symm
    · obtain ⟨i, hi⟩ := hsurj_factor C eC x hxC hx4
      refine ⟨(i, Multiplicative.ofAdd 1), Subtype.ext ?_⟩
      have hn : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
      simpa [f, axis, hDx, hn, φC] using hi.symm
  let e : CyclicFourSubgroups H ≃ (Fin 3 × Multiplicative (ZMod 2)) :=
    (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm
  have hef (x) : e (f x) = x := e.apply_symm_apply x
  have hlabelB (D : CyclicFourSubgroups H) : (e D).2 = 1 ↔ D.val ≤ B := by
    obtain ⟨x, rfl⟩ := hf_surj D
    rw [hef]
    by_cases hx : x.2 = 1
    · simp only [hx, true_iff]
      simpa [f, hx] using haxisB x.1
    · simp only [hx, false_iff]
      intro hb
      exact hnoboth _ ⟨hb, by simpa [f, hx] using haxisC x.1⟩
  have hlabelC (D : CyclicFourSubgroups H) : (e D).2 ≠ 1 ↔ D.val ≤ C := by
    obtain ⟨x, rfl⟩ := hf_surj D
    rw [hef]
    by_cases hx : x.2 = 1
    · constructor
      · intro hn; exact (hn hx).elim
      · intro hc
        exact (hnoboth _ ⟨by simpa [f, hx] using haxisB x.1, hc⟩).elim
    · exact ⟨fun _ => by simpa [f, hx] using haxisC x.1, fun _ => hx⟩
  have hBne : B ≠ C := by
    intro h
    exact hnoboth (axis φB hφB 0) ⟨haxisB 0, h ▸ haxisB 0⟩
  refine ⟨e, ?_⟩
  intro a
  have himage (K : Subgroup H) (eK : K ≃* Q) :
      K.map a.toMonoidHom = B ∨ K.map a.toMonoidHom = C := by
    apply quaternion_subgroup_eq_factor B C _ ⟨eB⟩ ⟨eC⟩ hinter hcomm
    · exact ⟨(K.equivMapOfInjective a.toMonoidHom a.injective).symm.trans eK⟩
    · rw [hjoin]; exact le_top
  have hmap (D : CyclicFourSubgroups H) (K L : Subgroup H)
      (hD : D.val ≤ K) (hKL : K.map a.toMonoidHom = L) :
      (cyclicFourAction a D).val ≤ L := by
    rw [cyclicFourAction_apply_val, ← hKL]
    exact map_mono hD
  rcases himage B eB with hb | hb
  · have hc : C.map a.toMonoidHom = C := by
      rcases himage C eC with hc | hc
      · exact (hBne (map_injective a.injective (hb.trans hc.symm))).elim
      · exact hc
    refine ⟨1, fun D => ?_⟩
    rw [one_mul]
    by_cases hd : (e D).2 = 1
    · exact ((hlabelB _).mpr (hmap D B B ((hlabelB D).mp hd) hb)).trans hd.symm
    · have hd' : (e (cyclicFourAction a D)).2 ≠ 1 :=
        (hlabelC _).mpr (hmap D C C ((hlabelC D).mp hd) hc)
      exact ((zmod2_cases _).resolve_left hd').trans ((zmod2_cases _).resolve_left hd).symm
  · have hc : C.map a.toMonoidHom = B := by
      rcases himage C eC with hc | hc
      · exact hc
      · exact (hBne (map_injective a.injective (hb.trans hc.symm))).elim
    refine ⟨Multiplicative.ofAdd 1, fun D => ?_⟩
    by_cases hd : (e D).2 = 1
    · have hd' : (e (cyclicFourAction a D)).2 ≠ 1 :=
        (hlabelC _).mpr (hmap D B C ((hlabelB D).mp hd) hb)
      rw [hd, mul_one]
      exact (zmod2_cases _).resolve_left hd'
    · have hd' : (e (cyclicFourAction a D)).2 = 1 :=
        (hlabelB _).mpr (hmap D C B ((hlabelC D).mp hd) hc)
      rw [hd', (zmod2_cases _).resolve_left hd]
      decide

end Subgroup
