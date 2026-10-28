module

public import Theory.GroupTheory.PGroup.NormalSubgroups

open scoped Pointwise

/-!
# A self-centralizing normal abelian subgroup in a finite two-group

Choose a maximal normal abelian subgroup `A`.  If its centralizer is larger,
pass to the quotient by `A`; a normal subgroup of order two in the image of the
centralizer lifts to a subgroup `B` containing `A`.  The lift is abelian because
it centralizes `A` and its quotient over `A` is cyclic, contradicting maximality.
-/

section

variable {P : Type*} [Group P] [Finite P]

/-- Extend a normal abelian subgroup of a finite two-group to a maximal one,
which is self-centralizing. -/
public theorem exists_normal_abelian_selfCentralizing_containing
    (hP : IsPGroup 2 P) (E : Subgroup P)
    (hEn : E.Normal) (hEc : IsMulCommutative E) :
    ∃ A : Subgroup P, E ≤ A ∧ A.Normal ∧ IsMulCommutative A ∧
      (∀ B : Subgroup P, B.Normal → IsMulCommutative B → A ≤ B → B = A) ∧
      Subgroup.centralizer (A : Set P) ≤ A := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let _ : Fact (IsPGroup 2 P) := ⟨hP⟩
  let good : Subgroup P → Prop := fun H => H.Normal ∧ IsMulCommutative H
  obtain ⟨A, hA_le, hAmax⟩ :=
    Finite.exists_le_maximal (p := good)
      (a := E) ⟨hEn, hEc⟩
  have hAgood : good A := hAmax.1
  let _ : A.Normal := hAgood.1
  let _ : IsMulCommutative A := hAgood.2
  let C : Subgroup P := Subgroup.centralizer (A : Set P)
  let _ : C.Normal := inferInstance
  have hAC : A ≤ C := Subgroup.le_centralizer A
  have hCA : C ≤ A := by
    by_contra hnot
    change ¬ (∀ ⦃x : P⦄, x ∈ C → x ∈ A) at hnot
    push Not at hnot
    obtain ⟨c, hcC, hcA⟩ := hnot
    let q : P →* (P ⧸ A) := QuotientGroup.mk' A
    let _ : Fact (IsPGroup 2 (P ⧸ A)) :=
      ⟨(Fact.out : IsPGroup 2 P).to_quotient A⟩
    let Cbar : Subgroup (P ⧸ A) := C.map q
    let _ : Cbar.Normal := by
      dsimp [Cbar, q]
      exact QuotientGroup.map_normal A C
    have hqC : q c ∈ Cbar := by
      exact ⟨c, hcC, rfl⟩
    have hqne : q c ≠ 1 := by
      intro h
      apply hcA
      exact (QuotientGroup.eq_one_iff (N := A) (x := c)).mp h
    have hCbar_nontrivial : Nontrivial Cbar := by
      refine ⟨⟨1, Cbar.one_mem⟩, ⟨q c, hqC⟩, ?_⟩
      intro he
      exact hqne (Subtype.ext_iff.mp he).symm
    have hCbarp : IsPGroup 2 Cbar :=
      (Fact.out : IsPGroup 2 (P ⧸ A)).to_subgroup Cbar
    obtain ⟨k, hk⟩ := hCbarp.exists_card_eq
    have hkpos : 1 ≤ k := by
      have hkz : k ≠ 0 := by
        intro hk0
        have hcard_one : Nat.card Cbar = 1 := by simpa [hk0] using hk
        have hcard_gt : 1 < Nat.card Cbar :=
          Finite.one_lt_card_iff_nontrivial.mpr hCbar_nontrivial
        exact (Nat.ne_of_gt hcard_gt) hcard_one
      exact Nat.one_le_iff_ne_zero.mpr hkz
    obtain ⟨Zbar, hZbarN, hZbar_le, hZbarcard⟩ :=
      exists_normal_subgroup_card_pow_of_normal (p := 2) (N := Cbar)
        (inferInstance : Cbar.Normal) hk 1 hkpos
    let _ : Zbar.Normal := hZbarN
    let B : Subgroup P := Zbar.comap q
    have hAB : A ≤ B := by
      intro a ha
      have hqa : q a = 1 := (QuotientGroup.eq_one_iff (N := A) (x := a)).mpr ha
      change q a ∈ Zbar
      rw [hqa]
      exact Zbar.one_mem
    have hBC : B ≤ C := by
      intro x hx
      rcases hZbar_le hx with ⟨c', hc'C, hqc'⟩
      have hker : x * c'⁻¹ ∈ A := by
        apply (QuotientGroup.eq_one_iff (N := A) (x := x * c'⁻¹)).mp
        change q (x * c'⁻¹) = 1
        rw [map_mul, map_inv, hqc']
        simp
      have hxc : x * c'⁻¹ ∈ C := hAC hker
      have hc'inv : c' ∈ C := hc'C
      simpa [mul_assoc] using C.mul_mem hxc hc'inv
    have hBproper : A ≤ B := hAB
    have hBcomm : IsMulCommutative B := by
      let f₀ : B →* (P ⧸ A) := q.comp B.subtype
      have hf₀ : ∀ x : B, f₀ x ∈ Zbar := by
        intro x
        exact x.property
      let f : B →* Zbar := f₀.codRestrict Zbar hf₀
      let _ : IsCyclic Zbar := isCyclic_of_prime_card hZbarcard
      have hfker : f.ker ≤ Subgroup.center B := by
        intro x hx
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        have hxa : (x : P) ∈ A := by
          rw [MonoidHom.mem_ker] at hx
          have hxq : q (x : P) = 1 := by
            simpa [f, f₀] using congrArg Subtype.val hx
          exact (QuotientGroup.eq_one_iff (N := A) (x := (x : P))).mp hxq
        have hyc : (y : P) ∈ C := hBC y.property
        exact (Subgroup.mem_centralizer_iff.mp hyc) (x : P) hxa |>.symm
      exact f.isMulCommutative_of_isCyclic_of_ker_le_center hfker
    have hBgood : good B := ⟨inferInstance, hBcomm⟩
    have hBA : B ≤ A := hAmax.2 hBgood hAB
    have hZbar_nontrivial : Nontrivial Zbar := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      rw [hZbarcard]
      norm_num
    obtain ⟨z, hz⟩ : ∃ z : Zbar, z ≠ 1 := by
      by_contra h
      push Not at h
      exact (not_subsingleton_iff_nontrivial.mpr hZbar_nontrivial)
        ⟨fun x y => (h x).trans (h y).symm⟩
    rcases hZbar_le z.property with ⟨c', hc'C, hqc'⟩
    have hc'A : c' ∉ A := by
      intro hc'A
      have : q c' = 1 := (QuotientGroup.eq_one_iff (N := A) (x := c')).mpr hc'A
      apply hz
      apply Subtype.ext
      exact hqc'.symm.trans this
    have hc'B : c' ∈ B := by
      change q c' ∈ Zbar
      rw [hqc']
      exact z.property
    exact hc'A (hBA hc'B)
  exact ⟨A, hA_le, hAgood.1, hAgood.2,
    fun B hBn hBc hAB => le_antisymm (hAmax.2 ⟨hBn, hBc⟩ hAB) hAB, hCA⟩

/-- A finite `2`-group has a normal abelian self-centralizing subgroup. -/
public theorem exists_normal_abelian_selfCentralizing
    (hP : IsPGroup 2 P) :
    ∃ A : Subgroup P, A.Normal ∧ IsMulCommutative A ∧
      Subgroup.centralizer (A : Set P) ≤ A := by
  obtain ⟨A, -, hAn, hAc, -, hCA⟩ :=
    exists_normal_abelian_selfCentralizing_containing hP ⊥ inferInstance inferInstance
  exact ⟨A, hAn, hAc, hCA⟩

end
