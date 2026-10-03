module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# A cyclic group extended by an inverting involution

A finite cyclic subgroup `R` together with an involution outside `R` which
inverts every element of `R` generates a dihedral group. We choose a cyclic
generator, map rotations and reflections explicitly, and establish the two
normal forms to prove bijectivity. The outside-subgroup condition separates
rotations from reflections.

This elementary presentation is used in Stellmacher (3.6)(a), Journal of
Algebra 190 (1997), p. 22. The involution must exist in the group under
consideration; this result does not lift involutions across quotients.
-/

open scoped Pointwise

universe u


private theorem mem_zpowers_involution_eq_one_or_self
    {X : Type u} [Group X] [Finite X] {s y : X}
    (hs : s ≠ 1 ∧ s ^ 2 = 1) (hy : y ∈ Subgroup.zpowers s) :
    y = 1 ∨ y = s := by
  classical
  have hsOrder : orderOf s = 2 :=
    orderOf_eq_prime hs.2 hs.1
  have hcard : Nat.card (Subgroup.zpowers s) = 2 := by
    rw [Nat.card_zpowers, hsOrder]
  obtain ⟨z, hz1, hzunique⟩ :=
    (Nat.card_eq_two_iff' (1 : Subgroup.zpowers s)).mp hcard
  by_cases hy1 : y = 1
  · exact Or.inl hy1
  · right
    let ys : Subgroup.zpowers s := ⟨y, hy⟩
    let ss : Subgroup.zpowers s := ⟨s, Subgroup.mem_zpowers s⟩
    have hys1 : ys ≠ 1 := by
      intro heq
      apply hy1
      exact congrArg Subtype.val heq
    have hss1 : ss ≠ 1 := by
      intro heq
      apply hs.1
      exact congrArg Subtype.val heq
    exact congrArg Subtype.val ((hzunique ys hys1).trans (hzunique ss hss1).symm)

public theorem Subgroup.nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted
    {X : Type u} [Group X] [Finite X]
    (R : Subgroup X) (s : X)
    (hRcyclic : IsCyclic R) (hs2 : s ^ 2 = 1)
    (hsnotR : s ∉ R)
    (hinv : ∀ r : X, r ∈ R → s * r * s⁻¹ = r⁻¹) :
    Nonempty (↑(R ⊔ Subgroup.zpowers s) ≃* DihedralGroup (Nat.card R)) := by
  classical
  have hs : s ≠ 1 ∧ s ^ 2 = 1 := ⟨fun h => hsnotR (h ▸ R.one_mem), hs2⟩
  let E : Subgroup X := R ⊔ Subgroup.zpowers s
  let _ : IsCyclic R := hRcyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := R)
  let eR : Multiplicative (ZMod (Nat.card R)) ≃* R :=
    zmodMulEquivOfGenerator hg (n := Nat.card R) rfl
  let rot (i : ZMod (Nat.card R)) : X := (eR (Multiplicative.ofAdd i) : R)
  have hrot_mem (i : ZMod (Nat.card R)) : rot i ∈ R :=
    (eR (Multiplicative.ofAdd i)).property
  have hrot_mul (i j : ZMod (Nat.card R)) : rot (i + j) = rot i * rot j := by
    exact congrArg Subtype.val (eR.map_mul (Multiplicative.ofAdd i) (Multiplicative.ofAdd j))
  have hrot_zero : rot 0 = 1 := by
    exact congrArg Subtype.val eR.map_one
  have hrot_neg (i : ZMod (Nat.card R)) : rot (-i) = (rot i)⁻¹ := by
    exact congrArg Subtype.val (eR.map_inv (Multiplicative.ofAdd i))
  have hsInv (i : ZMod (Nat.card R)) : s * rot i * s⁻¹ = rot (-i) := by
    rw [hinv (rot i) (hrot_mem i), hrot_neg]
  have hsSelf : s⁻¹ = s := by
    calc
      s⁻¹ = s⁻¹ * (s * s) := by rw [show s * s = 1 by simpa [pow_two] using hs.2]; simp
      _ = s := by group
  have hsSq : s * s = 1 := by simpa [pow_two] using hs.2
  have hrot_s (i : ZMod (Nat.card R)) : rot i * s = s * rot (-i) := by
    calc
      rot i * s = (s * s) * rot i * s := by rw [hsSq]; simp
      _ = s * (s * rot i * s⁻¹) := by rw [hsSelf]; group
      _ = s * rot (-i) := by rw [hsInv]
  let f : DihedralGroup (Nat.card R) → E := fun d =>
    match d with
    | DihedralGroup.r i => ⟨rot i, (le_sup_left : R ≤ E) (hrot_mem i)⟩
    | DihedralGroup.sr i => ⟨s * rot i,
        E.mul_mem ((le_sup_right : Subgroup.zpowers s ≤ E) (Subgroup.mem_zpowers s))
          ((le_sup_left : R ≤ E) (hrot_mem i))⟩
  have hf_one : f 1 = 1 := by
    apply Subtype.ext
    exact hrot_zero
  have hf_mul : ∀ d e, f (d * e) = f d * f e := by
    rintro (i | i) (j | j) <;> apply Subtype.ext <;> dsimp [f]
    · rw [hrot_mul]
    · rw [show j - i = (-i) + j by simp [sub_eq_add_neg, add_comm], hrot_mul]
      calc
        s * (rot (-i) * rot j) = (s * rot (-i)) * rot j := by group
        _ = (rot i * s) * rot j := by rw [hrot_s i]
        _ = rot i * (s * rot j) := by group
    · rw [hrot_mul]
      group
    · rw [show j - i = (-i) + j by simp [sub_eq_add_neg, add_comm], hrot_mul]
      calc
        rot (-i) * rot j = (s * s) * (rot (-i) * rot j) := by rw [hsSq]; simp
        _ = s * (s * rot (-i)) * rot j := by group
        _ = s * (rot i * s) * rot j := by rw [hrot_s i]
        _ = s * rot i * (s * rot j) := by group
  let F : DihedralGroup (Nat.card R) →* E :=
    { toFun := f
      map_one' := hf_one
      map_mul' := hf_mul }
  have hFsurj : Function.Surjective F := by
    intro x
    have hnorm : Subgroup.zpowers s ≤ Subgroup.normalizer (R : Set X) := by
      intro y hy
      rcases mem_zpowers_involution_eq_one_or_self hs hy with hy1 | hys
      · rw [hy1]
        simp
      · rw [hys]
        rw [Subgroup.mem_normalizer_iff]
        intro r
        constructor <;> intro hr
        · rw [hinv r hr]
          exact R.inv_mem hr
        · have hback := hinv (s * r * s⁻¹) hr
          have hleft : s * (s * r * s⁻¹) * s⁻¹ = r := by
            rw [hsSelf]
            calc
              s * (s * r * s) * s = (s * s) * r * (s * s) := by group
              _ = r := by rw [hsSq]; simp
          rw [hleft] at hback
          rw [hback]
          exact R.inv_mem hr
    have hxprod : (x : X) ∈ (R : Set X) * (Subgroup.zpowers s : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left R (Subgroup.zpowers s) hnorm]
      exact x.property
    rcases hxprod with ⟨r, hr, y, hy, hry⟩
    rcases mem_zpowers_involution_eq_one_or_self hs hy with hy1 | hys
    · rw [hy1] at hry
      obtain ⟨i, hi⟩ := eR.surjective ⟨r, hr⟩
      refine ⟨DihedralGroup.r i.toAdd, ?_⟩
      apply Subtype.ext
      have hir : rot i.toAdd = r := by
        simpa [rot] using congrArg Subtype.val hi
      simpa [F, f, hir] using hry
    · rw [hys] at hry
      obtain ⟨i, hi⟩ := eR.surjective ⟨r, hr⟩
      refine ⟨DihedralGroup.sr (-i.toAdd), ?_⟩
      apply Subtype.ext
      have hir : rot i.toAdd = r := congrArg Subtype.val hi
      change s * rot (-i.toAdd) = (x : X)
      calc
        s * rot (-i.toAdd) = rot i.toAdd * s := (hrot_s i.toAdd).symm
        _ = r * s := by rw [hir]
        _ = (x : X) := hry
  have hFinj : Function.Injective F := by
    intro d e hde
    cases d with
    | r i =>
        cases e with
        | r j =>
            have hij : rot i = rot j :=
              congrArg (fun z : E => (z : X)) hde
            have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j := by
              apply eR.injective
              apply Subtype.ext
              exact hij
            exact congrArg DihedralGroup.r (congrArg Multiplicative.toAdd heq)
        | sr j =>
            exfalso
            have hEq : rot i = s * rot j :=
              congrArg (fun z : E => (z : X)) hde
            apply hsnotR
            have : s = rot i * (rot j)⁻¹ := by rw [hEq]; group
            rw [this]
            exact R.mul_mem (hrot_mem i) (R.inv_mem (hrot_mem j))
    | sr i =>
        cases e with
        | r j =>
            exfalso
            have hEq : s * rot i = rot j :=
              congrArg (fun z : E => (z : X)) hde
            apply hsnotR
            have : s = rot j * (rot i)⁻¹ := by rw [← hEq]; group
            rw [this]
            exact R.mul_mem (hrot_mem j) (R.inv_mem (hrot_mem i))
        | sr j =>
            have hij : rot i = rot j := by
              have := congrArg (fun z : E => (z : X)) hde
              dsimp [F, f] at this
              exact mul_left_cancel this
            have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j := by
              apply eR.injective
              apply Subtype.ext
              exact hij
            exact congrArg DihedralGroup.sr (congrArg Multiplicative.toAdd heq)
  exact ⟨(MulEquiv.ofBijective F ⟨hFinj, hFsurj⟩).symm⟩

