module
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Join
public import Mathlib.Tactic.Group

/-!
# Diagonal elementary eights in quaternion central products

Let `B` and `C` be commuting quaternion subgroups with intersection of order
two, and let `θ : B ≃* C` be an actual factor isomorphism. The diagonal subgroup
is the range of `b ↦ b * θ b` joined with `B ⊓ C`. It is elementary abelian of
order eight, contains the shared center, and lies in `B ⊔ C`.

Factor commutation makes the diagonal map a homomorphism. The two quaternion
factors share their unique involution, which the isomorphism preserves in the
ambient group. Thus the map has exponent-two image, and its kernel is the
intersection of the factors. Its image has order four and intersects the
shared center trivially. The commuting join therefore has order eight and
exponent two.

This intrinsic construction supplies the diagonal geometry used in
Stellmacher (9.1), Journal of Algebra 190 (1997), p. 48. Its exact map and join
are exposed for later action calculations; selecting an invariant diagonal
requires the separate action hypotheses of the application.

For an involution that swaps the factors through `θ`, its centralizer inside
`B ⊔ C` is exactly this diagonal. A fixed product `b*c` differs from
`b*θ(b)` by an element of `B ⊓ C`; conversely the diagonal generators and the
shared involution are fixed. This identity requires only factor commutation
and intersection of order two, while the quaternion calculation above supplies
the elementary-eight conclusion.
-/

open scoped Pointwise

namespace Subgroup
universe u
variable {G : Type u} [Group G]

/-- Multiplication of matching elements in two commuting isomorphic factors. -/
@[expose] public def quaternionDiagonalHom (B C : Subgroup G) (θ : B ≃* C)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) : B →* G where
  toFun b := (b : G) * θ b
  map_one' := by simp
  map_mul' b b' := by
    simp only [map_mul, Subgroup.coe_mul]
    rw [mul_assoc, ← mul_assoc (b' : G), hcomm b' b'.property (θ b) (θ b).property]
    simp only [mul_assoc]

/-- The matched-factor image joined with the shared intersection. -/
@[expose] public def quaternionDiagonal (B C : Subgroup G) (θ : B ≃* C)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) : Subgroup G :=
  (quaternionDiagonalHom B C θ hcomm).range ⊔ (B ⊓ C)

private theorem quaternion_unique_involution {Q : Type*} [Group Q]
    (e : Q ≃* QuaternionGroup 2) (z : Q) (hz : z ≠ 1) (hz2 : z ^ 2 = 1) :
    (∀ x : Q, x ^ 2 = 1 → x = 1 ∨ x = z) ∧
    (∀ x : Q, x ^ 2 = 1 ∨ x ^ 2 = z) := by
  have h : ∀ z : QuaternionGroup 2, z ≠ 1 → z ^ 2 = 1 →
      (∀ x : QuaternionGroup 2, x ^ 2 = 1 → x = 1 ∨ x = z) ∧
      (∀ x : QuaternionGroup 2, x ^ 2 = 1 ∨ x ^ 2 = z) := by decide
  have hz' : e z ≠ 1 := fun hh => hz (e.injective (hh.trans e.map_one.symm))
  have hz2' : (e z)^2 = 1 := by rw [← map_pow, hz2, map_one]
  obtain ⟨h1, h2⟩ := h (e z) hz' hz2'
  constructor
  · intro x hx
    have hx' : (e x)^2 = 1 := by rw [← map_pow, hx, map_one]
    rcases h1 (e x) hx' with hh | hh
    · exact Or.inl (e.injective (hh.trans e.map_one.symm))
    · exact Or.inr (e.injective hh)
  · intro x
    rcases h2 (e x) with hh | hh
    · exact Or.inl (e.injective (by simpa using hh))
    · exact Or.inr (e.injective (by simpa using hh))

/-- The actual diagonal of a quaternion central product is an elementary eight. -/
public theorem quaternion_diagonal_elementary_eight (B C : Subgroup G)
    (model : B ≃* QuaternionGroup 2) (θ : B ≃* C)
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) :
    IsElementaryAbelian 2 (quaternionDiagonal B C θ hcomm) ∧
      Nat.card (quaternionDiagonal B C θ hcomm) = 8 ∧
      B ⊓ C ≤ quaternionDiagonal B C θ hcomm ∧
      quaternionDiagonal B C θ hcomm ≤ B ⊔ C := by
  let I := B ⊓ C
  obtain ⟨z, hz, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : I)).mp hinter
  have hzG : (z : G) ≠ 1 := fun hh => hz (Subtype.ext hh)
  have hz2 : (z : G)^2 = 1 := by
    have hh := pow_card_eq_one' (x := z)
    rw [hinter] at hh
    exact congrArg Subtype.val hh
  let zB : B := ⟨z, z.property.1⟩
  let zC : C := ⟨z, z.property.2⟩
  have hzB : zB ≠ 1 := fun hh => hzG (congrArg Subtype.val hh)
  have hzC : zC ≠ 1 := fun hh => hzG (congrArg Subtype.val hh)
  have hzB2 : zB ^ 2 = 1 := Subtype.ext hz2
  have hzC2 : zC ^ 2 = 1 := Subtype.ext hz2
  have hB := quaternion_unique_involution model zB hzB hzB2
  have hC := quaternion_unique_involution (θ.symm.trans model) zC hzC hzC2
  have hθz : θ zB = zC := by
    have hsq : (θ zB)^2 = 1 := by rw [← map_pow, hzB2, map_one]
    rcases hC.1 (θ zB) hsq with hh | hh
    · exact (hzB (θ.injective (hh.trans θ.map_one.symm))).elim
    · exact hh
  have hθI (b : B) (hb : (b : G) ∈ C) : (θ b : G) = b := by
    let bb : I := ⟨b, b.property, hb⟩
    by_cases h : bb = 1
    · have hb1 : b = 1 := Subtype.ext (congrArg (fun t : I => (t : G)) h)
      simp [hb1]
    · have hbb : bb = z := hzuniq bb h
      have hbz : b = zB := Subtype.ext (congrArg (fun t : I => (t : G)) hbb)
      rw [hbz, hθz]
  have hsquare (b : B) : ((b : G) * θ b)^2 = 1 := by
    rw [(show Commute (b : G) (θ b) from hcomm b b.property (θ b) (θ b).property).mul_pow]
    rcases hB.2 b with hb | hb
    · have hθb : (θ b)^2 = 1 := by rw [← map_pow, hb, map_one]
      have hbG : (b : G)^2 = 1 := congrArg Subtype.val hb
      have hθbG : (θ b : G)^2 = 1 := congrArg Subtype.val hθb
      rw [hbG, hθbG, one_mul]
    · have hθb : (θ b)^2 = zC := by rw [← map_pow, hb, hθz]
      have hbG : (b : G)^2 = z := congrArg Subtype.val hb
      have hθbG : (θ b : G)^2 = z := congrArg Subtype.val hθb
      rw [hbG, hθbG, ← pow_two, hz2]
  let f := quaternionDiagonalHom B C θ hcomm
  have hfI (b : B) (hb : (b : G) ∈ C) : f b = 1 := by
    change (b : G) * θ b = 1
    rw [hθI b hb, ← pow_two]
    let bb : I := ⟨b, b.property, hb⟩
    have hh := pow_card_eq_one' (x := bb)
    rw [hinter] at hh
    exact congrArg Subtype.val hh
  have hker : f.ker = I.subgroupOf B := by
    ext b
    constructor
    · intro hb
      have hh : (b : G) * θ b = 1 := hb
      have heq : (b : G) = (θ b : G)⁻¹ := eq_inv_of_mul_eq_one_left hh
      exact ⟨b.property, by change (b : G) ∈ C; rw [heq]; exact C.inv_mem (θ b).property⟩
    · intro hb
      exact hfI b hb.2
  have hkerCard : Nat.card f.ker = 2 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show I ≤ B from inf_le_left)).toEquiv]
    exact hinter
  have hBcard : Nat.card B = 8 := by
    rw [Nat.card_congr model.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hrangeCard : Nat.card f.range = 4 := by
    have hh := f.ker.card_mul_index
    rw [Subgroup.index_ker, hkerCard, hBcard] at hh
    omega
  have hdisj : Disjoint f.range I := by
    apply disjoint_iff.mpr
    apply le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨b, rfl⟩ := hx.1
    have hbC : (b : G) ∈ C := by
      have hh : (b : G) * θ b ∈ C := hx.2.2
      exact (C.mul_mem_cancel_right (θ b).property).mp hh
    exact hfI b hbC
  have hcentral : I ≤ centralizer (f.range : Set G) := by
    intro w hw x hx
    obtain ⟨b, rfl⟩ := hx
    change ((b : G) * θ b) * w = w * ((b : G) * θ b)
    rw [mul_assoc, ← hcomm w hw.1 (θ b) (θ b).property,
      ← mul_assoc, hcomm b b.property w hw.2, mul_assoc]
  have helementary {A : Type u} [Group A] (hsq : ∀ a : A, a^2 = 1) :
      IsElementaryAbelian 2 A := by
    have hinv (a : A) : a⁻¹ = a := by
      apply inv_eq_of_mul_eq_one_left
      simpa [pow_two] using hsq a
    exact {
      toIsMulCommutative := ⟨⟨fun a b => by
        calc
          a * b = (a * b)⁻¹ := (hinv _).symm
          _ = b * a := by rw [mul_inv_rev, hinv, hinv]⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }
  let : IsElementaryAbelian 2 f.range := helementary (A := ↥f.range) (by
    intro x
    obtain ⟨b, hb⟩ := x.property
    apply Subtype.ext
    change (x : G)^2 = 1
    rw [← hb]
    exact hsquare b)
  let : IsElementaryAbelian 2 I := helementary (A := ↥I) (by
    intro x
    have hIc : Nat.card I = 2 := hinter
    simpa only [hIc] using pow_card_eq_one' (x := x))
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer hcentral, ?_, le_sup_right, ?_⟩
  · change Nat.card (f.range ⊔ I : Subgroup G) = 8
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (hcentral.trans (centralizer_le_normalizer _)) hdisj, hrangeCard, hinter]
  · apply sup_le
    · intro x hx
      obtain ⟨b, rfl⟩ := hx
      exact mul_mem_sup b.property (θ b).property
    · exact inf_le_left.trans le_sup_left
/-- The fixed subgroup of an involution swapping two commuting factors through
`θ` is their exact diagonal when the shared intersection has order two. -/
public theorem quaternion_diagonal_eq_inf_centralizer_of_swap
    (B C : Subgroup G) (θ : B ≃* C)
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (s : G) (hs : s^2 = 1)
    (hsB : ∀ b : B, s * (b : G) * s⁻¹ = θ b) :
    (B ⊔ C) ⊓ centralizer ({s} : Set G) = quaternionDiagonal B C θ hcomm := by
  let e : MulAut G := MulAut.conj s
  have he2 (x : G) : e (e x) = x := by
    change s * (s * x * s⁻¹) * s⁻¹ = x
    have hs' : s * s = 1 := by simpa [pow_two] using hs
    calc
      s * (s * x * s⁻¹) * s⁻¹ = (s*s) * x * (s*s)⁻¹ := by group
      _ = x := by rw [hs']; simp
  have heB (b : B) : e (b : G) = θ b := hsB b
  have heC (c : C) : e (c : G) = (θ.symm c : B) := by
    have hh := congrArg e (heB (θ.symm c))
    simpa only [he2, MulEquiv.apply_symm_apply] using hh.symm
  have hfix_iff (x : G) : x ∈ centralizer ({s} : Set G) ↔ e x = x := by
    rw [mem_centralizer_singleton_iff]
    change x * s = s * x ↔ s * x * s⁻¹ = x
    constructor
    · intro h
      rw [← h, mul_inv_cancel_right]
    · intro h
      exact ((mul_inv_eq_iff_eq_mul).mp h).symm
  have heI (x : G) (hx : x ∈ B ⊓ C) : e x = x := by
    have hex : e x ∈ B ⊓ C := by
      constructor
      · rw [heC ⟨x, hx.2⟩]
        exact (θ.symm ⟨x, hx.2⟩).property
      · rw [heB ⟨x, hx.1⟩]
        exact (θ ⟨x, hx.1⟩).property
    by_cases hx1 : x = 1
    · simp [hx1]
    obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : (B ⊓ C : Subgroup G))).mp hinter
    have hxne : (⟨x, hx⟩ : (B ⊓ C : Subgroup G)) ≠ 1 :=
      fun h => hx1 (congrArg Subtype.val h)
    have hexne : (⟨e x, hex⟩ : (B ⊓ C : Subgroup G)) ≠ 1 := by
      intro h
      apply hx1
      apply e.injective
      simpa using congrArg Subtype.val h
    exact congrArg Subtype.val ((hz _ hexne).trans (hz _ hxne).symm)
  apply le_antisymm
  · intro x hx
    have hnorm : B ≤ normalizer (C : Set G) := by
      apply le_trans ?_ (centralizer_le_normalizer _)
      intro b hb c hc
      exact (hcomm b hb c hc).symm
    have hx' : x ∈ (B : Set G) * (C : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right B C hnorm]
      exact hx.1
    obtain ⟨b, hb, c, hc, rfl⟩ := hx'
    have hfixed := (hfix_iff (b*c)).mp hx.2
    let bb : B := ⟨b,hb⟩
    let cc : C := ⟨c,hc⟩
    have heq : (θ bb : G) * (θ.symm cc : G) = b*c := by
      rw [map_mul] at hfixed
      change e (bb : G) * e (cc : G) = b*c at hfixed
      rwa [heB, heC] at hfixed
    let d : G := (θ bb : G)⁻¹ * c
    have hdC : d ∈ C := C.mul_mem (C.inv_mem (θ bb).property) hc
    have hdB : d ∈ B := by
      have hd : d = b⁻¹ * (θ.symm cc : G) := by
        have hbc : b * (θ bb : G) = (θ bb : G) * b := hcomm b hb (θ bb) (θ bb).property
        dsimp [d]
        rw [← mul_left_cancel_iff (a := b)]
        rw [← mul_assoc, (Commute.inv_right hbc).eq, mul_assoc, ← heq]
        simp
      rw [hd]
      exact B.mul_mem (B.inv_mem hb) (θ.symm cc).property
    have hd : d ∈ quaternionDiagonal B C θ hcomm := by
      change d ∈ (quaternionDiagonalHom B C θ hcomm).range ⊔ (B ⊓ C)
      exact (show B ⊓ C ≤ (quaternionDiagonalHom B C θ hcomm).range ⊔ (B ⊓ C)
        from le_sup_right) ⟨hdB, hdC⟩
    have hbdiag : b * (θ bb : G) ∈ quaternionDiagonal B C θ hcomm := by
      change b * (θ bb : G) ∈ (quaternionDiagonalHom B C θ hcomm).range ⊔ (B ⊓ C)
      exact (show (quaternionDiagonalHom B C θ hcomm).range ≤
        (quaternionDiagonalHom B C θ hcomm).range ⊔ (B ⊓ C) from le_sup_left) ⟨bb, rfl⟩
    have hh := (quaternionDiagonal B C θ hcomm).mul_mem hbdiag hd
    simpa [d, mul_assoc] using hh
  · apply sup_le
    · intro x hx
      obtain ⟨b, rfl⟩ := hx
      refine ⟨mul_mem_sup b.property (θ b).property, (hfix_iff _).mpr ?_⟩
      change e ((b : G) * θ b) = (b : G) * θ b
      rw [map_mul, heB, heC, MulEquiv.symm_apply_apply]
      exact (hcomm b b.property (θ b) (θ b).property).symm
    · intro x hx
      exact ⟨(show B ⊓ C ≤ B ⊔ C from inf_le_left.trans le_sup_left) hx, (hfix_iff x).mpr (heI x hx)⟩
end Subgroup
