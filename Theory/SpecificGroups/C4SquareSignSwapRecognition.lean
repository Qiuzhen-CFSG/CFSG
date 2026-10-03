module
public import Theory.SpecificGroups.C4SquareSignSwapPresentation
public import Theory.GroupTheory.QuaternionCentralProductInvolutions

/-!
# Marked sign-and-swap recognition from quaternion coordinates

In an order-64 group, a normal C₄ × C₄ base and normal Q₈ subgroup
intersect in a cyclic subgroup of order four. Extend its generator to a
basis of the base. The order-two center of the quaternion central product
forces an odd coefficient in the quaternion action on the complementary
generator; otherwise both independent base squares would be central.

The coordinate calculation behind Stellmacher (8.6)(a) then turns quaternion
generators `c, r` and a complementary base generator `a` into the rotations
`a, a*c` and swap involution `a^2*r`. An inverter can be adjusted by `c`
to commute with the quaternion generator. Generation then identifies the
three distinguished subgroups using the explicit order-64 presentation.

Source: Stellmacher (8.6)(a), `refs/latex/stellmacher-n-group.tex`.
-/

namespace C4SquareSignSwap

/-- Quaternion coordinates give the sign-and-swap relations explicitly. -/
public theorem relations_of_quaternion_coordinates {G : Type*} [Group G] (a c r t : G)
    (ha : a ^ 4 = 1) (hc : c ^ 4 = 1) (hac : Commute a c)
    (hr : r ^ 2 = c ^ 2) (hra : r * a * r⁻¹ = a * c)
    (hrc : r * c * r⁻¹ = c⁻¹)
    (ht : t ^ 2 = 1) (hta : t * a * t⁻¹ = a⁻¹)
    (htc : t * c * t⁻¹ = c⁻¹) (htr : Commute t r) :
    Relations a (a * c) t (a ^ 2 * r) := by
  have ha2 : a ^ 2 = (a ^ 2)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    simpa only [← pow_add] using ha
  have hconj (x y z : G) : x * (y * z) * x⁻¹ =
      (x * y * x⁻¹) * (x * z * x⁻¹) := by group
  have hrb : r * (a * c) * r⁻¹ = a := by
    rw [hconj, hra, hrc, mul_inv_cancel_right]
  have ht2a : t * a ^ 2 * t⁻¹ = a ^ 2 := by
    rw [show t * a ^ 2 * t⁻¹ = (t * a * t⁻¹) ^ 2 by simp only [pow_two]; group, hta, inv_pow,
      ← ha2]
  have hru : r * a ^ 2 * r⁻¹ = (a * c) ^ 2 := by
    rw [show r * a ^ 2 * r⁻¹ = (r * a * r⁻¹) ^ 2 by simp only [pow_two]; group, hra]
  refine ⟨ha, ?_, ht, ?_, (Commute.refl a).mul_right hac, ?_, hta, ?_, ?_, ?_⟩
  · rw [hac.mul_pow, ha, hc, one_mul]
  · calc
      (a ^ 2 * r) ^ 2 = a ^ 2 * (r * a ^ 2 * r⁻¹) * r ^ 2 := by simp only [pow_two]; group
      _ = a ^ 2 * (a ^ 2 * c ^ 2) * c ^ 2 := by rw [hru, hac.mul_pow, hr]
      _ = a ^ 4 * c ^ 4 := by group
      _ = 1 := by rw [ha, hc, one_mul]
  · change t * (a ^ 2 * r) = (a ^ 2 * r) * t
    calc
      t * (a ^ 2 * r) = (t * a ^ 2 * t⁻¹) * (t * r) := by group
      _ = a ^ 2 * (r * t) := by rw [ht2a, htr.eq]
      _ = _ := by group
  · rw [hconj, hta, htc, mul_inv_rev, hac.inv_inv.eq]
  · calc
      (a ^ 2 * r) * a * (a ^ 2 * r)⁻¹ =
          a ^ 2 * (r * a * r⁻¹) * (a ^ 2)⁻¹ := by group
      _ = a ^ 2 * (a * c) * (a ^ 2)⁻¹ := by rw [hra]
      _ = a * c := by
        rw [((Commute.refl a).mul_right hac).pow_left 2, mul_inv_cancel_right]
  · calc
      (a ^ 2 * r) * (a * c) * (a ^ 2 * r)⁻¹ =
          a ^ 2 * (r * (a * c) * r⁻¹) * (a ^ 2)⁻¹ := by group
      _ = a ^ 2 * a * (a ^ 2)⁻¹ := by rw [hrb]
      _ = a := by rw [(Commute.refl a).pow_left 2, mul_inv_cancel_right]

/-- A quaternion subgroup and its complementary base generator in adapted
coordinates. The action coefficient has been normalized to one. -/
public structure QuaternionCoordinates {G : Type*} [Group G]
    (A R : Subgroup G) (a c r : G) : Prop where
  a_four : a ^ 4 = 1
  c_four : c ^ 4 = 1
  c_two_ne : c ^ 2 ≠ 1
  ac : Commute a c
  r_two : r ^ 2 = c ^ 2
  ra : r * a * r⁻¹ = a * c
  rc : r * c * r⁻¹ = c⁻¹
  base : A = Subgroup.closure ({a, c} : Set G)
  quaternion : R = Subgroup.closure ({c, r} : Set G)

/-- Multiplication by the cyclic quaternion generator corrects the possible
central commutator with an involutive inverter. -/
public theorem exists_commuting_inverter_of_quaternion_coordinates
    {G : Type*} [Group G] (A R : Subgroup G) (a c r t : G)
    (h : QuaternionCoordinates A R a c r)
    (ht : t ^ 2 = 1) (hinv : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹)
    (htr : t * r * t⁻¹ = r ∨ t * r * t⁻¹ = c ^ 2 * r) :
    ∃ t', (t' = t ∨ t' = c * t) ∧ t' ^ 2 = 1 ∧
      (∀ x ∈ A, t' * x * t'⁻¹ = x⁻¹) ∧ Commute t' r := by
  have hcA : c ∈ A := by rw [h.base]; exact Subgroup.subset_closure (by simp)
  have hccomm : ∀ x ∈ A, Commute c x := by
    rw [h.base]
    intro x hx
    apply Subgroup.closure_induction (p := fun x _ => Commute c x) ?_ ?_ ?_ ?_ hx
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact h.ac.symm
      · exact Commute.refl _
    · exact Commute.one_right c
    · intro x y _ _ hx hy
      exact hx.mul_right hy
    · intro x _ hx
      exact hx.inv_right
  rcases htr with htr | htr
  · refine ⟨t, Or.inl rfl, ht, hinv, ?_⟩
    change t * r = r * t
    exact (mul_inv_eq_iff_eq_mul).mp htr
  · refine ⟨c * t, Or.inr rfl, ?_, ?_, ?_⟩
    · calc
        (c * t) ^ 2 = c * (t * c * t⁻¹) * t ^ 2 := by
          simp only [pow_two]; group
        _ = c * c⁻¹ * 1 := by rw [hinv c hcA, ht]
        _ = 1 := by group
    · intro x hx
      calc
        (c * t) * x * (c * t)⁻¹ = c * (t * x * t⁻¹) * c⁻¹ := by group
        _ = c * x⁻¹ * c⁻¹ := by rw [hinv x hx]
        _ = x⁻¹ := by rw [(hccomm x hx).inv_right.eq, mul_inv_cancel_right]
    · change (c * t) * r = r * (c * t)
      have hrc' : r * c = c⁻¹ * r := (mul_inv_eq_iff_eq_mul).mp h.rc
      have hc3 : c ^ 3 = c⁻¹ := by
        apply mul_left_cancel (a := c)
        rw [mul_inv_cancel, ← pow_succ', h.c_four]
      calc
        (c * t) * r = c * (t * r * t⁻¹) * t := by group
        _ = c * (c ^ 2 * r) * t := by rw [htr]
        _ = c ^ 3 * r * t := by group
        _ = (c⁻¹ * r) * t := by rw [hc3]
        _ = r * (c * t) := by rw [← hrc', mul_assoc]


/-- Adapted quaternion coordinates extract all four marked generators.
The central commutator alternative is the only extra information about the
chosen inverter needed by the coordinate calculation. -/
public theorem exists_marked_generators_of_quaternion_coordinates
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 64)
    (A R Qa Qb : Subgroup G) [R.Normal]
    (hA : Nonempty (A ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (hR : Nonempty (R ≃* QuaternionGroup 2))
    (hRQ : R ≤ Qb) (hQb : Qb.index = 2)
    (a c r t : G) (h : QuaternionCoordinates A R a c r)
    (htQb : t ∈ Qb) (ht : t ^ 2 = 1)
    (hinv : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹)
    (hQa : Qa = A ⊔ Subgroup.zpowers t)
    (htr : t * r * t⁻¹ = r ∨ t * r * t⁻¹ = c ^ 2 * r) :
    ∃ a b t' u : G, Relations a b t' u ∧
      Subgroup.closure ({a, b, t', u} : Set G) = ⊤ ∧
      A = Subgroup.closure ({a, b} : Set G) ∧
      A ⊔ R = Subgroup.closure ({a, b, u} : Set G) ∧
      Qa = Subgroup.closure ({a, b, t'} : Set G) ∧
      Qb = Subgroup.closure ({a * b, a * b⁻¹, t', u} : Set G) := by
  have haA : a ∈ A := by rw [h.base]; exact Subgroup.subset_closure (by simp)
  have hcA : c ∈ A := by rw [h.base]; exact Subgroup.subset_closure (by simp)
  have hcR : c ∈ R := by rw [h.quaternion]; exact Subgroup.subset_closure (by simp)
  have hrR : r ∈ R := by rw [h.quaternion]; exact Subgroup.subset_closure (by simp)
  obtain ⟨t', ht', ht2, htinv, htcomm⟩ :=
    exists_commuting_inverter_of_quaternion_coordinates A R a c r t h ht hinv htr
  have hrel : Relations a (a * c) t' (a ^ 2 * r) :=
    relations_of_quaternion_coordinates a c r t' h.a_four h.c_four h.ac h.r_two
      h.ra h.rc ht2 (htinv a haA) (htinv c hcA) htcomm
  have hbase (H : Subgroup G) : A ≤ H ↔ a ∈ H ∧ c ∈ H := by
    rw [h.base]
    simp only [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff,
      SetLike.mem_coe]
  have hquaternion (H : Subgroup G) : R ≤ H ↔ c ∈ H ∧ r ∈ H := by
    rw [h.quaternion]
    simp only [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff,
      SetLike.mem_coe]
  have hbase' : A = Subgroup.closure ({a, a * c} : Set G) := by
    apply eq_of_forall_ge_iff
    intro H
    rw [hbase]
    simp only [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff,
      SetLike.mem_coe]
    exact and_congr_right (fun haH => (H.mul_mem_cancel_left haH).symm)
  have hAR : A ⊔ R = Subgroup.closure ({a, a * c, a ^ 2 * r} : Set G) := by
    apply eq_of_forall_ge_iff
    intro H
    rw [sup_le_iff, hbase, hquaternion]
    simp only [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff,
      SetLike.mem_coe]
    constructor
    · rintro ⟨⟨haH, hcH⟩, _, hrH⟩
      exact ⟨haH, H.mul_mem haH hcH, H.mul_mem (H.pow_mem haH 2) hrH⟩
    · rintro ⟨haH, hbH, huH⟩
      have hcH := (H.mul_mem_cancel_left haH).mp hbH
      exact ⟨⟨haH, hcH⟩, hcH, (H.mul_mem_cancel_left (H.pow_mem haH 2)).mp huH⟩
  have hQa' : Qa = A ⊔ Subgroup.zpowers t' := by
    rw [hQa]
    apply eq_of_forall_ge_iff
    intro H
    simp only [sup_le_iff, Subgroup.zpowers_le]
    apply and_congr_right
    intro hAH
    rcases ht' with rfl | rfl
    · rfl
    · exact (H.mul_mem_cancel_left (hAH hcA)).symm
  have hQa'' : Qa = Subgroup.closure ({a, a * c, t'} : Set G) := by
    apply eq_of_forall_ge_iff
    intro H
    rw [hQa', hbase']
    simp only [sup_le_iff, Subgroup.zpowers_le, Subgroup.closure_le,
      Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe, and_assoc]
  have hgen : Subgroup.closure ({a, a * c, t', a ^ 2 * r} : Set G) = ⊤ := by
    let H := Subgroup.closure ({a, a * c, t', a ^ 2 * r} : Set G)
    have hARH : A ⊔ R ≤ H := by
      rw [hAR]
      apply Subgroup.closure_mono
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
    have htH : t' ∈ H := Subgroup.subset_closure (by simp)
    have hout := Subgroup.inverter_not_mem_c4_square_sup_quaternion A R hA hR t' htinv
    have hindex := Subgroup.c4_square_sup_quaternion_index_two hcard A R hA hR t' htinv
    apply top_unique
    intro x _
    by_cases hx : x ∈ A ⊔ R
    · exact hARH hx
    · have hxt : x * t'⁻¹ ∈ A ⊔ R :=
        ((A ⊔ R).mul_mem_iff_of_index_two hindex).mpr (by
          simp only [hx, Subgroup.inv_mem_iff, hout])
      simpa only [inv_mul_cancel_right] using H.mul_mem (hARH hxt) htH
  have htQ : t' ∈ Qb := by
    rcases ht' with rfl | rfl
    · exact htQb
    · exact Qb.mul_mem (hRQ hcR) htQb
  have huQ : a ^ 2 * r ∈ Qb := Qb.mul_mem (Qb.sq_mem_of_index_two hQb a) (hRQ hrR)
  have hQ : Qb = Subgroup.closure
      ({a * (a * c), a * (a * c)⁻¹, t', a ^ 2 * r} : Set G) := by
    let H := Subgroup.closure
      ({a * (a * c), a * (a * c)⁻¹, t', a ^ 2 * r} : Set G)
    have hHQ : H ≤ Qb := by
      apply (Subgroup.closure_le _).mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · change a * (a * c) ∈ Qb
        simpa only [pow_two, mul_assoc] using
          Qb.mul_mem (Qb.sq_mem_of_index_two hQb a) (hRQ hcR)
      · have heq : a * (a * c)⁻¹ = c⁻¹ := by
          rw [mul_inv_rev, ← mul_assoc, h.ac.inv_right.eq, mul_inv_cancel_right]
        rw [heq]
        exact Qb.inv_mem (hRQ hcR)
      · exact htQ
      · exact huQ
    obtain ⟨e, ea, eb, et, eu⟩ := exists_equiv_of_relations hcard hrel hgen
    have hmap : extraspecialCore.map e.toMonoidHom = H := by
      rw [extraspecialCore_eq_closure, MonoidHom.map_closure]
      simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom,
        map_mul, map_inv, ea, eb, et, eu]
      rfl
    have hHcard : Nat.card H = 32 := by
      rw [← hmap, Subgroup.card_map_of_injective e.injective, card_extraspecialCore]
    have hQcard : Nat.card Qb = 32 := by
      have hh := Qb.card_mul_index
      rw [hQb, hcard] at hh
      omega
    exact (Subgroup.eq_of_le_of_card_ge hHQ (by rw [hHcard, hQcard])).symm
  exact ⟨a, a * c, t', a ^ 2 * r, hrel, hgen, hbase', hAR, hQa'', hQ⟩


/-- In a quaternion central product, an involution conjugates an element
with nontrivial square either to itself or to its inverse. -/
public theorem inverter_quaternion_conjugation_alternatives
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (c r t : G) (hrmem : r ∈ B ⊔ C) (htmem : t ∈ B ⊔ C)
    (hc4 : c ^ 4 = 1) (hc2 : c ^ 2 ≠ 1)
    (hr2 : r ^ 2 = c ^ 2) (ht2 : t ^ 2 = 1) :
    t * r * t⁻¹ = r ∨ t * r * t⁻¹ = c ^ 2 * r := by
  have hcmem : c ^ 2 ∈ B ⊓ C := by
    rw [← hr2]
    exact Subgroup.quaternion_central_product_square_mem_inf
      B C hB hC hinter hcomm r hrmem
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : (B ⊓ C : Subgroup G))).mp hinter
  have hz' : (⟨c ^ 2, hcmem⟩ : (B ⊓ C : Subgroup G)) = z :=
    hz _ (fun heq => hc2 (congrArg Subtype.val heq))
  have hsqmem : (t * r) ^ 2 ∈ B ⊓ C :=
    Subgroup.quaternion_central_product_square_mem_inf B C hB hC hinter hcomm
      (t * r) ((B ⊔ C).mul_mem htmem hrmem)
  have hsq : (t * r) ^ 2 = 1 ∨ (t * r) ^ 2 = c ^ 2 := by
    by_cases hh : (t * r) ^ 2 = 1
    · exact Or.inl hh
    · exact Or.inr (congrArg Subtype.val
        ((hz ⟨(t * r) ^ 2, hsqmem⟩ (fun heq => hh (congrArg Subtype.val heq))).trans hz'.symm))
  have hr4 : r ^ 4 = 1 := by
    calc r ^ 4 = (r ^ 2) ^ 2 := by group
         _ = (c ^ 2) ^ 2 := by rw [hr2]
         _ = 1 := by simpa only [← pow_mul] using hc4
  have hrinv : r⁻¹ = c ^ 2 * r := by
    calc r⁻¹ = r⁻¹ * r ^ 4 := by rw [hr4, mul_one]
         _ = r ^ 2 * r := by group
         _ = c ^ 2 * r := by rw [hr2]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht2)
  have hconj : t * r * t⁻¹ = (t * r) ^ 2 * r⁻¹ := by
    rw [htinv]
    simp only [pow_two]
    group
  rcases hsq with hs | hs
  · exact Or.inr (by rw [hconj, hs, one_mul, hrinv])
  · exact Or.inl (by
      rw [hconj, hs, hrinv, ← mul_assoc, ← pow_add, hc4, one_mul])

/-- The quaternion central product supplies the commutator condition, so
adapted base coordinates suffice for the complete marked extraction. -/
public theorem exists_marked_generators_of_central_product_coordinates
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 64)
    (A R Qa Qb B C : Subgroup G) [R.Normal]
    (hA : Nonempty (A ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (hR : Nonempty (R ≃* QuaternionGroup 2))
    (hRQ : R ≤ Qb) (hQb : Qb.index = 2) (hBC : Qb = B ⊔ C)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (a c r t : G) (h : QuaternionCoordinates A R a c r)
    (htQb : t ∈ Qb) (ht : t ^ 2 = 1)
    (hinv : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹)
    (hQa : Qa = A ⊔ Subgroup.zpowers t) :
    ∃ a b t' u : G, Relations a b t' u ∧
      Subgroup.closure ({a, b, t', u} : Set G) = ⊤ ∧
      A = Subgroup.closure ({a, b} : Set G) ∧
      A ⊔ R = Subgroup.closure ({a, b, u} : Set G) ∧
      Qa = Subgroup.closure ({a, b, t'} : Set G) ∧
      Qb = Subgroup.closure ({a * b, a * b⁻¹, t', u} : Set G) := by
  have hrR : r ∈ R := by rw [h.quaternion]; exact Subgroup.subset_closure (by simp)
  apply exists_marked_generators_of_quaternion_coordinates hcard A R Qa Qb hA hR hRQ hQb
    a c r t h htQb ht hinv hQa
  exact inverter_quaternion_conjugation_alternatives B C hB hC hinter hcomm c r t
    (hBC ▸ hRQ hrR) (hBC ▸ htQb) h.c_four h.c_two_ne h.r_two ht


private theorem exists_base_complement {G : Type*} [Group G]
    (A : Subgroup G) (hA : Nonempty (A ≃* Base))
    (c : G) (hcA : c ∈ A) (hc2 : c ^ 2 ≠ 1) :
    ∃ a : G, a ^ 4 = 1 ∧ a ^ 2 ≠ 1 ∧ a ^ 2 ≠ c ^ 2 ∧ Commute a c ∧
      A = Subgroup.closure ({a, c} : Set G) := by
  obtain ⟨e⟩ := hA
  let cA : A := ⟨c, hcA⟩
  have hnon : (e cA) ^ 2 ≠ 1 := by
    intro heq
    apply hc2
    have hh : cA ^ 2 = 1 := e.injective (by simpa only [map_pow, map_one] using heq)
    exact congrArg (fun x : A => (x : G)) hh
  have hfinite : ∀ c : Base, c ^ 2 ≠ 1 → ∃ a : Base,
      a ^ 4 = 1 ∧ a ^ 2 ≠ 1 ∧ a ^ 2 ≠ c ^ 2 ∧
      ∀ x : Base, ∃ i j : Fin 4, x = a ^ i.val * c ^ j.val := by decide +kernel
  obtain ⟨aB, ha4, ha2, hac2, hgen⟩ := hfinite (e cA) hnon
  let aA := e.symm aB
  have ha4' : (aA : G) ^ 4 = 1 := by
    have hh : aA ^ 4 = 1 := e.injective (by simpa [aA] using ha4)
    exact congrArg (fun x : A => (x : G)) hh
  have ha2' : (aA : G) ^ 2 ≠ 1 := by
    intro heq
    apply ha2
    have hh : aA ^ 2 = 1 := Subtype.ext heq
    simpa [aA] using congrArg e hh
  have hac2' : (aA : G) ^ 2 ≠ c ^ 2 := by
    intro heq
    apply hac2
    have hh : aA ^ 2 = cA ^ 2 := Subtype.ext heq
    simpa [aA] using congrArg e hh
  have hac : Commute (aA : G) c := by
    have hh : aA * cA = cA * aA := e.injective (by
      simp only [map_mul]; exact mul_comm _ _)
    exact congrArg (fun x : A => (x : G)) hh
  refine ⟨aA, ha4', ha2', hac2', hac, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨i, j, hij⟩ := hgen (e ⟨x, hx⟩)
    have heq : x = (aA : G) ^ i.val * c ^ j.val := by
      have hh : (⟨x, hx⟩ : A) = aA ^ i.val * cA ^ j.val := e.injective (by
        simpa [aA] using hij)
      exact congrArg (fun x : A => (x : G)) hh
    rw [heq]
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact aA.property
    · exact hcA

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem exists_quaternion_complement {G : Type*} [Group G]
    (R : Subgroup G) (hR : Nonempty (R ≃* QuaternionGroup 2))
    (c : G) (hcR : c ∈ R) (hc2 : c ^ 2 ≠ 1) :
    ∃ r : G, r ^ 2 = c ^ 2 ∧ r * c * r⁻¹ = c⁻¹ ∧
      R = Subgroup.closure ({c, r} : Set G) := by
  obtain ⟨e⟩ := hR
  let cR : R := ⟨c, hcR⟩
  have hnon : (e cR) ^ 2 ≠ 1 := by
    intro heq
    apply hc2
    have hh : cR ^ 2 = 1 := e.injective (by simpa only [map_pow, map_one] using heq)
    exact congrArg (fun x : R => (x : G)) hh
  have hfinite : ∀ c : QuaternionGroup 2, c ^ 2 ≠ 1 → ∃ r : QuaternionGroup 2,
      r ^ 2 = c ^ 2 ∧ r * c * r⁻¹ = c⁻¹ ∧
      ∀ x : QuaternionGroup 2, ∃ i j : Fin 4, x = c ^ i.val * r ^ j.val := by decide +kernel
  obtain ⟨rB, hr2, hrc, hgen⟩ := hfinite (e cR) hnon
  let rR := e.symm rB
  refine ⟨rR, ?_, ?_, le_antisymm ?_ ?_⟩
  · have hh : rR ^ 2 = cR ^ 2 := e.injective (by simpa [rR] using hr2)
    exact congrArg (fun x : R => (x : G)) hh
  · have hh : rR * cR * rR⁻¹ = cR⁻¹ := e.injective (by simpa [rR] using hrc)
    exact congrArg (fun x : R => (x : G)) hh
  · intro x hx
    obtain ⟨i, j, hij⟩ := hgen (e ⟨x, hx⟩)
    have heq : x = c ^ i.val * (rR : G) ^ j.val := by
      have hh : (⟨x, hx⟩ : R) = cR ^ i.val * rR ^ j.val := e.injective (by
        simpa [rR] using hij)
      exact congrArg (fun x : R => (x : G)) hh
    rw [heq]
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hcR
    · exact rR.property


/-- The order-two center forces an odd action coefficient, yielding adapted
quaternion coordinates for the normal C₄-square base. -/
public theorem exists_quaternion_coordinates_of_central_product
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 64)
    (A R Qb B C : Subgroup G) [A.Normal] [R.Normal]
    (hA : Nonempty (A ≃* Base)) (hR : Nonempty (R ≃* QuaternionGroup 2))
    (hRQ : R ≤ Qb) (hQb : Qb.index = 2) (hBC : Qb = B ⊔ C)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (t : G) (hinv : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹) :
    ∃ a c r : G, QuaternionCoordinates A R a c r := by
  classical
  obtain ⟨c, hcorder, hcgen⟩ :=
    Subgroup.exists_generator_c4_square_inf_quaternion hcard A R hA hR t hinv
  have hcAR : c ∈ A ⊓ R := hcgen ▸ Subgroup.mem_zpowers c
  have hc4 : c ^ 4 = 1 := hcorder ▸ pow_orderOf_eq_one c
  have hc2 : c ^ 2 ≠ 1 := by
    intro hh
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [hcorder] at hd
    norm_num at hd
  obtain ⟨a, ha4, ha2, hac2, hac, hbase⟩ := exists_base_complement A hA c hcAR.1 hc2
  obtain ⟨r, hr2, hrc, hquat⟩ := exists_quaternion_complement R hR c hcAR.2 hc2
  have haA : a ∈ A := by rw [hbase]; exact Subgroup.subset_closure (by simp)
  have hrR : r ∈ R := by rw [hquat]; exact Subgroup.subset_closure (by simp)
  have hcommem : r * a * r⁻¹ * a⁻¹ ∈ A ⊓ R := by
    constructor
    · exact A.mul_mem (Subgroup.Normal.conj_mem inferInstance a haA r) (A.inv_mem haA)
    · change r * a * r⁻¹ * a⁻¹ ∈ R
      have hh := R.mul_mem hrR
        (Subgroup.Normal.conj_mem inferInstance r⁻¹ (R.inv_mem hrR) a)
      simpa only [mul_assoc] using hh
  rw [← hcgen, mem_zpowers_iff_mem_range_orderOf, hcorder] at hcommem
  obtain ⟨k, hk, hpower⟩ := Finset.mem_image.mp hcommem
  have hk4 : k < 4 := Finset.mem_range.mp hk
  have hra : r * a * r⁻¹ = c ^ k * a :=
    (mul_inv_eq_iff_eq_mul).mp hpower.symm
  have htop : Subgroup.closure ({a, c, r, t} : Set G) = ⊤ := by
    let H := Subgroup.closure ({a, c, r, t} : Set G)
    have hARH : A ⊔ R ≤ H := by
      rw [hbase, hquat]
      apply sup_le <;> apply Subgroup.closure_mono <;>
        intro x hx <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢ <;> tauto
    have htH : t ∈ H := Subgroup.subset_closure (by simp)
    have hout := Subgroup.inverter_not_mem_c4_square_sup_quaternion A R hA hR t hinv
    have hidx := Subgroup.c4_square_sup_quaternion_index_two hcard A R hA hR t hinv
    apply top_unique
    intro x _
    by_cases hx : x ∈ A ⊔ R
    · exact hARH hx
    · have hxt : x * t⁻¹ ∈ A ⊔ R :=
        ((A ⊔ R).mul_mem_iff_of_index_two hidx).mpr (by
          simp only [hx, Subgroup.inv_mem_iff, hout])
      simpa only [inv_mul_cancel_right] using H.mul_mem (hARH hxt) htH
  have hcentral (x : G) (hxa : Commute x a) (hxc : Commute x c)
      (hxr : Commute x r) (hxt : Commute x t) : ∀ y : G, Commute x y := by
    intro y
    have hy : y ∈ Subgroup.closure ({a, c, r, t} : Set G) := by rw [htop]; trivial
    apply Subgroup.closure_induction (p := fun y _ => Commute x y) ?_ ?_ ?_ ?_ hy
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hxa
      · exact hxc
      · exact hxr
      · exact hxt
    · exact Commute.one_right x
    · intro y z _ _ hy hz
      exact hy.mul_right hz
    · intro y _ hy
      exact hy.inv_right
  have hsqinv (x : G) (hx : x ^ 4 = 1) : (x ^ 2)⁻¹ = x ^ 2 := by
    symm
    apply eq_inv_iff_mul_eq_one.mpr
    simpa only [← pow_add] using hx
  have hct : Commute (c ^ 2) t := by
    have hh : t * c ^ 2 * t⁻¹ = c ^ 2 := by
      rw [← conj_pow, hinv c hcAR.1, inv_pow, hsqinv c hc4]
    exact ((mul_inv_eq_iff_eq_mul).mp hh).symm
  have hcr : Commute (c ^ 2) r := by
    have hh : r * c ^ 2 * r⁻¹ = c ^ 2 := by
      rw [← conj_pow, hrc, inv_pow, hsqinv c hc4]
    exact ((mul_inv_eq_iff_eq_mul).mp hh).symm
  have hcCentral := hcentral (c ^ 2) (hac.symm.pow_left 2)
    ((Commute.refl c).pow_left 2) hcr hct
  have hkodd : k = 1 ∨ k = 3 := by
    by_contra hn
    have hkeven : k = 0 ∨ k = 2 := by omega
    have hck2 : (c ^ k) ^ 2 = 1 := by
      rcases hkeven with rfl | rfl
      · simp
      · simpa only [← pow_mul] using hc4
    have har : Commute (a ^ 2) r := by
      have hh : r * a ^ 2 * r⁻¹ = a ^ 2 := by
        rw [← conj_pow, hra, ((hac.symm.pow_left k)).mul_pow, hck2, one_mul]
      exact ((mul_inv_eq_iff_eq_mul).mp hh).symm
    have hat : Commute (a ^ 2) t := by
      have hh : t * a ^ 2 * t⁻¹ = a ^ 2 := by
        rw [← conj_pow, hinv a haA, inv_pow, hsqinv a ha4]
      exact ((mul_inv_eq_iff_eq_mul).mp hh).symm
    have haCentral := hcentral (a ^ 2) ((Commute.refl a).pow_left 2) (hac.pow_left 2) har hat
    have hZcard : Nat.card (Subgroup.center Qb) = 2 := by
      rw [hBC]
      exact Subgroup.quaternion_central_product_center_card B C hB hC hinter hcomm
    let aa : Subgroup.center Qb := ⟨⟨a ^ 2, Qb.sq_mem_of_index_two hQb a⟩,
      Subgroup.mem_center_iff.mpr (fun y => Subtype.ext (haCentral y).symm)⟩
    let cc : Subgroup.center Qb := ⟨⟨c ^ 2, Qb.pow_mem (hRQ hcAR.2) 2⟩,
      Subgroup.mem_center_iff.mpr (fun y => Subtype.ext (hcCentral y).symm)⟩
    have haa : aa ≠ 1 := fun hh => ha2 (congrArg (fun z : Subgroup.center Qb => ((z : Qb) : G)) hh)
    have hcc : cc ≠ 1 := fun hh => hc2 (congrArg (fun z : Subgroup.center Qb => ((z : Qb) : G)) hh)
    obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center Qb)).mp hZcard
    exact hac2 (congrArg (fun z : Subgroup.center Qb => ((z : Qb) : G))
      ((hz aa haa).trans (hz cc hcc).symm))
  rcases hkodd with rfl | rfl
  · refine ⟨a, c, r, ha4, hc4, hc2, hac, hr2, ?_, hrc, hbase, hquat⟩
    simpa only [pow_one, hac.eq] using hra
  · refine ⟨a⁻¹, c, r, ?_, hc4, hc2, hac.inv_left, hr2, ?_, hrc, ?_, hquat⟩
    · rw [inv_pow, ha4, inv_one]
    · have hc3 : c ^ 3 = c⁻¹ := by
        apply mul_right_cancel (b := c)
        rw [inv_mul_cancel, ← pow_succ, hc4]
      rw [← conj_inv, hra, hc3, mul_inv_rev, inv_inv]
    · rw [hbase]
      apply eq_of_forall_ge_iff
      intro H
      simp only [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff,
        SetLike.mem_coe, Subgroup.inv_mem_iff]


/-- Extract marked sign-and-swap generators from a split order-64 local
configuration. All hypotheses concern ordinary subgroups and their models;
no ambient recognition or classification assumptions are required. -/
public theorem exists_marked_generators_of_split_local_structure
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 64)
    (A R Qa Qb B C : Subgroup G) [A.Normal] [R.Normal]
    (hA : Nonempty (A ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (hR : Nonempty (R ≃* QuaternionGroup 2))
    (hRQ : R ≤ Qb) (hQb : Qb.index = 2) (hBC : Qb = B ⊔ C)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (t : G) (htQb : t ∈ Qb) (ht : t ^ 2 = 1)
    (hinv : ∀ x ∈ A, t * x * t⁻¹ = x⁻¹)
    (hQa : Qa = A ⊔ Subgroup.zpowers t) :
    ∃ a b t' u : G, Relations a b t' u ∧
      Subgroup.closure ({a, b, t', u} : Set G) = ⊤ ∧
      A = Subgroup.closure ({a, b} : Set G) ∧
      A ⊔ R = Subgroup.closure ({a, b, u} : Set G) ∧
      Qa = Subgroup.closure ({a, b, t'} : Set G) ∧
      Qb = Subgroup.closure ({a * b, a * b⁻¹, t', u} : Set G) := by
  obtain ⟨a, c, r, h⟩ := exists_quaternion_coordinates_of_central_product hcard
    A R Qb B C hA hR hRQ hQb hBC hB hC hinter hcomm t hinv
  exact exists_marked_generators_of_central_product_coordinates hcard A R Qa Qb B C
    hA hR hRQ hQb hBC hB hC hinter hcomm a c r t h htQb ht hinv hQa

end C4SquareSignSwap
