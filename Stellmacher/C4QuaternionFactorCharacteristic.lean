module

public import Stellmacher.LaterDefs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The characteristic quaternion factor of C4 central Q8

For commuting cyclic-four and quaternion-eight subgroups with intersection
of order two, every noncentral order-four element of their join lies in the
quaternion factor. Both factors have a square dichotomy relative to the
shared involution. If the cyclic component is not in the intersection, a
noncentral quaternion component makes the product an involution, while a
central quaternion component makes the product central in the join.

The two standard noncommuting quaternion generators then show that every
quaternion subgroup of the join equals the given factor. Consequently every
automorphism preserving the join, and every element of its ambient normalizer,
preserves that factor. Its relative index two gives a commutator bound for
every group of normalizing actors. The final extraction theorems apply this
to the actual factors in `IsCentralProductModel whole C4 Q8`.

These are the algebraic factor-invariance and containment prerequisites for
the residual-action argument in Stellmacher (1997), Section 8, (8.6)(a2).
-/

open scoped Pointwise

namespace Subgroup

universe u v
variable {G : Type u} [Group G]

private theorem model_square_dichotomy {M : Type v} [Group M]
    (hfinite : ∀ z b : M, z ≠ 1 → z ^ 2 = 1 →
      (b = 1 ∨ b = z) ∨ b ^ 2 = z)
    (B : Subgroup G) (e : B ≃* M) (z : G) (hz : z ∈ B)
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (b : G) (hb : b ∈ B) :
    (b = 1 ∨ b = z) ∨ b ^ 2 = z := by
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

public theorem c4_quaternion_noncentral_order_four_mem (B C : Subgroup G)
    (hB : Nonempty (B ≃* Multiplicative (ZMod 4)))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (x : G) (hx : x ∈ B ⊔ C) (hx4 : orderOf x = 4)
    (hnoncentral : ∃ y ∈ B ⊔ C, x * y ≠ y * x) : x ∈ C := by
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
  have hdecomp (y : G) (hy : y ∈ B ⊔ C) :
      ∃ b ∈ B, ∃ c ∈ C, b * c = y := by
    change y ∈ (↑(B ⊔ C) : Set G) at hy
    rw [coe_mul_of_left_le_normalizer_right B C hnorm] at hy
    exact hy
  have hcentral (b : G) (hb : b ∈ B) (y : G) (hy : y ∈ B ⊔ C) :
      b * y = y * b := by
    obtain ⟨other, hother, c, hc, rfl⟩ := hdecomp y hy
    have hbb : b * other = other * b := by
      have hsub : (⟨b, hb⟩ : B) * ⟨other, hother⟩ =
          (⟨other, hother⟩ : B) * ⟨b, hb⟩ := eB.injective
        (by simp only [map_mul]; exact mul_comm (eB ⟨b, hb⟩) (eB ⟨other, hother⟩))
      exact congrArg Subtype.val hsub
    rw [← mul_assoc, hbb, mul_assoc, hcomm b hb c hc, ← mul_assoc]
  obtain ⟨b, hb, c, hc, rfl⟩ := hdecomp x hx
  have hfour : ∀ z b : Multiplicative (ZMod 4), z ≠ 1 → z ^ 2 = 1 →
      (b = 1 ∨ b = z) ∨ b ^ 2 = z := by decide
  have hquaternion : ∀ z b : QuaternionGroup 2, z ≠ 1 → z ^ 2 = 1 →
      (b = 1 ∨ b = z) ∨ b ^ 2 = z := by decide
  rcases model_square_dichotomy hfour B eB z zz.property.1 hz1' hz2 b hb with
    (hb1 | hbz) | hb2
  · simpa [hb1] using hc
  · exact C.mul_mem (hbz ▸ zz.property.2) hc
  rcases model_square_dichotomy hquaternion C eC z zz.property.2 hz1' hz2 c hc with
    (hc1 | hcz) | hc2
  · obtain ⟨y, hy, hxy⟩ := hnoncentral
    exact (hxy (hcentral (b * c) (by simpa [hc1] using hb) y hy)).elim
  · obtain ⟨y, hy, hxy⟩ := hnoncentral
    exact (hxy (hcentral (b * c) (B.mul_mem hb (hcz ▸ zz.property.1)) y hy)).elim
  · have hsq : (b * c) ^ 2 = 1 := by
      rw [(show Commute b c from hcomm b hb c hc).mul_pow, hb2, hc2, ← pow_two, hz2]
    have hdvd := orderOf_dvd_of_pow_eq_one hsq
    rw [hx4] at hdvd
    norm_num at hdvd

public theorem c4_quaternion_subgroup_eq_factor (B C D : Subgroup G)
    (hB : Nonempty (B ≃* Multiplicative (ZMod 4)))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hD : Nonempty (D ≃* QuaternionGroup 2)) (hle : D ≤ B ⊔ C) : D = C := by
  obtain ⟨e⟩ := hD
  let f : QuaternionGroup 2 →* G := D.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := D.subtype_injective.comp e.symm.injective
  let first := f (QuaternionGroup.a 1)
  let second := f (QuaternionGroup.xa 0)
  have hfirstD : first ∈ D := (e.symm (QuaternionGroup.a 1)).property
  have hsecondD : second ∈ D := (e.symm (QuaternionGroup.xa 0)).property
  have hfirst4 : orderOf first = 4 := by
    rw [orderOf_injective f hf, QuaternionGroup.orderOf_a_one]
  have hsecond4 : orderOf second = 4 := by
    rw [orderOf_injective f hf, QuaternionGroup.orderOf_xa]
  have hnc : first * second ≠ second * first := by
    intro hh
    have heq : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 := hf (by simp only [map_mul]; exact hh)
    exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1) heq
  have hfirst : first ∈ C := c4_quaternion_noncentral_order_four_mem B C hB hC
    hinter hcomm first (hle hfirstD) hfirst4 ⟨second, hle hsecondD, hnc⟩
  have hsecond : second ∈ C := c4_quaternion_noncentral_order_four_mem B C hB hC
    hinter hcomm second (hle hsecondD) hsecond4 ⟨first, hle hfirstD, Ne.symm hnc⟩
  have hcontain : D ≤ C := by
    intro x hx
    let xx : D := ⟨x, hx⟩
    have hxf : f (e xx) = x := by simp [f, xx]
    rw [← hxf]
    cases e xx with
    | a index =>
      have hi : (QuaternionGroup.a index : QuaternionGroup 2) =
          QuaternionGroup.a 1 ^ index.val := by simp
      rw [hi, map_pow]
      exact C.pow_mem hfirst _
    | xa index =>
      have hi : (QuaternionGroup.xa index : QuaternionGroup 2) =
          QuaternionGroup.xa 0 * QuaternionGroup.a 1 ^ index.val := by simp
      rw [hi, map_mul, map_pow]
      exact C.mul_mem hsecond (C.pow_mem hfirst _)
  obtain ⟨eC⟩ := hC
  let : Finite C := Finite.of_injective eC eC.injective
  exact eq_of_le_of_card_ge hcontain
    ((Nat.card_congr eC.toEquiv).trans (Nat.card_congr e.toEquiv).symm).le

public theorem c4_quaternion_factor_invariant (B C : Subgroup G)
    (hB : Nonempty (B ≃* Multiplicative (ZMod 4)))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (e : G ≃* G) (hjoin : (B ⊔ C).map e.toMonoidHom = B ⊔ C) :
    C.map e.toMonoidHom = C := by
  apply c4_quaternion_subgroup_eq_factor B C _ hB hC hinter hcomm
  · obtain ⟨eC⟩ := hC
    exact ⟨(C.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eC⟩
  · exact (map_mono (show C ≤ B ⊔ C from le_sup_right)).trans_eq hjoin

public theorem c4_quaternion_normalizer_le_factor_normalizer (B C : Subgroup G)
    (hB : Nonempty (B ≃* Multiplicative (ZMod 4)))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) :
    normalizer (↑(B ⊔ C) : Set G) ≤ normalizer (C : Set G) := by
  intro element helement
  rw [mem_normalizer_iff_map_conj_eq] at helement ⊢
  exact c4_quaternion_factor_invariant B C hB hC hinter hcomm (MulAut.conj element) helement

public theorem c4_quaternion_commutator_le_factor [Finite G] (B C actors : Subgroup G)
    (hB : Nonempty (B ≃* Multiplicative (ZMod 4)))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hnormalize : actors ≤ normalizer (↑(B ⊔ C) : Set G)) :
    ⁅B ⊔ C, actors⁆ ≤ C := by
  have hnC := hnormalize.trans
    (c4_quaternion_normalizer_le_factor_normalizer B C hB hC hinter hcomm)
  have hnorm : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (hcomm b hb c hc).symm
  have hBcard : Nat.card B = 4 := by
    obtain ⟨eB⟩ := hB
    rw [Nat.card_congr eB.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hCcard : Nat.card C = 8 := by
    obtain ⟨eC⟩ := hC
    rw [Nat.card_congr eC.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hproduct := card_mul_eq_card_inf_mul_card_sup_of_normalizes C B hnorm
  rw [hCcard, hBcard, inf_comm C B, hinter, sup_comm C B] at hproduct
  have hindex : (C.subgroupOf (B ⊔ C)).index = 2 := by
    have hindexProduct := (C.subgroupOf (B ⊔ C)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show C ≤ B ⊔ C from le_sup_right)).toEquiv,
      hCcard] at hindexProduct
    omega
  apply Subgroup.commutator_le.mpr
  intro vector hvector actor hactor
  have hconj : actor * vector⁻¹ * actor⁻¹ ∈ B ⊔ C :=
    (mem_normalizer_iff.mp (hnormalize hactor) _).mp ((B ⊔ C).inv_mem hvector)
  have hsame : (⟨vector, hvector⟩ : (B ⊔ C : Subgroup G)) ∈ C.subgroupOf (B ⊔ C) ↔
      (⟨actor * vector⁻¹ * actor⁻¹, hconj⟩ : (B ⊔ C : Subgroup G)) ∈
        C.subgroupOf (B ⊔ C) := by
    change vector ∈ C ↔ actor * vector⁻¹ * actor⁻¹ ∈ C
    exact C.inv_mem_iff.symm.trans (mem_normalizer_iff.mp (hnC hactor) _)
  have hmul := ((C.subgroupOf (B ⊔ C)).mul_mem_iff_of_index_two hindex).mpr hsame
  change vector * (actor * vector⁻¹ * actor⁻¹) ∈ C at hmul
  simpa only [commutatorElement_def, mul_assoc] using hmul

end Subgroup

namespace Stellmacher
open Later
universe u

public theorem c4_quaternion_model_exists_normalized_factor
    {G : Type u} [Group G] (whole : Subgroup G)
    (hmodel : IsCentralProductModel whole C4 Q8) :
    ∃ B C : Subgroup G, IsModel B C4 ∧ IsModel C Q8 ∧ whole = B ⊔ C ∧
      Nat.card (B ⊓ C : Subgroup G) = 2 ∧
      (∀ b ∈ B, ∀ c ∈ C, b * c = c * b) ∧
      (B ⊓ C : Subgroup G) ≤ (Subgroup.center whole).map whole.subtype ∧
      Subgroup.normalizer (whole : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  obtain ⟨B, C, hB, hC, hwhole, hinter, hcomm, hcentral⟩ := hmodel
  refine ⟨B, C, hB, hC, hwhole, hinter, hcomm, hcentral, ?_⟩
  rw [hwhole]
  exact Subgroup.c4_quaternion_normalizer_le_factor_normalizer B C hB hC hinter hcomm

public theorem c4_quaternion_model_exists_commutator_bound
    {G : Type u} [Group G] [Finite G] (whole actors : Subgroup G)
    (hmodel : IsCentralProductModel whole C4 Q8)
    (hnormalize : actors ≤ Subgroup.normalizer (whole : Set G)) :
    ∃ C : Subgroup G, IsModel C Q8 ∧ C ≤ whole ∧
      Subgroup.normalizer (whole : Set G) ≤ Subgroup.normalizer (C : Set G) ∧
      ⁅whole, actors⁆ ≤ C := by
  obtain ⟨B, C, hB, hC, rfl, hinter, hcomm, _⟩ := hmodel
  exact ⟨C, hC, le_sup_right,
    Subgroup.c4_quaternion_normalizer_le_factor_normalizer B C hB hC hinter hcomm,
    Subgroup.c4_quaternion_commutator_le_factor B C actors hB hC hinter hcomm hnormalize⟩

end Stellmacher
