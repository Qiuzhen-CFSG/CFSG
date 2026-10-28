module

public import Theory.Representation.BinaryOffender.FixedSpaceSpan
public import Mathlib.GroupTheory.Index

/-!
# Elementary subgroups and their image on a normal kernel

The intersection of an abelian subgroup with a homomorphism kernel embeds
into the fixed space of its image. The first isomorphism theorem then gives
the offender inequality when the subgroup is at least as large as the kernel
module. Kernel coordinates retain the actual commuting elements, so an
unrelated representation of the quotient cannot be substituted.

This is the rank argument at the start of Aschbacher--Smith H.15.5,
combined manuscript (1 March 2004), printed p.401.
-/

@[expose] public section

open Representation.BinaryOffender
open scoped IsMulCommutative

namespace MathieuCode.M22ElementaryFour
variable {G D V : Type*} [Group G] [Group D] [Finite G] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The image of an elementary subgroup at least as large as the kernel module
is an offender. The injection into its fixed space is constructed from the
commuting intersection with the kernel, rather than assumed. -/
theorem image_offender_of_kernel_coordinates (q : G →* D) (ρ : Representation (ZMod 2) D V)
    (e : q.ker ≃ V)
    (he : ∀ (a : G) (k : q.ker), Commute a k.val → ρ (q a) (e k) = e k)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card V ≤ Nat.card A) (hne : ¬ A ≤ q.ker) :
    IsOffender ρ (A.map q) := by
  let := hA
  let : Finite V := Finite.of_equiv q.ker e
  have hel : IsElementaryTwo (A.map q) := ⟨by
    intro hb
    apply hne
    intro a ha
    have hh := Subgroup.mem_map_of_mem q ha
    rw [hb, Subgroup.mem_bot] at hh
    exact hh, IsElementaryAbelian.map q⟩
  let f := q.comp A.subtype
  let j : f.ker → fixedSpace ρ (A.map q) := fun k =>
    ⟨e ⟨k.val.val, k.property⟩, by
      rintro ⟨_, a, ha, rfl⟩
      exact he a ⟨k.val.val, k.property⟩
        (show Commute a k.val.val from
          congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) k.val))⟩
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun k : q.ker => (k : G)) (e.injective (congrArg Subtype.val hxy))
  have hb := Nat.card_le_card_of_injective j hj
  have hf : Nat.card A = Nat.card (A.map q) * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (s := f.ker),
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    congr 1
    exact congrArg Nat.card (by simp [f, MonoidHom.range_comp])
  have hbound : Nat.card V ≤ Nat.card (A.map q) * Nat.card (fixedSpace ρ (A.map q)) := by
    exact hcard.trans (hf.trans_le (Nat.mul_le_mul_left _ hb))
  rw [hel.card_eq_two_pow_rank, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ (A.map q)),
    show Nat.card (ZMod 2) = 2 by simp [Nat.card_eq_fintype_card], ← pow_add] at hbound
  have hr := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound
  exact ⟨hel, (fixedCodim_le_rank_iff ρ _).mpr hr⟩
end MathieuCode.M22ElementaryFour

namespace MathieuCode.M22ElementaryFour
variable {G D : Type*} [Group G] [Group D]

theorem map_conj_image (q : G →* D) (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).map q =
      (A.map q).map (MulAut.conj (q g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp

theorem card_image_mul_card_inf_kernel (q : G →* D) (A : Subgroup G) :
    Nat.card (A.map q) * Nat.card (A ⊓ q.ker : Subgroup G) = Nat.card A := by
  let f := q.comp A.subtype
  let e : f.ker ≃ (A ⊓ q.ker : Subgroup G) :=
    { toFun k := ⟨k.val.val, k.val.property, k.property⟩
      invFun k := ⟨⟨k.val, k.property.1⟩, k.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hr : f.range = A.map q := by simp [f, MonoidHom.range_comp]
  rw [← Nat.card_congr e, ← hr,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

theorem card_intersection_of_card_image_two (q : G →* D) (A : Subgroup G)
    (hA : Nat.card A = 16) (himage : Nat.card (A.map q) = 2) :
    Nat.card (A ⊓ q.ker : Subgroup G) = 8 := by
  have h := card_image_mul_card_inf_kernel q A
  rw [hA, himage] at h
  omega
end MathieuCode.M22ElementaryFour
