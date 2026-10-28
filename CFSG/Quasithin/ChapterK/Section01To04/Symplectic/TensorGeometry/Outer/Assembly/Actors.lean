module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.Transport

/-!
# Native intersections of elementary outer actors

In the actual outer automorphism quotient every outer involution has the same
field-involution image. Thus the product of two outer involutions is native,
and an elementary actor containing an outer involution meets the component in
index two. Conjugating the component marking by the matrix which normalizes
the outer operator gives the literal native subgroup used by the Hermitian
model. Its order is half the original actor's order, hence the cube of the
Schur-field order in the maximal-rank case.

Source: Aschbacher–Smith, K.3.4.2, printed p.457.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Assembly
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
  (L : Subgroup G) [L.Normal] [IsIrreducible (ρ.comp L.subtype)]
  [Field F] [Algebra (SchurField (ρ.comp L.subtype)) F]

private theorem outer_mul_mem {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (a t : G) (ha : orderOf a = 2) (hat : a ∉ L) (ht : orderOf t = 2) (htt : t ∉ L) :
    a * t ∈ L := by
  let : CharP (SchurField (ρ.comp L.subtype)) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap
    (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  let α := extensionAction L h.groupEquiv.symm
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))
  have hconj (c : Sp F) : q (MulAut.conj c) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := Transport.outer_group_normal_form ρ L hS hs h a ha hat
  obtain ⟨d, hd⟩ := Transport.outer_group_normal_form ρ L hS hs h t ht htt
  have he : q (α a) = q (α t) := by
    change q (extensionAction L h.groupEquiv.symm a) = q (extensionAction L h.groupEquiv.symm t)
    rw [hc, hd]
    simp only [map_mul, map_inv, hconj, one_mul, inv_one, mul_one]
  have ht2 : t * t = 1 := by simpa only [← pow_two, ht] using pow_orderOf_eq_one t
  apply (extensionAction_mem_inner_iff L h.groupEquiv.symm
    (component_centralizer_eq_bot ρ L hS h.groupEquiv.symm) (a * t)).mp
  apply (QuotientGroup.eq_one_iff _).mp
  change q (α (a * t)) = 1
  rw [map_mul, map_mul, he, ← map_mul, ← map_mul, ht2, map_one, map_one]

theorem native_index_two {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (t : G) (htA : t ∈ A) (hout : t ∉ L) : (L.comap A.subtype).index = 2 := by
  let : IsElementaryAbelian 2 A := hA.2
  have ht : orderOf t = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t htA) (fun he => hout (he ▸ L.one_mem))
  apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨⟨t, htA⟩, hout, ?_⟩
  intro a
  by_cases ha : a.val ∈ L
  · exact Or.inr ha
  · exact Or.inl (outer_mul_mem ρ L hS hs h a.val t
      (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a.val a.property)
        (fun he => ha (he ▸ L.one_mem))) ha ht hout)

noncomputable def nativeMark {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (c : Sp F) : L ≃* Sp F := h.groupEquiv.trans (MulAut.conj c⁻¹)

noncomputable def nativeActor {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (c : Sp F) (A : Subgroup G) : Subgroup (Sp F) :=
  (A.comap L.subtype).map (nativeMark ρ L h c).toMonoidHom

theorem nativeActor_card_mul_two {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (c : Sp F) (A : Subgroup G) (hA : IsElementaryTwo A)
    (t : G) (htA : t ∈ A) (hout : t ∉ L) :
    Nat.card (nativeActor ρ L h c A) * 2 = Nat.card A := by
  have he : Nat.card (A.comap L.subtype) = Nat.card (L.comap A.subtype) :=
    Nat.card_congr {
      toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [nativeActor, Subgroup.card_map_of_injective (nativeMark ρ L h c).injective, he,
    ← native_index_two ρ L hS hs h A hA t htA hout]
  exact (L.comap A.subtype).card_mul_index

theorem nativeActor_ne_bot {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (c : Sp F) (A : Subgroup G) (hA : IsElementaryTwo A)
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L) (hproper : zpowers t < A) :
    nativeActor ρ L h c A ≠ ⊥ := by
  intro he
  have hc := nativeActor_card_mul_two ρ L hS hs h c A hA t
    (hproper.le (mem_zpowers t)) hout
  rw [he, Subgroup.card_bot] at hc
  have heq : zpowers t = A := Subgroup.eq_of_le_of_card_ge hproper.le (by
    rw [Nat.card_zpowers, ht]
    omega)
  exact hproper.ne heq

theorem nativeActor_card_cube {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (c : Sp F) (A : Subgroup G) (hA : IsElementaryTwo A)
    (t : G) (htA : t ∈ A) (hout : t ∉ L) (hr : rank A = 3 * s + 1) :
    Nat.card (nativeActor ρ L h c A) = Nat.card (SchurField (ρ.comp L.subtype)) ^ 3 := by
  have hc := nativeActor_card_mul_two ρ L hS hs h c A hA t htA hout
  rw [hA.card_eq_two_pow_rank, hr, pow_succ] at hc
  rw [h.schur_card, ← pow_mul, Nat.mul_comm s 3]
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) hc

end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Assembly
