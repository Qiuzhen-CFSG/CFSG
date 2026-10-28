module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.FixedPoints

/-!
# From the two intrinsic cubic counts to the local Sylow group

The equality U = O₂(H) identifies the kernel of the restricted actor map
with the fixed subgroup in U, through an inclusion-preserving equivalence.
The preceding image and fixed-point calculations give
|C_H(D_H)| = 2 |C_{U/Z}(D_H)| |C_{H*}(D_H*)|.
The intrinsic model counts four and six therefore give order 48 and a
Sylow two-group of order sixteen, with its original ambient embedding.

The two model counts are explicit remaining premises. This conditional
assembly is not yet a proof of the source local-centralizer order.
Source: Aschbacher–Smith 15.3.60, printed p.1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal
variable {G : Type*} [Group G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- The centralizer-map kernel is exactly the fixed subgroup of the actual two-core. -/
noncomputable def centralizerKernelEquiv (d : Recognition Z ZS)
    (P : Sylow 3 (centralizerH Z)) :
    ((pCore 2 (centralizerH Z)).subgroupOf
      (centralizer ((P : Subgroup (centralizerH Z)) : Set (centralizerH Z)))) ≃*
      kernelFixed Z ZS d P where
  toFun x := ⟨⟨((x.val : centralizerH Z) : G), by
    rw [d.core_eq]
    exact mem_map_of_mem (centralizerH Z).subtype x.property⟩, x.val.property⟩
  invFun u := ⟨⟨⟨(u.val : G), closureU_le_H d.subgroup_le u.val.property⟩, u.property⟩, by
    rw [← closure_subgroupOf_H_eq_core Z ZS d.core_eq]
    exact u.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The local centralizer order factors through its proved kernel and image. -/
lemma centralizer_card_formula [Finite G] (d : Recognition Z ZS)
    (P : Sylow 3 (centralizerH Z)) :
    Nat.card (centralizer ((P : Subgroup (centralizerH Z)) : Set (centralizerH Z))) =
      (2 * Nat.card (quotientFixed Z ZS P)) *
        Nat.card (centralizer (((P : Subgroup (centralizerH Z)).map
          (QuotientGroup.mk' (pCore 2 (centralizerH Z)))) : Set (ActorQuotient Z))) := by
  let N := pCore 2 (centralizerH Z)
  let C := centralizer ((P : Subgroup (centralizerH Z)) : Set (centralizerH Z))
  let q := QuotientGroup.mk' N
  have h := (N.subgroupOf C).card_mul_index
  change Nat.card (N.subgroupOf C) * N.relIndex C = Nat.card C at h
  have hi : N.relIndex C = Nat.card (C.map q) := by
    simpa only [q, QuotientGroup.ker_mk'] using relIndex_ker C q
  rw [hi, actor_centralizer_image, Nat.card_congr (centralizerKernelEquiv Z ZS d P).toEquiv,
    kernelFixed_card] at h
  exact h.symm

/-- Construct the Sylow group and its ambient image once the two intrinsic model counts are supplied. -/
lemma sylow_centralizer_of_model_counts [Finite G] (d : Recognition Z ZS)
    (P : Sylow 3 (centralizerH Z))
    (hfixed : Nat.card (quotientFixed Z ZS P) = 4)
    (hactor : Nat.card (centralizer (((P : Subgroup (centralizerH Z)).map
      (QuotientGroup.mk' (pCore 2 (centralizerH Z)))) : Set (ActorQuotient Z))) = 6) :
    ∃ S : Sylow 2 (centralizer ((P : Subgroup (centralizerH Z)) : Set (centralizerH Z))),
      Nat.card S = 16 ∧
      ∃ R : Subgroup G,
        R = ((S : Subgroup _).map
          (centralizer ((P : Subgroup (centralizerH Z)) : Set (centralizerH Z))).subtype).map
          (centralizerH Z).subtype ∧
        IsPGroup 2 R ∧ Nat.card R = 16 ∧
        R ≤ centralizer (((P : Subgroup (centralizerH Z)).map (centralizerH Z).subtype) : Set G) := by
  let C := centralizer ((P : Subgroup (centralizerH Z)) : Set (centralizerH Z))
  have hc : Nat.card C = 48 := by
    rw [centralizer_card_formula Z ZS d P, hfixed, hactor]
  let S : Sylow 2 C := Sylow.nonempty.some
  have hS : Nat.card S = 16 := by
    rw [S.card_eq_multiplicity, hc]
    decide +kernel
  let R := ((S : Subgroup C).map C.subtype).map (centralizerH Z).subtype
  refine ⟨S, hS, R, rfl, (S.isPGroup'.map C.subtype).map (centralizerH Z).subtype, ?_, ?_⟩
  · rw [card_map_of_injective (centralizerH Z).subtype_injective,
      card_map_of_injective C.subtype_injective]
    exact hS
  · rintro _ ⟨c, ⟨s, hs, rfl⟩, rfl⟩ _ ⟨p, hp, rfl⟩
    exact congrArg Subtype.val (s.property p hp)
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal
