module

public import Stellmacher.Recognition.NormalEightQuaternionDihedralSetup
public import Theory.GroupTheory.QuaternionCentralProductInvolutionCorrection
public import Theory.GroupTheory.QuaternionCentralProductCentralizerSquare
public import Theory.GroupTheory.QuaternionCentralProductInnerOuterFixed

/-!
# The quaternion fixed-eight witness in the actual Sylow group

The supplied quaternion factors belong to the quotient core. Transport them
through the actual-core equivalence into the original Sylow group. Their join
is the original core preimage, and their centralizer lies in that join. The
dihedral quotient forces the Sylow group to have order 256.

Select an outside centralizer element with central square, then correct it to
an involution whose restrictions to the factors are inner and outer
respectively. The intrinsic fixed-subgroup calculation gives a nonabelian
centralizer of order eight in the core. This route needs no fusion or
elementary-rank hypothesis.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, case (c), printed p.392.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- A quaternion core and dihedral-eight quotient give Sylow order 256. -/
public theorem quaternion_dihedral_sylow_card (S : Sylow 2 G)
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (he : Nonempty ((S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4)) :
    Nat.card S = 256 := by
  obtain ⟨e⟩ := he
  have hi : (omegaCorePreimage S).index = 8 := by
    change Nat.card (S ⧸ omegaCorePreimage S) = 8
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hc := (omegaCorePreimage S).card_mul_index
  rw [card_omegaCorePreimage, hH, hi] at hc
  omega

/-- The quotient-core factors give actual quaternion subgroups of the Sylow,
with their product equal to the self-centralizing actual core. -/
public theorem quaternion_dihedral_actual_factors
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) :
    ∃ B' C' : Subgroup S,
      Nonempty (B' ≃* QuaternionGroup 2) ∧
      Nonempty (C' ≃* QuaternionGroup 2) ∧
      B' ⊔ C' = omegaCorePreimage S ∧
      Nat.card (B' ⊓ C' : Subgroup S) = 2 ∧
      (∀ b ∈ B', ∀ c ∈ C', b * c = c * b) ∧
      (B' ⊔ C').Normal ∧ Nat.card (B' ⊔ C' : Subgroup S) = 32 ∧
      centralizer ((B' ⊔ C' : Subgroup S) : Set S) ≤ B' ⊔ C' := by
  let P := omegaCorePreimage S
  let e := (omegaCorePreimageEquiv S).symm
  let f := P.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.injective
  have hrange : f.range = P := by
    ext s
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).property
    · intro hs
      obtain ⟨x, hx⟩ := e.surjective ⟨s, hs⟩
      exact ⟨x, congrArg Subtype.val hx⟩
  have hj : B.map f ⊔ C.map f = P := by
    rw [← Subgroup.map_sup, hjoin, ← MonoidHom.range_eq_map]
    exact hrange
  have hself : centralizer (P : Set S) ≤ P := by
    intro s hs
    apply omegaQuotient_centralizer_pCore_le hN S hZ
    intro x hx
    rw [← omegaCorePreimage_map S] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    simpa only [map_mul] using congrArg (omegaQuotientHom S) (hs k hk)
  refine ⟨B.map f, C.map f, ?_, ?_, hj, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨model⟩ := hB
    exact ⟨(B.equivMapOfInjective f hf).symm.trans model⟩
  · obtain ⟨model⟩ := hC
    exact ⟨(C.equivMapOfInjective f hf).symm.trans model⟩
  · rw [← map_inf _ _ f hf, card_map_of_injective hf, hinter]
  · rintro b ⟨x, hx, rfl⟩ c ⟨y, hy, rfl⟩
    simpa only [map_mul] using congrArg f (hcomm x hx y hy)
  · rw [hj]
    infer_instance
  · rw [hj]
    exact (card_omegaCorePreimage S).trans hH
  · simpa only [hj] using hself

/-- Selecting a central square and computing the inner/outer fixed subgroup
suffice for the required witness, with no fusion or rank bound in the assembly. -/
public theorem quaternion_dihedral_witness_of_local_calculations
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (he : Nonempty ((S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4))
    (hselection : ∀ B' C' : Subgroup S,
      Nonempty (B' ≃* QuaternionGroup 2) → Nonempty (C' ≃* QuaternionGroup 2) →
      Nat.card (B' ⊓ C' : Subgroup S) = 2 →
      (∀ b ∈ B', ∀ c ∈ C', b * c = c * b) →
      (B' ⊔ C').Normal → Nat.card (B' ⊔ C' : Subgroup S) = 32 →
      centralizer ((B' ⊔ C' : Subgroup S) : Set S) ≤ B' ⊔ C' →
      Nat.card S = 256 →
      ∃ k : S, k ∉ B' ⊔ C' ∧
        k ∈ normalizer ((B' ⊔ C' : Subgroup S) : Set S) ∧
        k ∈ centralizer (B' : Set S) ∧ k ^ 2 ∈ B' ⊓ C')
    (hfixed : ∀ B' C' : Subgroup S,
      Nonempty (B' ≃* QuaternionGroup 2) → Nonempty (C' ≃* QuaternionGroup 2) →
      Nat.card (B' ⊓ C' : Subgroup S) = 2 →
      (∀ b ∈ B', ∀ c ∈ C', b * c = c * b) →
      ∀ l : S, orderOf l = 2 →
        l ∈ normalizer (B' : Set S) → l ∈ normalizer (C' : Set S) →
        (∃ b ∈ B', ∀ x ∈ B', l * x * l⁻¹ = b * x * b⁻¹) →
        (¬ ∃ c ∈ C', ∀ x ∈ C', l * x * l⁻¹ = c * x * c⁻¹) →
        ¬ IsMulCommutative ((B' ⊔ C') ⊓ centralizer ({l} : Set S) : Subgroup S) ∧
        Nat.card ((B' ⊔ C') ⊓ centralizer ({l} : Set S) : Subgroup S) = 8) :
    ∃ l : S, orderOf l = 2 ∧
      ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) ∧
      Nat.card (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) = 8 := by
  obtain ⟨B', C', hB', hC', hj, hi, hc, hn, hcard, hself⟩ :=
    quaternion_dihedral_actual_factors hN S hZ hH B C hB hC hjoin hinter hcomm
  obtain ⟨k, hkout, hkn, hkc, hksq⟩ :=
    hselection B' C' hB' hC' hi hc hn hcard hself
      (quaternion_dihedral_sylow_card S hH he)
  obtain ⟨l, hl, _, hlnB, hlnC, hinner, houter⟩ :=
    exists_involution_inner_outer_of_quaternion_centralizing_square
      B' C' hB' hC' hi hc hself k hkout hkn hkc hksq
  have hf := hfixed B' C' hB' hC' hi hc l hl hlnB hlnC hinner houter
  rw [hj] at hf
  exact ⟨l, hl, hf⟩

/-- The quaternion central product with dihedral-eight quotient supplies an
involution whose fixed subgroup in the actual core is nonabelian of order eight.
This is the witness used in the dihedral involution geometry. -/
public theorem quaternion_dihedral_fixed_eight_witness
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (he : Nonempty ((S ⧸ omegaCorePreimage S) ≃* DihedralGroup 4)) :
    ∃ l : S, orderOf l = 2 ∧
      ¬ IsMulCommutative (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) ∧
      Nat.card (omegaCorePreimage S ⊓ centralizer ({l} : Set S) : Subgroup S) = 8 := by
  apply quaternion_dihedral_witness_of_local_calculations
    hN S hZ hH B C hB hC hjoin hinter hcomm he
  · intro B' C' hB' hC' hi hc hn hcard hself hS
    exact exists_centralizing_square_of_quaternion_central_product
      S.isPGroup' hS B' C' hB' hC' hi hc hn hcard hself
  · exact quaternion_central_product_inner_outer_fixed

end Stellmacher.Recognition.NormalEightNonnormalImage
