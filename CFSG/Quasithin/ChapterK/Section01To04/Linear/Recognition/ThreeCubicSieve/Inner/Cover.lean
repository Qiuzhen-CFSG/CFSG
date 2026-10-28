module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.TensorEstimates
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# Lifting the actual inner actor through the SL₃ center

An elementary subgroup of the full linear normalizer whose operators lie in
an SL₃ image lifts through its odd central kernel. The lift preserves the
literal operator image, binary rank, and common fixed codimension. Faithfulness
of the covering representation is unnecessary.

Source: the central-cover convention in Aschbacher–Smith K.3.2, printed
pp.454–456; the inner action in Guralnick–Malle, Classification of 2F-modules II,
author manuscript Proposition 4.7. The lift uses the existing coprime-kernel
Sylow theorem, and the kernel order divides the order-three scalar center.
-/

@[expose] public section
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Inner

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V)

/-- The kernel of the literal map to the action image has odd order. -/
theorem actionHom_kernel_coprime (hk : σ.ker ≤ Subgroup.center _) :
    Nat.Coprime 2 (Nat.card (actionHom σ).ker) := by
  have he : (actionHom σ).ker = σ.ker := by
    ext g
    change actionHom σ g = 1 ↔ σ g = 1
    constructor
    · intro h
      exact congrArg (fun x : actionImage σ => x.val.val) h
    · intro h
      apply Subtype.ext
      exact Units.ext h
  rw [he]
  exact (by decide : Nat.Coprime 2 3).of_dvd_right
    ((Subgroup.card_dvd_of_le hk).trans (Matrix.SL3.card_center_dvd_three B.Carrier))

/-- Lift the actual inner operator subgroup, preserving both sides of the
fixed-codimension inequality. -/
theorem exists_inner_lift (hk : σ.ker ≤ Subgroup.center _)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hi : A.map (linearNormalizer σ).subtype ≤ actionImage σ) :
    ∃ E : Subgroup SL(3,B.Carrier), IsElementaryTwo E ∧
      E.map σ.asGroupHom = A.map (linearNormalizer σ).subtype ∧
      rank E = rank A ∧ fixedCodim σ E = fixedCodim (normalizerRepresentation σ) A := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.2
  let C := A.map (linearNormalizer σ).subtype
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  let D := C.subgroupOf (actionImage σ)
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf hi
  obtain ⟨E, hE, he, hc⟩ := Subgroup.exists_elementaryAbelian_map_eq_of_surjective_coprime
    (actionHom σ) σ.asGroupHom.rangeRestrict_surjective (actionHom_kernel_coprime B σ hk) D
  have hm : E.map σ.asGroupHom = A.map (linearNormalizer σ).subtype := by
    have hh := congrArg (Subgroup.map (actionImage σ).subtype) he
    rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hi] at hh
    exact hh
  have hEn : E ≠ ⊥ := by
    intro hn
    rw [hn, Subgroup.map_bot] at hm
    exact hA.1 ((A.map_eq_bot_iff_of_injective (linearNormalizer σ).subtype_injective).mp hm.symm)
  have hr : rank E = rank A := by
    change Nat.log 2 (Nat.card E) = _
    rw [hc]
    change rank D = rank A
    rw [rank_subgroupOf hi, rank_map_injective _ (linearNormalizer σ).subtype_injective]
  refine ⟨E, ⟨hEn, hE⟩, hm, hr, ?_⟩
  have hf : fixedSpace σ E = fixedSpace (normalizerRepresentation σ) A := by
    calc
      fixedSpace σ E = fixedSpace (Units.coeHom _) (E.map σ.asGroupHom) :=
        by
          have heq : (Units.coeHom (Module.End (ZMod 2) V)).comp σ.asGroupHom = σ := by
            ext g v
            rfl
          rw [← fixedSpace_comp_map, heq]
      _ = fixedSpace (Units.coeHom _) (A.map (linearNormalizer σ).subtype) := by rw [hm]
      _ = fixedSpace (normalizerRepresentation σ) A :=
        (fixedSpace_comp_map _ (linearNormalizer σ).subtype A).symm
  unfold fixedCodim
  rw [hf]

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Inner
