module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.Actors
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.FixedSpace.Transport
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.FixedSpace.Common

/-!
# Tensor-swap estimates on the original binary representation

The actual realization transports the outer actor to interchange and a
commuting nonidentity inner involution to a nontrivial diagonal involution.
The tensor calculations, transported back through that equivalence and the
original component Schur field, give displacement at least three and common
fixed codimension at least half the binary degree. The quotient formula uses
the literal intersection of the two original displacement kernels.

These discharge the two numerical premises of
`degree_le_of_tensorSwap_estimates`. The final consumer below applies the
published group reduction with those estimates proved, retaining only the
construction of actual tensor-swap realizations as an external premise.

Source: Guralnick--Malle, Classification of 2F-modules II, Section 3.5 and
Proposition 6.2(2--3); Aschbacher--Smith K.3.4, printed pp.456--457.
-/

public section

namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur
open Module Representation Representation.FrobeniusTensor
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  [IsIrreducible (ρ.comp L.subtype)] {t : G} {ht : IsSchurLinear ρ L t}

namespace TensorSwapRealization
variable (R : TensorSwapRealization ρ L t ht)

/-- The exact binary displacement is the Schur degree times `size.choose 2`. -/
theorem binary_displacement_finrank :
    finrank (ZMod 2) (ρ t - 1).range =
      finrank (ZMod 2) (FrobeniusTensor.SchurField (ρ.comp L.subtype)) * R.size.choose 2 := by
  rw [FixedSpace.binary_range_finrank ρ L t ht]
  congr 1
  calc
    _ = finrank (Closure (ρ.comp L.subtype))
        (FixedSpace.Tensor.flip (Closure (ρ.comp L.subtype)) R.size - 1).range :=
      FixedSpace.finrank_range_sub_one_equiv R.equivalence _ _ R.outer_action
    _ = _ := FixedSpace.Tensor.finrank_range_flip _ _

include R in
/-- Tensor interchange excludes an outer actor of moved dimension at most two. -/
theorem three_le_displacement_finrank : 3 ≤ finrank (ZMod 2) (ρ t - 1).range := by
  rw [R.binary_displacement_finrank]
  exact (le_trans (by decide : 3 ≤ Nat.choose 4 2)
    (Nat.choose_le_choose 2 R.four_le)).trans
    (Nat.le_mul_of_pos_left _ (schurField_finrank_pos (ρ.comp L.subtype)))

/-- The binary degree of the realized tensor square. -/
theorem binary_finrank : finrank (ZMod 2) V =
    finrank (ZMod 2) (FrobeniusTensor.SchurField (ρ.comp L.subtype)) * (R.size * R.size) := by
  rw [binary_finrank_eq (ρ.comp L.subtype), R.equivalence.finrank_eq]
  congr 1
  exact FixedSpace.Tensor.finrank_space _ _

/-- Transport both literal fixed equations through the realization and the original Schur field. -/
theorem commonFixed_finrank (u : L)
    (f : Module.End (Closure (ρ.comp L.subtype)) (Fin R.size → Closure (ρ.comp L.subtype)))
    (hf : ∀ v, R.equivalence (absoluteRep (ρ.comp L.subtype) u v) =
      TensorProduct.map f f (R.equivalence v)) :
    finrank (ZMod 2) ↥((ρ t - 1).ker ⊓ (ρ u - 1).ker) =
      finrank (ZMod 2) (FrobeniusTensor.SchurField (ρ.comp L.subtype)) *
        finrank (Closure (ρ.comp L.subtype))
          ↥((FixedSpace.Tensor.flip (Closure (ρ.comp L.subtype)) R.size - 1).ker ⊓
            (TensorProduct.map f f - 1).ker) := by
  rw [FixedSpace.binary_commonFixed_finrank ρ L t u ht
    (isSchurLinear_of_mem ρ L u.property), absoluteActor_of_mem]
  congr 1
  exact (FixedSpace.commonFixedEquiv R.equivalence _ _ _ _ R.outer_action hf).finrank_eq

/-- The original quotient codimension is the Schur degree times the tensor quotient codimension. -/
theorem pairFixedCodim_eq (u : L)
    (f : Module.End (Closure (ρ.comp L.subtype)) (Fin R.size → Closure (ρ.comp L.subtype)))
    (hf : ∀ v, R.equivalence (absoluteRep (ρ.comp L.subtype) u v) =
      TensorProduct.map f f (R.equivalence v)) :
    pairFixedCodim ρ t u =
      finrank (ZMod 2) (FrobeniusTensor.SchurField (ρ.comp L.subtype)) *
        finrank (Closure (ρ.comp L.subtype))
          (FixedSpace.Tensor.Space (Closure (ρ.comp L.subtype)) R.size ⧸
            ((FixedSpace.Tensor.flip (Closure (ρ.comp L.subtype)) R.size - 1).ker ⊓
              (TensorProduct.map f f - 1).ker)) := by
  have hcommon := R.commonFixed_finrank u f hf
  have hwhole := R.binary_finrank
  have hbinary := ((ρ t - 1).ker ⊓ (ρ u - 1).ker).finrank_quotient_add_finrank
  have htensor := ((FixedSpace.Tensor.flip (Closure (ρ.comp L.subtype)) R.size - 1).ker ⊓
    (TensorProduct.map f f - 1).ker).finrank_quotient_add_finrank
  rw [FixedSpace.Tensor.finrank_space] at htensor
  have hscaled := congrArg (fun m => finrank (ZMod 2) (FrobeniusTensor.SchurField (ρ.comp L.subtype)) * m) htensor
  dsimp [pairFixedCodim]
  rw [Nat.mul_add] at hscaled
  omega

private theorem degree_le_twice_pairFixedCodim_of_tensor_bound (u : L)
    (f : Module.End (Closure (ρ.comp L.subtype)) (Fin R.size → Closure (ρ.comp L.subtype)))
    (hf : ∀ v, R.equivalence (absoluteRep (ρ.comp L.subtype) u v) =
      TensorProduct.map f f (R.equivalence v))
    (hbound : 2 * finrank (Closure (ρ.comp L.subtype))
      ↥((FixedSpace.Tensor.flip (Closure (ρ.comp L.subtype)) R.size - 1).ker ⊓
        (TensorProduct.map f f - 1).ker) ≤ R.size * R.size) :
    finrank (ZMod 2) V ≤ 2 * pairFixedCodim ρ t u := by
  let S := (FixedSpace.Tensor.flip (Closure (ρ.comp L.subtype)) R.size - 1).ker ⊓
    (TensorProduct.map f f - 1).ker
  have hq := S.finrank_quotient_add_finrank
  rw [FixedSpace.Tensor.finrank_space] at hq
  have hmodel : R.size * R.size ≤ 2 * finrank (Closure (ρ.comp L.subtype))
      (FixedSpace.Tensor.Space (Closure (ρ.comp L.subtype)) R.size ⧸ S) := by
    change 2 * finrank (Closure (ρ.comp L.subtype)) S ≤ R.size * R.size at hbound
    omega
  rw [R.binary_finrank, R.pairFixedCodim_eq u f hf]
  exact (Nat.mul_le_mul_left (finrank (ZMod 2) (FrobeniusTensor.SchurField (ρ.comp L.subtype))) hmodel).trans_eq
    (Nat.mul_left_comm _ 2 _)

include R in
/-- The exact common-fixed-codimension estimate consumed by the outer degree argument. -/
theorem degree_le_twice_pairFixedCodim (u : L) (hu2 : u ^ 2 = 1) (hune : u ≠ 1)
    (hcomm : Commute t (u : G)) :
    finrank (ZMod 2) V ≤ 2 * pairFixedCodim ρ t u := by
  obtain ⟨f, hf2, hfne, hf⟩ := R.inner_action u hu2 hcomm
  apply R.degree_le_twice_pairFixedCodim_of_tensor_bound u f hf
  exact FixedSpace.Tensor.common_fixed_bound R.size (by have hh := R.four_le; omega)
    f hf2 (hfne hune)
end TensorSwapRealization

open Representation.BinaryOffender Theory.SpecificGroups.SymplecticFour

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Finite G]

/-- The outer degree bound with both tensor estimates discharged. Only construction of the actual realizations remains explicit. -/
theorem degree_le_of_tensorSwap_realizations {K : GroupClass}
    (h : SourceHypothesis K ρ L) {r : ℕ} (hr : 1 < r) (hF : Nat.card F = 2 ^ r)
    (e : L ⧸ Subgroup.center L ≃* Sp F) (A : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hnot : ¬ A ≤ L)
    (hrank : rank A ≤ 3 * r + 1) (hcodim : fixedCodim ρ A ≤ 2 * rank A)
    (hlinear : ∀ a ∈ A, IsSchurLinear ρ L a)
    (hmodel : ∀ t ∈ A, t ∉ L → t ^ 2 = 1 → ∀ ht : IsSchurLinear ρ L t,
      Nonempty (TensorSwapRealization ρ L t ht)) :
    finrank (ZMod 2) V ≤ 12 * r + 4 := by
  apply degree_le_of_outer_estimates h hr hF e A hA hnot hrank hcodim hlinear
  · intro s hs hsL hs2 hsl
    obtain ⟨R⟩ := hmodel s hs hsL hs2 hsl
    exact R.three_le_displacement_finrank
  · intro s hs u _ hsL hs2 huL hune hu2 hsu hsl
    obtain ⟨R⟩ := hmodel s hs hsL hs2 hsl
    exact R.degree_le_twice_pairFixedCodim ⟨u, huL⟩ (Subtype.ext hu2)
      (fun he => hune (congrArg Subtype.val he)) hsu
end CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur
