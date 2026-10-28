module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.Partitions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.Transvections

/-!
# The conjugated transvection obstruction for the four-plus-three partition

An elementary critical actor inside `V` cannot contain a transvection if
an actual conjugate of `V` lies in the intrinsic two-core of the partition
stabilizer. The module identification makes the transvection a transposition.
Its conjugate has the same odd sign, contradicting the even two-core calculation.

This applies both to `Uδ ≤ Vδ` in case (1) of 13.8.8 and to the later
`Vβ` actor. The local source argument must supply the transvection, its
compatible natural-module identification, and the conjugate containment.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed pp.958–959 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
open Representation.BinaryOffender Subgroup
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E] (ρ : Representation (ZMod 2) H E)

/-- Transport the actual critical actor before using the two-core obstruction. -/
theorem no_conjugated_transvection_in_fourThreeCore
    (φ : H →* S7) (hφ : Function.Injective φ)
    (hmodel : HasNaturalSubmodule ρ φ)
    (P A V : Subgroup H) (hP : P.map φ = fourThreeStabilizer)
    (hA : IsElementaryTwo A) (hAV : A ≤ V) (y : H)
    (hplace : V.map (MulAut.conj y).toMonoidHom ≤ (pCore 2 P).map P.subtype)
    (ht : ∃ a ∈ A, a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) : False := by
  obtain ⟨j, hj, he⟩ := hmodel
  obtain ⟨a, ha, hne, hc⟩ := ht
  let : IsElementaryAbelian 2 A := hA.2
  have hs := swap_of_involution_fixedCodim_one ρ φ hφ j hj he a hne
    (elemPow_eq_one_of_isElementaryAbelian a ha) hc
  have hb : (MulAut.conj y) a ∈ (pCore 2 P).map P.subtype :=
    hplace (mem_map_of_mem _ (hAV ha))
  have heven := mapped_fourThreeCore_even φ hφ P hP hb
  have hsign : (φ ((MulAut.conj y) a)).sign = (φ a).sign := by
    simp only [MulAut.conj_apply, map_mul, map_inv]
    rw [mul_right_comm, mul_inv_cancel, one_mul]
  rw [hsign, hs.sign_eq] at heven
  norm_num at heven

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
