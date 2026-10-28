module

public import Theory.Representation.GoldschmidtONan.OddReduction.Induction
public import Theory.Representation.GoldschmidtONan.OddReduction.SylowKernel
public import Theory.Representation.BinarySingerNormalizer

/-!
# The complete odd-order induction step for Goldschmidt–O’Nan pairs

The intrinsic Singer-normalizer facts discharge the two inputs to the Sylow
kernel argument. Its cyclic Sylow witness feeds Burnside transfer and the
proved proper-subgroup induction argument, giving odd order. All action,
fixed-space and normalizer witnesses are the actual ones of the given Input.

Source: GLS, Number 2, Chapter C, Proposition 14.2, Step 3,
`refs/KGroup/GLS2/ChapterC.tex`. The only induction premise is the explicit
classification of proper subgroups; the full assembly constructs it.
-/

public section

namespace Representation.GoldschmidtONan.OddReduction

variable {X V : Type*} [Group X] [Finite X]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

theorem odd_of_geometry (h : Input ρ Y)
    (hsub : SuborbitGeometry ρ Y) (hgeom : TransitiveGeometry ρ Y)
    (hIH : ProperSubgroupCases ρ) : Odd (Nat.card X) := by
  obtain ⟨S, hS⟩ := exists_cyclic_sylow_of_normalizer_facts h hsub hgeom
    (fun C P hC hreg hP hN => by
      let _ := hC
      exact BinarySingerNormalizer.isCyclic_of_isPGroup_le_normalizer C
        (fun v w hv hw => hreg v hv w hw) P hP hN)
    (fun C t hC hreg ht ht2 htN => by
      let _ := hC
      exact BinarySingerNormalizer.fixedSpace_card_sq_le C
        (fun v w hv hw => hreg v hv w hw) t ht ht2 htN)
  exact odd_of_cyclic_sylow h hgeom.1 hIH S hS

end Representation.GoldschmidtONan.OddReduction
