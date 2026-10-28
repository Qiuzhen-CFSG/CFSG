module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionFixedLine
public import Theory.Representation.BinaryPermutationAlternatingActions

/-!
# The literal alternating-eight fusion configuration of 12.2.16

After the module-orbit reductions, the original V is the even-weight
permutation core of A₈. The chosen v has weight two, z is the constant
word, and the adjusted outside conjugator sends v to vz while normalizing
C_T(v), a Sylow subgroup of C_G(v). The structure below records exactly
these intermediate data with the original quotient and coordinate maps.
Its existence is an outstanding source reduction, not a hypothesis of
12.2.16 or a substitute for the seven module alternatives.

The fixed involution belongs to Ω₁(Z(C_T(v))) by the original Sylow
placement and the structural theorem. The already proved fixed-line fusion
then contradicts an outside conjugator as soon as this central omega lies
in V. Proving that containment is the remaining A₈ module-geometric step.
Source: Aschbacher--Smith 12.2.16, final paragraph, printed p.800.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

/-- The source configuration after orbit selection and Sylow adjustment. -/
structure AlternatingEightFusion (T : Sylow 2 G) (L V : Subgroup G) where
  groupEquiv : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 8)
  vectorEquiv : V ≃* Multiplicative (BinaryPermutation.core (Fin 8))
  intertwines : ∀ (l : L) (w : V),
    ((vectorEquiv.symm (Multiplicative.ofAdd
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8)
        (groupEquiv (QuotientGroup.mk' (pCore 2 L) l))
        (vectorEquiv w).toAdd))) : G) = (l : G) * (w : G) * (l : G)⁻¹
  v : V
  z : V
  weight_two : (Finset.univ.filter fun i : Fin 8 => (vectorEquiv v).toAdd.val i ≠ 0).card = 2
  constant : ∀ i : Fin 8, (vectorEquiv z).toAdd.val i = 1
  z_ne : (z : G) ≠ 1
  z_fixed : (z : G) ∈ centralizer (L : Set G)
  fixed_line : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = (z : G)
  sylow : Sylow 2 (centralizer ({(v : G)} : Set G))
  sylow_image : (sylow : Subgroup (centralizer ({(v : G)} : Set G))).map
    (centralizer ({(v : G)} : Set G)).subtype =
      (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)
  g : G
  outside : g ∉ normalizer (L : Set G)
  conjugates : g * (v : G) * g⁻¹ = (v : G) * (z : G)
  normalizes : g ∈ normalizer
    ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G) : Set G)

namespace AlternatingEightFusion
variable (C : AlternatingEightFusion T L V)

/-- The literal point centralizer in the original T. -/
abbrev pointSylow : Subgroup G := (T : Subgroup G) ⊓ centralizer ({(C.v : G)} : Set G)

/-- The original fixed involution lies in the actual central omega subgroup. -/
theorem fixed_mem_pointSylow_omega
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) : (C.z : G) ∈ omegaCenterIn C.pointSylow := by
  let := D.elementary
  have hMC := normalizer_centralizes_fixed_line h D structural
    C.z.property C.z_ne C.z_fixed C.fixed_line
  apply (mem_omegaCenterIn_iff C.pointSylow (C.z : G)).mpr
  refine ⟨⟨D.le_sylow C.z.property,?_⟩,?_,
    elemPow_eq_one_of_isElementaryAbelian _ C.z.property⟩
  · apply mem_centralizer_singleton_iff.mpr
    exact congrArg (fun w : V => (w : G)) (mul_comm C.z C.v)
  · intro r hr
    exact mem_centralizer_singleton_iff.mp (hMC ((structural G T L h).1 hr.1))

/-- The final source omega-center containment rules out this fusion configuration. -/
theorem false_of_omega_le
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (homega : omegaCenterIn C.pointSylow ≤ V) : False := by
  exact C.outside (normalizer_le_of_fixed_line_in_omega h D structural hnone
    C.z.property C.z_ne C.z_fixed C.fixed_line C.pointSylow
    (C.fixed_mem_pointSylow_omega h D structural) homega C.normalizes)

end AlternatingEightFusion
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
