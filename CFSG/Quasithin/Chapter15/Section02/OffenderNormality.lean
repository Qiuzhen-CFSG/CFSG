module

public import CFSG.Quasithin.Chapter15.Section02.InvolutionLayers
public import Theory.GroupTheory.QuadraticCommutatorNormality

/-!
# Normality of the literal Case-II offender commutator

For the original offender `A`, write `B = A ∩ Q` and `ZS = [V,B]`.
The quadratic action on the normal closure of `V` makes `A` centralize
`ZS`. The subgroup `X` centralizes `V`, hence `ZS`; together with the
normalization by `T`, the source generation `H = ⟨X,A,T⟩` proves normality.
The application theorem uses that normality in the actual local-to-ambient
15.2.28 bound, with the unchanged inclusion of `H` in `G`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the proof
of Lemma 15.2.11 on p.1111 and Lemma 15.2.28 on p.1119. The marked
offender selection, generation and normalization by `T` remain earlier
source inputs; this module does not establish their existence.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section02

variable {G : Type*} [Group G]

/-- Apply the original offender normality proof to the 15.2.28 consumer. -/
theorem source_offender_normalClosure_involution_bound
    (H : Subgroup G) (V Q T S X A : Subgroup H) [Q.Normal]
    (hBV : A ⊓ Q ≤ normalizer (V : Set H))
    (hquadratic : ⁅⁅normalClosure (V : Set H), A⁆, A⁆ = ⊥)
    (hXV : X ≤ centralizer (V : Set H))
    (hTZ : T ≤ normalizer (⁅V, A ⊓ Q⁆ : Subgroup H))
    (hgen : (X ⊔ A) ⊔ T = ⊤)
    (hQT : Q ≤ T) (hTS : ∀ x ∈ T, x ^ 2 = 1 → x ∈ S)
    (hcomm : ⁅V, S⁆ ≤ ⁅V, A ⊓ Q⁆) :
    ⁅(normalClosure (V : Set H)).map H.subtype,
      involutionGenerated (Q.map H.subtype)⁆ ≤
      (⁅V, A ⊓ Q⁆).map H.subtype := by
  let : (⁅V, A ⊓ Q⁆).Normal :=
    commutator_normal_of_quadratic_generation V Q X A T hBV hquadratic hXV hTZ hgen
  exact source_local_normalClosure_involution_bound H V Q T S ⁅V, A ⊓ Q⁆
    hQT hTS hcomm

end CFSG.Quasithin.Chapter15.Section02
