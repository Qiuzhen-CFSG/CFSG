module

public import Theory.Representation.NormalElementaryQuotient.BestOffender
public import Theory.Representation.BinaryOffender.Stability

/-!
# The full Thompson image in a centralizer quotient

Every nontrivial image of a maximum elementary abelian subgroup is a best
binary offender. Apply maximality to D C_V(D) for the inverse image D of
each subgroup of the image, then cancel the common action kernel. Thus the
entire Thompson image lies in the offender-generated subgroup.

This is the reusable version of the argument previously internal to
Chapter15's ActionRecognition/Thompson. Its terminal Chapter12 consumer
retains the original projection Y → Y/O₂(Y).
Source: Aschbacher--Smith, B.1.3 and B.2.4, pp.67 and 75--76.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

namespace Representation.NormalElementaryQuotient
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
  (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
  (q : G →* H) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (V : Set G))

/-- The full ordinary Thompson image lies in the best-offender-generated group. -/
theorem maxJ_image_le_offenderSubgroup (S : Subgroup G) (hVS : V ≤ S) :
    (Stellmacher.elementaryAbelianMaxJ S).map q ≤
      offenderSubgroup (representation V q hq hker) := by
  rw [map_le_iff_le_comap]
  apply sSup_le
  intro A hA
  rw [← map_le_iff_le_comap]
  by_cases hk : A.map q = ⊥
  · rw [hk]
    exact bot_le
  · exact le_iSup_of_le (A.map q)
      (le_iSup_of_le ⟨maxElementary_isBestOffender V q hq hker S A hVS hA hk,
        le_top⟩ le_rfl)
end Representation.NormalElementaryQuotient
