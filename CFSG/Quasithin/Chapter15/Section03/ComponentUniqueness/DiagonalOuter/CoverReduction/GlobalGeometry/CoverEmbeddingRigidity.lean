module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.ModelWitnesses
public import Theory.GroupTheory.PerfectCentralCoverEmbeddingRigidity
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.Mathieu.M23.Properties.Order

/-!
# Identifying nested covers after the equality-or-M₂₃ reduction

Let B ≤ K ≤ H be the source quasisimple subgroups, with B/O₂(B)
actually marked as PSL₃(4) and Z(B) = O₂(B) of order four. Restriction
of π : H → H/O₂(H) gives a perfect central cover K → π(K).
If π(B) = π(K), perfectness of K forces B = K without normality of B.

If π(K) is the concrete Mathieu group M₂₃, triviality of its universal
cover's kernel makes this cover an isomorphism. But |B| = 80640 does
not divide |M₂₃| = 10200960. This excludes the exceptional branch.

The exact I.1.3 assertion that the M₂₃ Schur multiplier is trivial remains
an explicit input, formulated using the constructed universal projection.
The equality-or-M₂₃ alternative is also explicit: its A.3.12 specialization
belongs to a separate task. Thus this module completes the conditional
rigidity argument, not the global geometry or source 15.3.38.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
I.1.1 and I.1.3 on printed p.407 (PDF p.418), and the proof of 15.3.38
on printed p.1136 (PDF p.1153).
-/

public section

open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
namespace CoverEmbeddingRigidity

variable {H : Type*} [Group H]

/-- The marked source cover has order four times the actual PSL₃(4) order. -/
theorem card_marked_cover (B : Subgroup H)
    (hc : center B = pCore 2 B) (hz : Nat.card (center B) = 4)
    (c : ProjectiveMarking B 4) : Nat.card B = 80640 := by
  have hq : Nat.card (B ⧸ pCore 2 B) = 20160 := by
    rw [Nat.card_congr c.equivalence.toEquiv, Matrix.PSL3.LinearThree.card_projective,
      c.card]
    norm_num
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B), hq, ← hc, hz]

variable [Finite H]

/-- Equality in H/O₂(H) identifies the nested covers. In particular, no
ambient or relative normality of the smaller subgroup is assumed. -/
theorem eq_of_equal_image {B K : Subgroup H} [IsQuasisimple K]
    (hBK : B ≤ K)
    (heq : B.map (QuotientGroup.mk' (pCore 2 H)) =
      K.map (QuotientGroup.mk' (pCore 2 H))) : B = K := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact eq_of_le_of_map_eq_of_central_kernel hBK _
    (pCoreQuotientCover 2 K).ker_le_center heq

/-- The genuine M₂₃ multiplier input excludes the exceptional quotient
image: its induced perfect central cover would identify K with M₂₃,
contradicting Lagrange for the marked subgroup B. -/
theorem not_m23_image {B K : Subgroup H} [IsQuasisimple K]
    (hBK : B ≤ K)
    (hc : center B = pCore 2 B) (hz : Nat.card (center B) = 4)
    (c : ProjectiveMarking B 4)
    (hm : (universalProjection Sporadic.Mathieu.M23).ker = ⊥) :
    ¬ Nonempty ((K.map (QuotientGroup.mk' (pCore 2 H))) ≃*
      Sporadic.Mathieu.M23) := by
  rintro ⟨e⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q := pCoreQuotientCover 2 K
  let f : Cover K Sporadic.Mathieu.M23 :=
    { toMonoidHom := e.toMonoidHom.comp q.toMonoidHom
      surjective := e.surjective.comp q.surjective
      isPerfect := q.isPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective q.toMonoidHom e.toMonoidHom e.injective]
        exact q.ker_le_center }
  let d : K ≃* Sporadic.Mathieu.M23 := MulEquiv.ofBijective f.toMonoidHom
    ⟨f.injective_of_universalProjection_ker_eq_bot hm, f.surjective⟩
  have hK : Nat.card K = 10200960 :=
    (Nat.card_congr d.toEquiv).trans Sporadic.Mathieu.m23_order
  have hd := card_dvd_of_le hBK
  rw [card_marked_cover B hc hz c, hK] at hd
  norm_num at hd

/-- The conditional rigidity step on printed p.1136. Both source inputs
are displayed: the quotient-image alternative and the actual trivial
M₂₃ multiplier. All central-cover and exclusion premises are proved above. -/
theorem eq_of_equal_image_or_m23 {B K : Subgroup H}
    [IsQuasisimple B] [IsQuasisimple K] [K.Normal]
    (hBK : B ≤ K)
    (hc : center B = pCore 2 B) (hz : Nat.card (center B) = 4)
    (c : ProjectiveMarking B 4)
    (hm : (universalProjection Sporadic.Mathieu.M23).ker = ⊥)
    (halt : B.map (QuotientGroup.mk' (pCore 2 H)) =
        K.map (QuotientGroup.mk' (pCore 2 H)) ∨
      Nonempty ((K.map (QuotientGroup.mk' (pCore 2 H))) ≃*
        Sporadic.Mathieu.M23)) : B = K := by
  rcases halt with heq | hm23
  · exact eq_of_equal_image hBK heq
  · exact (not_m23_image hBK hc hz c hm hm23).elim

end CoverEmbeddingRigidity
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry

end
