module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.FusedNine.ElementaryNine
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.FusedNine.ComplementFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.FusedNine.IntersectionData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.FusedNine.IntersectionExistence
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.FusedNine.IntersectionFixedPoints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.InvolutionFusion

/-!
# A fused elementary nine from the involution normalizers

The A₆ complement constructs an elementary nine in N(E) containing c.
There are at most two N(E)-classes of elements of order three. An intersection
actor acting without nonidentity fixed points on E cannot be N(E)-conjugate
to c, which centralizes the marked involution in E. The S₅ complement of F
gives a commuting involution for that actor, and ambient involution fusion
therefore fuses it with c. Both N(E)-classes, and hence the elementary nine,
are fused in G.

The intersection construction supplies an element of order three in
N(E) ∩ N(F), and the fixed-point theorem proves that its action on E
fixes only the identity. These discharge the actor premise in the final
assembly from the involution-normalizer data. No ambient Sylow-three
statement, ambient order or recognition is used.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 3, printed pp.7–8, Lemma 8.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The geometric intersection actor fuses both three-classes of N(E). -/
public theorem normalizer_E_three_fusion_of_intersection_actor
    (h2 : InvolutionNormalizerData D k) (w : FusedNineIntersectionActor D k)
    (x : G) (hxN : x ∈ normalizer (CaseII.E D k : Set G)) (hx : orderOf x = 3) :
    IsConj x (CaseII.into D k CaseII.c) := by
  let N := normalizer (CaseII.E D k : Set G)
  let cG := CaseII.into D k CaseII.c
  let cN : N := ⟨cG, CaseII.centralizer_le_normalizer_E D k (k CaseII.c).property⟩
  let wN : N := ⟨w.actor, w.normalizes_E⟩
  let xN : N := ⟨x, hxN⟩
  have hcN : orderOf cN = 3 := by
    rw [← orderOf_coe cN]
    exact (orderOf_injective (CaseII.into D k) (CaseII.into_injective D k) CaseII.c).trans
      CaseII.actor_orders.2.2.1
  have hwN : orderOf wN = 3 := by
    rw [← orderOf_coe wN]
    exact w.actor_order
  have hxN3 : orderOf xN = 3 := by
    rw [← orderOf_coe xN]
    exact hx
  have hcw : ¬IsConj cN wN := by
    intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    have hgc : (MulAut.conj (g : G)) cG = w.actor := by
      exact congrArg Subtype.val hg
    have hzE : D.z ∈ CaseII.E D k := (CaseII.eNormalizerPoint D k).property
    have hgE : (CaseII.E D k).map (MulAut.conj (g : G)).toMonoidHom =
        CaseII.E D k := mem_normalizer_iff_map_conj_eq.mp g.property
    have htE : (MulAut.conj (g : G)) D.z ∈ CaseII.E D k := by
      rw [← hgE]
      exact mem_map_of_mem _ hzE
    have hc : Commute cG D.z := mem_centralizer_singleton_iff.mp (k CaseII.c).property
    have ht := hc.map (MulAut.conj (g : G)).toMonoidHom
    change Commute ((MulAut.conj (g : G)) cG) ((MulAut.conj (g : G)) D.z) at ht
    rw [hgc] at ht
    have h1 := w.fixed_point_free _ htE ht
    exact D.z_ne_one ((MulAut.conj (g : G)).injective (h1.trans (map_one _).symm))
  obtain ⟨t, ht, hwt⟩ := three_in_normalizer_F_commutes_involution D k h2.normalizer_F
    w.actor w.normalizes_F w.actor_order
  have hwc : IsConj w.actor cG := CaseII.three_fusion_of_commuting_involution D k
    h2.involution_fusion w.actor w.actor_order t ht hwt
  rcases normalizer_E_three_trichotomy D k h2.normalizer_E xN cN wN hxN3 hcN hwN
    with h | h | h
  · exact N.subtype.map_isConj h
  · exact (N.subtype.map_isConj h).trans hwc
  · exact (hcw h).elim

/-- A fully fused elementary nine, conditional on the source intersection actor. -/
public theorem exists_fused_elementary_nine_of_intersection_actor
    (h2 : InvolutionNormalizerData D k) (w : FusedNineIntersectionActor D k) :
    ∃ P : Subgroup G, P ≤ normalizer (CaseII.E D k : Set G) ∧
      IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧ CaseII.into D k CaseII.c ∈ P ∧
      ∀ x ∈ P, orderOf x = 3 → IsConj x (CaseII.into D k CaseII.c) := by
  obtain ⟨P, hPN, hPe, hPc, hcP⟩ := exists_elementary_nine_in_normalizer_E D k h2.normalizer_E
  exact ⟨P, hPN, hPe, hPc, hcP, fun x hx hx3 =>
    normalizer_E_three_fusion_of_intersection_actor D k h2 w x (hPN hx) hx3⟩

/-- The involution normalizers supply an elementary nine in N(E) containing c,
all of whose elements of order three are conjugate to c in G. -/
public theorem exists_fused_elementary_nine_of_involution_normalizers
    (h2 : InvolutionNormalizerData D k) :
    ∃ P : Subgroup G, P ≤ normalizer (CaseII.E D k : Set G) ∧
      IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧ CaseII.into D k CaseII.c ∈ P ∧
      ∀ x ∈ P, orderOf x = 3 → IsConj x (CaseII.into D k CaseII.c) := by
  obtain ⟨x, hxE, hxF, hx⟩ := exists_three_in_normalizer_intersection D k h2
  exact exists_fused_elementary_nine_of_intersection_actor D k h2
    { actor := x
      normalizes_E := hxE
      normalizes_F := hxF
      actor_order := hx
      fixed_point_free := intersection_three_fixed_point_free D k h2 x hxE hxF hx }

end Theory.GroupTheory.HeldM22A10.M22Identification
