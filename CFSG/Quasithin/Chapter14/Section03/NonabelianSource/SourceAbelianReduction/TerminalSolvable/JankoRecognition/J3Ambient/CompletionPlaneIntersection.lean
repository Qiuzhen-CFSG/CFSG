module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.SourceSixteenCompletion
public import Theory.SpecificGroups.Janko3.SourceRecognition.PlaneCubicNormalizer

/-!
# The literal completion/plane-normalizer intersection

The original point subgroup has order 480 and lies in both the recognized
order-8160 completion and the full order-2880 plane normalizer. Their order
gcd is 480, so their entire intersection is that same original subgroup.
All complement, natural-action, and field-embedding markings are retained.

Source: Baumeister, A geometry for groups of J₃-type (2007), Lemma 2.11.
-/

public noncomputable section
open Subgroup
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen
open Janko23.J3Recognition.Ambient.Seventeen

set_option maxHeartbeats 800000 in
/-- The full first/second rank-three intersection is the original field subgroup. -/
theorem literal_completion_plane_intersection
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (ha : ∀ (c : C) (x : A),
      a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    completion j.range (overlap j) ⊓ normalizer (A : Set G) = j.range := by
  obtain ⟨e, _, _⟩ := PlaneTransport.affine_equiv_of_complement A C l a hC ha
  have hPlane : Nat.card Plane = 16 := by
    rw [← Nat.card_congr SingerField.rootCoordinates.toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, SingerField.field_card]
  have hLinear : Nat.card LinearGroup = 180 := by
    rw [Matrix.card_GL_field]
    norm_num [Representation.SL2FourNatural.card_field, Fin.prod_univ_succ]
  have hN : Nat.card (normalizer (A : Set G)) = 2880 := by
    rw [Nat.card_congr e.toEquiv, SemidirectProduct.card, hPlane, hLinear]
  obtain ⟨k, hk, _, hr⟩ := literal_sixteen_model_embedding P hc A C a j hj
  have hL : Nat.card (completion j.range (overlap j)) = 8160 := by
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hk).toEquiv]
    exact Theory.PSL2.BinaryFourFieldExtension.model_card
  symm
  apply eq_of_le_of_card_ge (le_inf le_sup_left hj.2.1)
  have hd := Nat.dvd_gcd
    (card_dvd_of_le (show completion j.range (overlap j) ⊓ normalizer (A : Set G) ≤
      completion j.range (overlap j) from inf_le_left))
    (card_dvd_of_le (show completion j.range (overlap j) ⊓ normalizer (A : Set G) ≤
      normalizer (A : Set G) from inf_le_right))
  rw [hL, hN] at hd
  norm_num at hd
  rw [hj.2.2.1]
  exact Nat.le_of_dvd (by decide) hd

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
