module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Assembly
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.Inputs

/-!
# The actual embedding alternatives for the contrary overgroup

After replacing the overgroup by KU, the embedding reduction supplies either
the binary component with its full automorphism quotient, or a specified
component and its conjugate. This module expresses those same alternatives
inside H for the ordinary-component argument. The binary case retains its
actual field and transports automorphisms across the given projective model.
The pair case retains the actual conjugator and transports the seed and its
two-core quotient along the subgroup inclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.4.20, printed p.1164.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary

open Chapter1 EmbeddingReduction ComponentElimination.OrdinaryReduction

variable {G : Type*} [Group G] {H K U P : Subgroup G}

private theorem binaryAutomorphismModel_of_case
    (hgen : H = K ⊔ U) (h : BinaryCase H U K) : BinaryAutomorphismModel H := by
  obtain ⟨_, _, _, _, hm, ⟨e⟩⟩ := h
  have eH : Nonempty ((H ⧸ pCore 2 H) ≃* MulAut (XiQuotient K)) := by
    rw [hgen]
    exact ⟨e⟩
  obtain ⟨f⟩ := eH
  rcases hm with hm | hm
  · obtain ⟨F, hF, hfin, hcard, ⟨g⟩⟩ := hm
    exact ⟨4, Or.inl rfl, F, hF, hfin, hcard, ⟨f.trans (MulAut.congr g)⟩⟩
  · obtain ⟨F, hF, hfin, hcard, ⟨g⟩⟩ := hm
    exact ⟨5, Or.inr rfl, F, hF, hfin, hcard, ⟨f.trans (MulAut.congr g)⟩⟩

private theorem map_intrinsic_conjugate {L : Subgroup G} (hLH : L ≤ H) (t : H) :
    ((L.subgroupOf H).map (MulAut.conj t).toMonoidHom).map H.subtype =
      L.conjBy (t : G) := by
  have hc : H.subtype.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj (t : G)).toMonoidHom.comp H.subtype := rfl
  rw [map_map, hc, ← map_map, map_subgroupOf_eq_of_le hLH]
  rfl

private theorem pairEmbedding_of_case
    (hgen : H = K ⊔ U) (h : ExchangedCase H U P K) :
    Nonempty (PairEmbedding H K U) := by
  obtain ⟨L, t, hL, _, _, hm, ht, hmove, _, hK, _, _, _, _, _⟩ := h
  have hKH : K ≤ H := le_sup_left.trans hgen.ge
  have hUH : U ≤ H := le_sup_right.trans hgen.ge
  let r : H := ⟨t, hUH ht.1⟩
  let e : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃* XiQuotient L :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hL.1) (pCore_map_iso 2 _)
  refine ⟨{
    seed := L.subgroupOf H
    cComponent := hL.2
    conjugator := r
    conjugator_mem := ht.1
    moves := ?_
    product := ?_
    model := ?_ }⟩
  · rw [← subgroupOf_normalizer_eq hL.1]
    exact hmove
  · apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hL.1, map_intrinsic_conjugate hL.1,
      map_subgroupOf_eq_of_le hKH]
    exact hK.symm
  · rcases hm with ⟨n, hn, _, hmodel⟩ | ⟨q, hq, hodd, hmodel⟩
    · exact Or.inl ⟨n, hn, hmodel.of_mulEquiv e⟩
    · exact Or.inr ⟨q, hq, hodd, hmodel.of_mulEquiv e⟩

/-- The actual embedding reduction supplies the ordinary-component input
on the same generated overgroup, with no additional classification premise. -/
theorem embeddingAlternatives_of_cases (hgen : H = K ⊔ U)
    (h : BinaryCase H U K ∨ ExchangedCase H U P K) :
    EmbeddingAlternatives H K U := by
  rcases h with hb | hp
  · exact Or.inl ⟨hb.1.2, binaryAutomorphismModel_of_case hgen hb⟩
  · exact Or.inr (pairEmbedding_of_case hgen hp)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary
