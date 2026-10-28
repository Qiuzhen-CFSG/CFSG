module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.PairIndex.Geometry
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.PairIndex.Swap.Standard

/-!
# Transporting the concrete Suzuki-pair interchange

Place the first component on the standard fixed B₂ Levi. Commutativity puts
the second component into its centralizer. A bound by the standard partner,
together with the two supplied Suzuki equivalences, gives equality by finite
cardinality. Conjugating the concrete Weyl interchange back then swaps the
original two factors, and transports properness of their join normalizer.

The assembly is conditional on component placement, the concrete centralizer
bound, and properness of the standard pair normalizer. No ambient simplicity,
relative normality, component exhaustiveness, or splitting is used.

Source: Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E; the Suzuki-wreath entry reproduced in the
proof of Theorem 5 of arXiv:0910.4758, pp.2–3.
-/

public section

namespace ReeF4.MaximalSubgroups.CommutingComponents

open Subgroup CarrierIdentification PairSwap

private theorem map_conj_mul {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_cancel {G : Type*} [Group G] (H : Subgroup G) (a : G) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom = H := by
  rw [← map_conj_mul]
  simp only [inv_mul_cancel, map_one]
  exact H.map_id

/-- Component placement and the two concrete geometry calculations suffice for
an interchange of the actual supplied factors in a proper ambient normalizer. -/
theorem identifiedPairSwap_of_leviConjugacy_of_standardGeometry
    (hplace : ComponentLeviConjugacy) (hcentral : StandardCentralizerBound)
    (hproper : StandardPairProper) : IdentifiedPairSwap := by
  intro m hm M hM hsolv hR L K hL hK hne hc eL eK
  obtain ⟨g, hg⟩ := hplace m hm M hM hsolv hR L K hL hK hne hc
  let f : M →* Model m := (MulAut.conj g).toMonoidHom.comp M.subtype
  have hLf : L.map f = standardSuzukiLevi m := by
    rw [← map_map]
    exact hg
  have hc' : ⁅K.map f, L.map f⁆ = ⊥ := by
    rw [← map_commutator, commutator_comm K L, hc, Subgroup.map_bot]
  rw [hLf] at hc'
  have hf : Function.Injective f := (MulAut.conj g).injective.comp M.subtype_injective
  let eS : standardSuzukiLevi m ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m :=
    ((equivMapOfInjective L f hf).trans (MulEquiv.subgroupCongr hLf)).symm.trans eL
  have hKle : K.map f ≤ standardPartner m :=
    (commutator_eq_bot_iff_le_centralizer.mp hc').trans (hcentral m hm eS)
  have hcard : Nat.card (standardPartner m) = Nat.card (K.map f) := by
    rw [standardPartner, card_map_of_injective (MulAut.conj (interchangeElement m)).injective,
      ← hLf, card_map_of_injective hf, card_map_of_injective hf]
    exact (Nat.card_congr eL.toEquiv).trans (Nat.card_congr eK.toEquiv).symm
  have hKf : K.map f = standardPartner m := eq_of_le_of_card_ge hKle hcard.le
  have hKg : (K.map M.subtype).map (MulAut.conj g).toMonoidHom = standardPartner m := by
    rwa [map_map]
  have hjoin : ((L ⊔ K).map M.subtype).map (MulAut.conj g).toMonoidHom =
      standardSuzukiLevi m ⊔ standardPartner m := by
    rw [Subgroup.map_sup, Subgroup.map_sup, hg, hKg]
  refine ⟨?_, g⁻¹ * interchangeElement m * g, ?_, ?_⟩
  · intro hn
    apply hproper m hm eS
    rw [← hjoin, ← map_equiv_normalizer_eq, hn]
    exact map_top_of_surjective _ (MulAut.conj g).surjective
  · rw [map_conj_mul, map_conj_mul, hg, (interchange_standard_pair m).1,
      ← hKg, map_conj_cancel]
  · rw [map_conj_mul, map_conj_mul, hKg, (interchange_standard_pair m).2,
      ← hg, map_conj_cancel]

end ReeF4.MaximalSubgroups.CommutingComponents
