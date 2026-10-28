module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData.Indices
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Endpoint

/-!
# Denominator exchange and placement in the original edge core

Reuse the genuine graph reversal constructed in `ReversedSourceData.Geometry`.
F.9.15 and strictness select the new critical neighbor. Both denominators
exchange by the same actual G₀ transporter; the terminal H-adjustment fixes
the H-invariant seeds. This supplies the opposite orientation in 13.8.7.

For the last clause of 13.8.8(2), incidence constructs an element of H
carrying γ₂ to γ₀. Conjugation transports the complete edge stabilizer and
its intrinsic two-core, hence the F.9.13(2) containment of Vγ.

The earlier explicit inputs are F.9.11's length bound, F.9.13's containments,
F.9.15's first-kernel identity, normalization of V₁, the standard edge
identity F.9.13(1), and O₂(L₁T)≤R₁ from the standing flag setup.
No symmetry, rank choice or endpoint-placement conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.8.7–8, printed pp.948–949, and F.9.13–17, printed pp.322–324.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
open ReversedSourceData
variable {G : Type*} [Group G] {L T H V : Subgroup G}

/-- Strictness detects a neighbor without any assumed reversal or rank comparison. -/
theorem exists_reversal_of_strict (c : CriticalPair L T H V) (V₃ Z : Subgroup G)
    (hb : 3 ≤ c.path.length) (hV₃ : V₃ ≤ V)
    (hVH : c.Vgamma ≤ H) (hZ : H ≤ normalizer (Z : Set G))
    (hF915 : c.Vgamma ⊓ firstKernel L T H (base L T H true) =
      Source.Egamma c.Vgamma (Source.UH H V₃) Z)
    (hstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z < c.Ugamma V₃) :
    Nonempty (Reversal c) := by
  apply exists_reversal c hb
  intro hk
  have hUV : c.Ugamma V₃ ≤ c.Vgamma := map_mono (conjugateSpanBy_mono hV₃ le_rfl)
  have he : c.Ugamma V₃ ≤ Source.Egamma c.Vgamma (Source.UH H V₃) Z :=
    (le_inf hUV (hUV.trans hk)).trans hF915.le
  apply hstrict.not_ge
  apply le_commutatorPreimage le_rfl
  exact (commutator_mono he le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (hVH.trans hZ))

/-- The actual inverse transporter of the newly selected first edge. -/
def transporter {c : CriticalPair L T H V} (r : Reversal c) : G0 L T H :=
  (c.gb * inG0 r.adjustment)⁻¹

theorem endpoint_map {c : CriticalPair L T H V} (r : Reversal c)
    (X : Subgroup G) (hX : H ≤ normalizer (X : Set G)) :
    X.map (MulAut.conj (r.pair.gb : G)).toMonoidHom =
      X.map (MulAut.conj (transporter r : G)).toMonoidHom := by
  rw [r.gb_eq]
  change X.conjBy ((transporter r : G) * (r.terminalAdjustment : G)) = _
  rw [conjBy_mul, show X.conjBy (r.terminalAdjustment : G) = X from
    mem_normalizer_iff_map_conj_eq.mp (hX r.terminalAdjustment.property)]
  rfl

theorem return_map {c : CriticalPair L T H V} (r : Reversal c)
    (X : Subgroup G) (hX : H ≤ normalizer (X : Set G)) :
    (X.map (MulAut.conj (c.gb : G)).toMonoidHom).map
      (MulAut.conj (transporter r : G)).toMonoidHom = X := by
  simp only [transporter, Subgroup.coe_inv, Subgroup.coe_mul, mul_inv_rev]
  change (X.conjBy (c.gb : G)).conjBy
    (((r.adjustment : G)⁻¹) * (c.gb : G)⁻¹) = X
  rw [conjBy_mul, conjBy_inv]
  exact mem_normalizer_iff_map_conj_eq.mp (hX (H.inv_mem r.adjustment.property))

/-- Both literal commutator-preimage denominators exchange under the same
actual graph transporter. The terminal factor fixes the H-invariant seeds. -/
theorem denominators {c : CriticalPair L T H V} (r : Reversal c)
    (V₃ Z : Subgroup G) (hZ : H ≤ normalizer (Z : Set G))
    (hγH : c.Ugamma V₃ ≤ H)
    (hUA : Source.UH H V₃ ≤ normalizer (c.Aone Z : Set G)) :
    Source.DH (Source.UH H V₃) (r.pair.Ugamma V₃) (r.pair.Aone Z) =
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z).map
        (MulAut.conj (transporter r : G)).toMonoidHom ∧
    Source.Dgamma (r.pair.Ugamma V₃) (Source.UH H V₃) Z =
      (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z)).map
        (MulAut.conj (transporter r : G)).toMonoidHom := by
  have hU := le_normalizer_conjugateSpanBy V₃ H
  have hUret := return_map r (Source.UH H V₃) hU
  have hZret := return_map r Z hZ
  have hUend := endpoint_map r (Source.UH H V₃) hU
  have hZend := endpoint_map r Z hZ
  change (c.Ugamma V₃).map _ = Source.UH H V₃ at hUret
  change (c.Aone Z).map _ = Z at hZret
  change r.pair.Ugamma V₃ = _ at hUend
  change r.pair.Aone Z = _ at hZend
  constructor
  · rw [Source.Dgamma, map_commutatorPreimage_equiv _ _ _ _ (hγH.trans hZ),
      hUret, ← hUend, ← hZend]
    rfl
  · rw [Source.DH, map_commutatorPreimage_equiv _ _ _ _ hUA,
      hUret, hZret, ← hUend]
    rfl

/-- The constructed pair reverses the asymmetric orientation. -/
theorem reverse_asymmetry {c : CriticalPair L T H V} (r : Reversal c)
    (V₃ Z : Subgroup G) (hZ : H ≤ normalizer (Z : Set G))
    (hγH : c.Ugamma V₃ ≤ H)
    (hUA : Source.UH H V₃ ≤ normalizer (c.Aone Z : Set G))
    (hfull : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z) = Source.UH H V₃)
    (hstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z < c.Ugamma V₃) :
    Source.DH (Source.UH H V₃) (r.pair.Ugamma V₃) (r.pair.Aone Z) < Source.UH H V₃ ∧
    Source.Dgamma (r.pair.Ugamma V₃) (Source.UH H V₃) Z = r.pair.Ugamma V₃ := by
  obtain ⟨hD, hDγ⟩ := denominators r V₃ Z hZ hγH hUA
  constructor
  · rw [hD]
    have hs := (map_lt_map_iff_of_injective
      (f := (MulAut.conj (transporter r : G)).toMonoidHom)
      (MulAut.conj (transporter r : G)).injective).mpr hstrict
    exact hs.trans_eq (return_map r (Source.UH H V₃) (le_normalizer_conjugateSpanBy V₃ H))
  · rw [hDγ, hfull]
    exact (endpoint_map r (Source.UH H V₃) (le_normalizer_conjugateSpanBy V₃ H)).symm

/-- F.9.13(1),(2) put the conjugated endpoint inside the original edge core.
The element in H is constructed from incidence with the second path vertex. -/
theorem exists_second_to_base [Finite G] (c : CriticalPair L T H V)
    (L₁ R₁ : Subgroup G) (hb : 2 ≤ c.path.length)
    (he : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hV : c.Vgamma ≤ (edgeGroup L T H (base L T H true) c.second).pCoreIn 2)
    (hR : (L₁ ⊔ T).pCoreIn 2 ≤ R₁) :
    ∃ h : H, inG0 (L := L) (T := T) h • c.second = base L T H false ∧
      c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2 ∧
      c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ R₁ := by
  have ha : (graph L T H).Adj (base L T H true) c.second := by
    have hh := c.path.adj_getVert_succ (i := 1) (by omega)
    rwa [c.first] at hh
  obtain ⟨t, ht⟩ := exists_neighbor_transporter ha
  have hh : inG0 (L := L) (T := T) t⁻¹ • c.second = base L T H false := by
    rw [← ht]
    exact inv_smul_smul (inG0 t) _
  have hedge : (edgeGroup L T H (base L T H true) c.second).map
      (MulAut.conj ((t⁻¹ : H) : G)).toMonoidHom = L₁ ⊔ T := by
    change (edgeGroup L T H (base L T H true) c.second).map
      (MulAut.conj (inG0 (L := L) (T := T) t⁻¹ : G)).toMonoidHom = _
    rw [edgeGroup, map_inf _ _ _ (MulAut.conj _).injective,
      ← vertexGroup_smul L T H (inG0 t⁻¹),
      ← vertexGroup_smul L T H (inG0 t⁻¹), inG0_one, hh,
      vertexGroup_base, vertexGroup_base]
    simpa only [Bool.false_eq_true, ↓reduceIte, inf_comm] using he
  have hcore : ((edgeGroup L T H (base L T H true) c.second).pCoreIn 2).map
      (MulAut.conj ((t⁻¹ : H) : G)).toMonoidHom = (L₁ ⊔ T).pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup _
      (IsPGroup.ker_isPGroup_of_injective (MulAut.conj _).injective), hedge]
  have hv := map_mono (f := (MulAut.conj ((t⁻¹ : H) : G)).toMonoidHom) hV
  rw [hcore] at hv
  exact ⟨t⁻¹, hh, hv, hv.trans hR⟩

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation
end
