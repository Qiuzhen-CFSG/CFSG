module
public import CFSG.Quasithin.ChapterF.Section09.CriticalEndpointTranslations
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.RankEightReversePoint

/-!
# Aligning both ends of the rank-eight critical pair

Left multiplication by the source factor exchanger aligns the endpoint actor
and central point. Right multiplication by its inverse independently aligns
the reverse point and fixes the conjugates of U and Z. The common-edge action
preserves the normalized critical-endpoint conditions; the actual two-core
identity transports the strict denominator.

Source: Aschbacher--Smith 14.6.13(2), printed p.1032.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open OddNormalizer Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- Independently orient the two factor labels without changing the critical
endpoint conditions or the strict literal denominator. -/
theorem align_critical_first_support
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH] (a : LocalQuotientAction D.H D.UH D.V₁)
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (D.T : Subgroup G) p H0 H1 H2)
    (i : h.CriticalEndpoint) (hb : 3 ≤ h.b)
    (hstrict : commutatorPreimage (i.conjugate D.UH) D.UH D.V₁ < i.conjugate D.UH)
    (hcase : (actorImage D.H (i.conjugate D.UH) ≤ actorImage D.H H1 ∧
        i.conjugate D.V₁ ≤ firstSupport a H1) ∨
      (actorImage D.H (i.conjugate D.UH) ≤ actorImage D.H H2 ∧
        i.conjugate D.V₁ ≤ firstSupport a H2))
    (hrev : D.V₁ ≤ i.conjugate (firstSupport a H1) ∨
      D.V₁ ≤ i.conjugate (firstSupport a H2)) :
    ∃ j : h.CriticalEndpoint,
      commutatorPreimage (j.conjugate D.UH) D.UH D.V₁ < j.conjugate D.UH ∧
      actorImage D.H (j.conjugate D.UH) ≤ actorImage D.H H1 ∧
      j.conjugate D.V₁ ≤ firstSupport a H1 ∧
      D.V₁ ≤ j.conjugate (firstSupport a H1) := by
  have hBH (k : h.CriticalEndpoint) : k.conjugate D.UH ≤ D.H :=
    (map_mono (conjugateSpanBy_mono h.plus_le le_rfl)).trans (k.large_le hb)
  have hZ (x : D.H) : D.V₁.map (MulAut.conj (x:G)).toMonoidHom = D.V₁ :=
    mem_normalizer_iff_map_conj_eq.mp
      ((h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) x.property)
  have hleft : ∃ j : h.CriticalEndpoint,
      commutatorPreimage (j.conjugate D.UH) D.UH D.V₁ < j.conjugate D.UH ∧
      actorImage D.H (j.conjugate D.UH) ≤ actorImage D.H H1 ∧
      j.conjugate D.V₁ ≤ firstSupport a H1 ∧
      (D.V₁ ≤ j.conjugate (firstSupport a H1) ∨
        D.V₁ ≤ j.conjugate (firstSupport a H2)) := by
    rcases hcase with ⟨ha,hp⟩ | ⟨ha,hp⟩
    · exact ⟨i,hstrict,ha,hp,hrev⟩
    · obtain ⟨x,hx,_,hex⟩ := d.exchanged
      let xH : D.H := ⟨x,h.T_le_H hx⟩
      let j := i.mulLeft ⟨x,hx⟩
      have hj (K : Subgroup G) : j.conjugate K =
          (i.conjugate K).map (MulAut.conj x).toMonoidHom := conjBy_mul K x i.representative
      have hH : D.H.map (MulAut.conj x).toMonoidHom = D.H :=
        mem_normalizer_iff_map_conj_eq.mp (D.H.le_normalizer xH.property)
      have hQ : D.QH.map (MulAut.conj x).toMonoidHom = D.QH := by
        change (D.H.pCoreIn 2).map _ = _
        rw [← AmalgamLocalCores.pCoreIn_map_of_injective
          2 (MulAut.conj x).toMonoidHom (MulAut.conj x).injective D.H,hH]
        rfl
      have hs := (map_lt_map_iff_of_injective
        (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective).mpr hstrict
      rw [critical_denominator_eq h _ (hBH i),
        map_inf _ _ _ (MulAut.conj x).injective,hQ,← hj D.UH,
        ← critical_denominator_eq h _ (hBH j)] at hs
      have ha' := exchange_factor_actor_transport a p d h.T_le_H x hx hex _ ha
      have he := actorImage_conjugate (i.conjugate D.UH) (hBH i) xH
      change actorImage D.H ((i.conjugate D.UH).map (MulAut.conj x).toMonoidHom) = _ at he
      rw [← hj D.UH] at he
      have hp' := exchange_factor_support_transport a p d h.T_le_H x hx hex _ hp
      rw [← hj D.V₁] at hp'
      refine ⟨j,hs,he.symm ▸ ha',hp',?_⟩
      have back (K : Subgroup G) (hk : D.V₁ ≤ i.conjugate K) : D.V₁ ≤ j.conjugate K := by
        have hm := map_mono (f := (MulAut.conj x).toMonoidHom) hk
        rw [hZ xH,← hj K] at hm
        exact hm
      exact hrev.imp (back _) (back _)
  obtain ⟨j,hs,ha,hp,hr | hr⟩ := hleft
  · exact ⟨j,hs,ha,hp,hr⟩
  · obtain ⟨x,hx,_,hex⟩ := d.exchanged
    let y : D.H := ⟨x⁻¹,D.H.inv_mem (h.T_le_H hx)⟩
    let k := j.mulRight y
    have hk (K : Subgroup G) : k.conjugate K =
        j.conjugate (K.map (MulAut.conj x⁻¹).toMonoidHom) := conjBy_mul K j.representative x⁻¹
    have hU : D.UH.map (MulAut.conj x⁻¹).toMonoidHom = D.UH :=
      mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_conjugateSpanBy _ _) y.property)
    have hKU : k.conjugate D.UH = j.conjugate D.UH := by rw [hk,hU]
    have hKZ : k.conjugate D.V₁ = j.conjugate D.V₁ := by rw [hk,hZ y]
    have hS : (firstSupport a H1).map (MulAut.conj x⁻¹).toMonoidHom = firstSupport a H2 := by
      unfold firstSupport
      rw [supportPreimage_conjugate a _ y,moved_map_conjugate]
      rw [← actorImage_conjugate H1 (d.first_le.trans d.zero_le) y,hex]
    refine ⟨k,?_,?_,?_,?_⟩
    · simpa only [hKU] using hs
    · simpa only [hKU] using ha
    · simpa only [hKZ] using hp
    · rwa [hk,hS]

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
