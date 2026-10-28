module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversalIndices
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.Lifting

/-!
# Index exchange after normalizing the reversed edge

The terminal H-factor fixes every H-invariant subgroup. The initial H-factor
conjugates the inverse endpoint pair inside H, preserving its star-image
rank and denominator index. Thus the actual normalized conjugator has the
same exchanged rank and codimension as the inverse conjugator, and equality
makes the reversed numerical choice eligible. The line-containment identity
retains both adjustments and assumes neither noncontainment.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Remark F.9.17,
printed p.324, and its use in 13.8.25, printed p.962.
-/

public section

open Subgroup
open Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G : Type*} [Group G]

theorem conjugate_mul (Q : Subgroup G) (a b : G) :
    Q.map (MulAut.conj (a * b)).toMonoidHom =
      (Q.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- The two stabilizer factors in the reversed edge have different roles. -/
theorem adjusted_conjugate (H Q : Subgroup G) (g : G) (h t : H)
    (hn : H ≤ normalizer (Q : Set G)) :
    Q.map (MulAut.conj ((h : G)⁻¹ * g⁻¹ * t)).toMonoidHom =
      (Q.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj (h : G)⁻¹).toMonoidHom := by
  have ht : Q.map (MulAut.conj (t : G)).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (hn t.property)
  rw [conjugate_mul, ht, conjugate_mul]

/-- Adjusting the reversed edge does not change its line-containment test. -/
theorem adjusted_line_containment (H UH Z : Subgroup G) (g : G) (h t : H)
    (hU : H ≤ normalizer (UH : Set G)) (hZ : H ≤ normalizer (Z : Set G)) :
    Z ≤ UH.map (MulAut.conj ((h : G)⁻¹ * g⁻¹ * t)).toMonoidHom ↔
      Z.map (MulAut.conj g).toMonoidHom ≤ UH := by
  rw [adjusted_conjugate H UH g h t hU]
  have hZh : Z.map (MulAut.conj (h : G)).toMonoidHom = Z :=
    mem_normalizer_iff_map_conj_eq.mp (hZ h.property)
  rw [← reversed_line_containment, hZh]
  exact (reversed_line_containment UH Z g).symm

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- The stabilizer adjustment preserves the exchanged rank and codimension. -/
theorem adjusted_rank_and_codimension (s : ConjugationSection H UH Z ρ)
    (g : G) (h t : H)
    (hforward : UH.map (MulAut.conj g).toMonoidHom ≤ H)
    (hreverse : UH ≤ H.map (MulAut.conj g).toMonoidHom)
    (hfaith : Function.Injective ρ) :
    let r := (h : G)⁻¹ * g⁻¹ * t
    rank (Source.starImage H (UH.map (MulAut.conj r).toMonoidHom)) =
      Module.finrank (ZMod 2) (U ⧸ s.image (Source.DH UH
        (UH.map (MulAut.conj g).toMonoidHom) (Z.map (MulAut.conj g).toMonoidHom))) ∧
    Module.finrank (ZMod 2) (U ⧸ s.image (Source.DH UH
      (UH.map (MulAut.conj r).toMonoidHom) (Z.map (MulAut.conj r).toMonoidHom))) =
      rank (Source.starImage H (UH.map (MulAut.conj g).toMonoidHom)) := by
  dsimp only
  have hZ := s.centralizes.trans (centralizer_le_normalizer _)
  have hUeq : UH.map (MulAut.conj (h : G)⁻¹).toMonoidHom = UH :=
    mem_normalizer_iff_map_conj_eq.mp (s.normalizes (H.inv_mem h.property))
  have hIH := reversed_actor_le H UH g hreverse
  have hRH : (UH.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj (h : G)⁻¹).toMonoidHom ≤ H := by
    have hh := map_mono (f := (MulAut.conj (h : G)⁻¹).toMonoidHom) hIH
    have hHeq : H.map (MulAut.conj (h : G)⁻¹).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer (H.inv_mem h.property))
    rwa [hHeq] at hh
  have hback : UH ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hforward
    rwa [conjugate_inverse_cancel] at hh
  have hn : UH ≤ normalizer ((Z.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) :=
    hback.trans ((s.centralizes_conjugate_line g⁻¹).trans (centralizer_le_normalizer _))
  have hd := map_commutatorPreimage_equiv (MulAut.conj (h : G)⁻¹) UH
    (UH.map (MulAut.conj g⁻¹).toMonoidHom) (Z.map (MulAut.conj g⁻¹).toMonoidHom) hn
  rw [hUeq] at hd
  have hindex :
      (Source.DH UH
        ((UH.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj (h : G)⁻¹).toMonoidHom)
        ((Z.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj (h : G)⁻¹).toMonoidHom)).relIndex UH =
      (Source.DH UH (UH.map (MulAut.conj g⁻¹).toMonoidHom)
        (Z.map (MulAut.conj g⁻¹).toMonoidHom)).relIndex UH := by
    change (commutatorPreimage _ _ _).relIndex _ = _
    rw [← hd]
    conv_lhs => arg 2; rw [← hUeq]
    exact relIndex_map_map_of_injective _ _ (MulAut.conj (h : G)⁻¹).injective
  obtain ⟨hr, hc⟩ := reversed_rank_and_codimension s g hforward hreverse hfaith
  rw [adjusted_conjugate H UH g h t s.normalizes,
    adjusted_conjugate H Z g h t hZ]
  constructor
  · change rank (Source.starImage H ((UH.map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj ((h⁻¹ : H) : G)).toMonoidHom)) = _
    rw [MarkedGeometry.starImage_conjugate _ hIH h⁻¹, rank,
      card_map_of_injective (MulAut.conj _).injective]
    exact hr
  · rw [s.quotient_finrank _ (s.line_le_DH _ _ hRH), hindex,
      ← s.quotient_finrank _ (s.line_le_DH _ _ hIH)]
    exact hc

theorem adjusted_equality_numerical_choice (s : ConjugationSection H UH Z ρ)
    (g : G) (h t : H)
    (hforward : UH.map (MulAut.conj g).toMonoidHom ≤ H)
    (hreverse : UH ≤ H.map (MulAut.conj g).toMonoidHom)
    (hfaith : Function.Injective ρ)
    (hrank : 1 < rank (Source.starImage H (UH.map (MulAut.conj g).toMonoidHom)))
    (hequal : Module.finrank (ZMod 2) (U ⧸ s.image (Source.DH UH
      (UH.map (MulAut.conj g).toMonoidHom) (Z.map (MulAut.conj g).toMonoidHom))) =
      rank (Source.starImage H (UH.map (MulAut.conj g).toMonoidHom))) :
    let r := (h : G)⁻¹ * g⁻¹ * t
    1 < rank (Source.starImage H (UH.map (MulAut.conj r).toMonoidHom)) ∧
    Module.finrank (ZMod 2) (U ⧸ s.image (Source.DH UH
      (UH.map (MulAut.conj r).toMonoidHom) (Z.map (MulAut.conj r).toMonoidHom))) =
      rank (Source.starImage H (UH.map (MulAut.conj r).toMonoidHom)) := by
  obtain ⟨hr, hc⟩ := adjusted_rank_and_codimension s g h t hforward hreverse hfaith
  dsimp only at hr hc ⊢
  rw [hr, hequal]
  exact ⟨hrank, hc⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
