module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.LocalData

/-!
# Conjugacy transport for the Tits centralizer calculation

The avoidance bound concerns elementary abelian subgroups normal in the
specified involution centralizer. Conjugating both subgroups preserves that
relative normality and the forbidden class of the literal five-inverter.
The commutator transport keeps its witness in the original five-kernel.

These are the transport steps for the finite calculations used in GM04,
Lemmas 2.3 and 8.8, internal pp.6 and 57. No centralizer bound is assumed
without an explicit argument, and this module does not construct such a bound.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
open Subgroup Tits

/-- The exact relative-normality bound, at one specified involution. -/
@[expose] def NormalElementaryBound (t : ParrottGroup) : Prop :=
  ∀ K : Subgroup ParrottGroup, K ≤ centralizer {t} →
    IsElementaryAbelian 2 K → (K.subgroupOf (centralizer {t})).Normal →
    (∀ k ∈ K, ¬ IsConj fiveInverter k) → Nat.card K ≤ 16

private theorem map_centralizer (e : ParrottGroup ≃* ParrottGroup) (t : ParrottGroup) :
    (centralizer {t}).map e.toMonoidHom = centralizer {e t} := by
  apply le_antisymm
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      map_centralizer_le_centralizer_image {t} e.toMonoidHom
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change e.symm y ∈ centralizer {t}
    rw [mem_centralizer_singleton_iff]
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      mem_centralizer_singleton_iff.mp hy

/-- Conjugacy transports relative normality in the actual centralizers. -/
theorem NormalElementaryBound.conjugate {a b : ParrottGroup}
    (ha : NormalElementaryBound a) (hab : IsConj a b) : NormalElementaryBound b := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  let e := MulAut.conj g⁻¹
  have he : e b = a := by
    rw [← hg]
    simp [e, mul_assoc]
  have hC : (centralizer {b}).map e.toMonoidHom = centralizer {a} := by
    rw [map_centralizer, he]
  intro K hK hE hN havoid
  let := hE
  let L := K.map e.toMonoidHom
  have hL : L ≤ centralizer {a} := by
    rw [← hC]
    exact map_mono hK
  have hLN : (L.subgroupOf (centralizer {a})).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hL).mpr
    rw [← hC]
    exact (map_mono ((normal_subgroupOf_iff_le_normalizer hK).mp hN)).trans
      (K.le_normalizer_map e.toMonoidHom)
  have hav : ∀ k ∈ L, ¬ IsConj fiveInverter k := by
    rintro _ ⟨k, hk, rfl⟩ hc
    apply havoid k hk
    apply hc.trans
    apply isConj_iff.mpr
    refine ⟨g, ?_⟩
    simp [e, mul_assoc]
  have hb := ha L hL (IsElementaryAbelian.map e.toMonoidHom) hLN hav
  simpa only [L, card_map_of_injective (f := e.toMonoidHom) e.injective] using hb

/-- A five-kernel commutator witness transports without moving that kernel. -/
theorem commutator_conjugate {a b : ParrottGroup} (hab : IsConj a b)
    (ha : ∃ x k : ParrottGroup, k ∈ fiveKernel ∧ k ≠ 1 ∧
      IsConj k (a * x * a⁻¹ * x⁻¹)) :
    ∃ x k : ParrottGroup, k ∈ fiveKernel ∧ k ≠ 1 ∧
      IsConj k (b * x * b⁻¹ * x⁻¹) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hab
  obtain ⟨x, k, hk, hkn, hc⟩ := ha
  refine ⟨g * x * g⁻¹, k, hk, hkn, hc.trans ?_⟩
  apply isConj_iff.mpr
  refine ⟨g, ?_⟩
  group

end CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
