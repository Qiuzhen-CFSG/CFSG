module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Reconstruction.Identification

/-!
# Moving singular seeds and relative centralizer transport

Assume the distinguished polar hyperplane is normalized by its full
centralizer. A₅-transitivity transports this to each nonsingular hyperplane.
An incident singular seed then generates that hyperplane under the full
centralizer: the lower bound is the conjugate of the actual residual span,
and the upper bound is normality. Choosing the seed in the intersection
with V_v makes it possible to conjugate both the seed and its nonsingular
index inside V_v. Fusion preserves their quadratic values and polar pairing,
so their full-centralizer spans, hence the polar hyperplanes, are transported.

Source: Aschbacher–Smith, combined manuscript, printed pp.879 and 928,
13.2.6(2) and the geometric reduction immediately preceding 13.6.8.
-/

public section

open Subgroup BinaryPermutation.FiveCentralizerGeometry
open BinaryPermutation.FiveGeometry
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
variable {G : Type*} [Group G] {L V : Subgroup G}
namespace Reconstruction

private theorem map_span (Z H : Subgroup G) (f : G →* G) :
    (conjugateSpanBy Z H).map f = conjugateSpanBy (Z.map f) (H.map f) := by
  unfold conjugateSpanBy
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨j, hj, w, hw, rfl⟩, rfl⟩
    exact ⟨f j, mem_map_of_mem f hj, f w, mem_map_of_mem f hw, by simp⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨j * w * j⁻¹, ⟨j, hj, w, hw, rfl⟩, by simp⟩

private theorem map_Gv (e : G ≃* G) (x : G) :
    (Gv x).map e.toMonoidHom = Gv (e x) := by
  apply le_antisymm
  · rintro y ⟨a, ha, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e a * e x = e x * e a
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp ha)
  · intro y hy
    refine ⟨e.symm y, mem_centralizer_singleton_iff.mpr ?_, e.apply_symm_apply y⟩
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hy

/-- Relative normality at v transports to every nonsingular polar hyperplane. -/
theorem centralizer_normalizes_perp (s : A5Module.Marking L V)
    (hf : FusionPreservesForm s)
    (hn : Gv (A5Module.markedV s) ≤ normalizer (vectorPerp s v : Set G))
    (u : Space) (hu : form u ≠ 0) :
    Gv (s.map (Multiplicative.ofAdd u)) ≤ normalizer (vectorPerp s u : Set G) := by
  have hv : form v ≠ 0 := by decide
  have hq : form v = form u :=
    (by decide : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a = b) _ _ hv hu
  obtain ⟨a, ha⟩ := exists_even_transport v u v_ne_zero
    (fun he => hu (he ▸ form.map_zero)) hq
  obtain ⟨l, hl⟩ := s.onto a
  have he : MulAut.conj (l : G) (s.map (Multiplicative.ofAdd v)) =
      s.map (Multiplicative.ofAdd u) := by rw [s.equivariant, hl, ha]
  have hp := vectorPerp_conjugate s hf (l : G) (L_normalizes s l.property) v u he
  have hh := map_mono (f := (MulAut.conj (l : G)).toMonoidHom) hn
  rw [map_Gv, map_equiv_normalizer_eq, hp] at hh
  exact he ▸ hh

/-- A moving singular seed generates its nonsingular polar hyperplane under
its full centralizer, if the distinguished hyperplane is relatively normal. -/
theorem perp_eq_centralizer_span [Finite G] (s : A5Module.Marking L V)
    (hf : FusionPreservesForm s)
    (hn : Gv (A5Module.markedV s) ≤ normalizer (vectorPerp s v : Set G))
    (u t : Space) (hu : form u ≠ 0) (ht : form t = 0) (ht0 : t ≠ 0)
    (hut : form.polarBilin u t = 0) :
    vectorPerp s u = conjugateSpanBy (zpowers (s.map (Multiplicative.ofAdd t)))
      (Gv (s.map (Multiplicative.ofAdd u))) := by
  apply le_antisymm
  · obtain ⟨a, hav, haz⟩ := Model.flag_transport u t hu ht ht0 hut
    obtain ⟨l, hl⟩ := s.onto a
    have hev : MulAut.conj (l : G) (s.map (Multiplicative.ofAdd v)) =
        s.map (Multiplicative.ofAdd u) := by rw [s.equivariant, hl, hav]
    have hez : MulAut.conj (l : G) (s.map (Multiplicative.ofAdd z)) =
        s.map (Multiplicative.ofAdd t) := by rw [s.equivariant, hl, haz]
    have hp := vectorPerp_conjugate s hf (l : G) (L_normalizes s l.property) v u hev
    have hactor : (Lv L (A5Module.markedV s)).map (MulAut.conj (l : G)).toMonoidHom ≤
        Gv (s.map (Multiplicative.ofAdd u)) := by
      have hh := map_mono (f := (MulAut.conj (l : G)).toMonoidHom)
        (Lv_le_Gv L (A5Module.markedV s))
      rw [map_Gv] at hh
      exact hev ▸ hh
    rw [← hp, ← Vv_eq_vectorPerp s]
    change (conjugateSpanBy _ _).map _ ≤ _
    rw [map_span, MonoidHom.map_zpowers]
    change conjugateSpanBy (zpowers (MulAut.conj (l : G)
      (s.map (Multiplicative.ofAdd z)))) _ ≤ _
    rw [hez]
    exact conjugateSpanBy_mono le_rfl hactor
  · exact conjugateSpanBy_le (zpowers_le.mpr ⟨Multiplicative.ofAdd t, hut, rfl⟩)
      (centralizer_normalizes_perp s hf hn u hu)

/-- Conjugation in G_v transports a family member even before normalization
of V is known. The seed is chosen in the intersection with V_v. -/
theorem perp_conjugate_of_normal [Finite G] (s : A5Module.Marking L V)
    (hf : FusionPreservesForm s)
    (hn : Gv (A5Module.markedV s) ≤ normalizer (vectorPerp s v : Set G))
    (g : G) (hg : g ∈ Gv (A5Module.markedV s))
    (u w : Space) (hu : form u ≠ 0) (hvu : form.polarBilin v u = 0)
    (huw : MulAut.conj g (s.map (Multiplicative.ofAdd u)) =
      s.map (Multiplicative.ofAdd w)) :
    (vectorPerp s u).map (MulAut.conj g).toMonoidHom = vectorPerp s w := by
  obtain ⟨t, ht0, ht, hvt, hut⟩ := Model.common_seed u hu hvu
  have htmem : s.map (Multiplicative.ofAdd t) ∈ vectorPerp s v :=
    ⟨Multiplicative.ofAdd t, hvt, rfl⟩
  have hyt : MulAut.conj g (s.map (Multiplicative.ofAdd t)) ∈ vectorPerp s v :=
    (mem_normalizer_iff.mp (hn hg) _).mp htmem
  obtain ⟨y, hy⟩ := s.range_eq.ge (vectorPerp_le s v hyt)
  have hty : MulAut.conj g (s.map (Multiplicative.ofAdd t)) =
      s.map (Multiplicative.ofAdd y.toAdd) := hy.symm
  have hy0 : y.toAdd ≠ 0 := by
    intro he
    have he1 : MulAut.conj g (s.map (Multiplicative.ofAdd t)) = 1 := by
      rw [hty, he]
      exact s.map.map_one
    have ht1 : s.map (Multiplicative.ofAdd t) = s.map 1 := by
      rw [map_one]
      exact (MulAut.conj g).injective (he1.trans (map_one (MulAut.conj g)).symm)
    exact ht0 (congrArg Multiplicative.toAdd (s.injective ht1))
  have hyq : form y.toAdd = 0 := (hf g t y.toAdd hty).symm.trans ht
  have hwq : form w ≠ 0 := fun he => hu ((hf g u w huw).trans he)
  have hwy : form.polarBilin w y.toAdd = 0 :=
    (polar_eq_of_conjugates s hf g u t w y.toAdd huw hty).symm.trans hut
  rw [perp_eq_centralizer_span s hf hn u t hu ht ht0 hut, map_span,
    MonoidHom.map_zpowers, map_Gv]
  change conjugateSpanBy (zpowers (MulAut.conj g (s.map (Multiplicative.ofAdd t))))
    (Gv (MulAut.conj g (s.map (Multiplicative.ofAdd u)))) = _
  rw [hty, huw]
  exact (perp_eq_centralizer_span s hf hn w y.toAdd hwq hyq hy0 hwy).symm

end Reconstruction
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
