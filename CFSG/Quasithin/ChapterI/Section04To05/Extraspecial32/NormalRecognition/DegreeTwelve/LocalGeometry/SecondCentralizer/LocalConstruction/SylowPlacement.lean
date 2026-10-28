module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Models
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.ModelFacts
public import Theory.GroupTheory.PRadicalSylowNormalizer

/-!
# Sylow placement from one common centralizer

Suppose a marked `C₂ × S₄` subgroup contains the full internal centralizer of
one of its first-class involutions. That centralizer has order sixteen, and
its center has a unique first-class element. Every element of its normalizer
fixes this element, so the centralizer is self-normalizing and hence Sylow.
Conjugacy of the three marked involutions supplies the other centralizer
containments. This proves the two global clauses of `LocalSeed` without an
ambient order or either full-centralizer model.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, opening of Lemma 4.2.
-/

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
variable {G : Type*} [Group G] {z t : G}
private theorem image_centralizer (f : Model 4 →* Centralizer t)
    (hf : Function.Injective f) (w : Model 4)
    (hc : centralizer ({f w} : Set (Centralizer t)) ≤ f.range) :
    (centralizer ({w} : Set (Model 4))).map f =
      centralizer ({f w} : Set (Centralizer t)) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hx))
  · intro y hy
    obtain ⟨x, rfl⟩ := hc hy
    refine ⟨x, mem_centralizer_singleton_iff.mpr (hf ?_), rfl⟩
    simpa only [map_mul] using mem_centralizer_singleton_iff.mp hy

/-- A marked local model and centralizer control at one first-class element
supply all Sylow and centralizer clauses of the published seed. -/
public theorem nonempty_localSeed_of_one_centralizer [Finite G] (f : Model 4 →* Centralizer t) (hf : Function.Injective f)
    (hcentral : f (centralInvolution 4) = distinguished t)
    (hfirst : ∀ x : Model 4, IsConj z (f x : G) ↔ FirstClass x)
    (w : Model 4) (hw : FirstClass w)
    (hc : centralizer ({f w} : Set (Centralizer t)) ≤ f.range) :
    Nonempty (LocalSeed z t) := by
  let P := centralizer ({f w} : Set (Centralizer t))
  have hmap := image_centralizer f hf w hc
  have hcard : Nat.card P = 16 := by
    dsimp only [P]
    rw [← hmap, card_map_of_injective hf]
    exact hw.card_centralizer_four
  have hn : normalizer (P : Set (Centralizer t)) = P := by
    apply le_antisymm _ P.le_normalizer
    intro n hn
    have hwP : f w ∈ P := mem_centralizer_singleton_iff.mpr rfl
    have hwZ : f w ∈ (center P).map P.subtype := by
      refine ⟨⟨f w, hwP⟩, mem_center_iff.mpr ?_, rfl⟩
      intro k
      exact Subtype.ext (mem_centralizer_singleton_iff.mp k.property)
    have hnZ := normalizer_le_normalizer_characteristic_image P (center P) hn
    have hvZ := (mem_normalizer_iff.mp hnZ (f w)).mp hwZ
    obtain ⟨v, hv, hvval⟩ := hvZ
    obtain ⟨y, hy⟩ := hc v.property
    have hyconj : IsConj z (f y : G) := by
      have he : (f y : G) = (n : G) * (f w : G) * (n : G)⁻¹ :=
        congrArg (fun x : Centralizer t => (x : G)) (hy.trans hvval)
      rw [he]
      exact ((hfirst w).mpr hw).trans (isConj_iff.mpr ⟨(n : G), rfl⟩)
    have hyw : y = w := hw.eq_of_centralizes_centralizer_four ((hfirst y).mp hyconj)
      (fun k hk => by
        apply hf
        simp only [map_mul]
        have hkP : f k ∈ P := by
          change f k ∈ centralizer ({f w} : Set (Centralizer t))
          rw [← hmap]
          exact mem_map_of_mem f hk
        have he := congrArg (fun x : P => (x : Centralizer t))
          ((mem_center_iff.mp hv) ⟨f k, hkP⟩)
        change f k * (v : Centralizer t) = (v : Centralizer t) * f k at he
        simpa only [← hy] using he.symm)
    have he : n * f w * n⁻¹ = f w := by
      exact hvval.symm.trans (hy.symm.trans (congrArg f hyw))
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  obtain ⟨T, hT⟩ := exists_sylow_eq_of_isPGroup_of_normalizer_eq P
    (IsPGroup.of_card (p := 2) (n := 4) hcard) hn
  refine ⟨{
    embed := f
    injective := hf
    central := hcentral
    first := hfirst
    sylow_card := ?_
    centralizer_le := ?_ }⟩
  · intro S
    calc
      Nat.card S = Nat.card T := Nat.card_congr (S.equiv T).toEquiv
      _ = 16 := by rw [hT]; exact hcard
  · intro x hx y hy
    obtain ⟨k, hk⟩ := hx.exists_conjugator_four hw
    have hkw : (MulAut.conj (f k)) (f x) = f w := by
      change f k * f x * (f k)⁻¹ = f w
      simpa only [map_mul, map_inv] using congrArg f hk
    have hyc : (MulAut.conj (f k)) y ∈ P := by
      apply mem_centralizer_singleton_iff.mpr
      simpa only [map_mul, hkw] using congrArg (MulAut.conj (f k))
        (mem_centralizer_singleton_iff.mp hy)
    have hkr : f k ∈ f.range := ⟨k, rfl⟩
    have hyr := f.range.mul_mem (f.range.mul_mem (f.range.inv_mem hkr) (hc hyc)) hkr
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
      mul_one] using hyr
end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
