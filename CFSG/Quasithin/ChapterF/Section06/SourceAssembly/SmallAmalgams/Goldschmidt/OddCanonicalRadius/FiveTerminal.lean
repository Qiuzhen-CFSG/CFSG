module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelFacts
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The terminal radius-five contradiction

The midpoint commutator identity on eight-arcs is the remaining source input.
Folding two four-edge track segments by the opposite labels identifies two
fourth powers. Since these powers are inverse involutions, their labels agree;
their different exact fixed intervals exclude that equality.

Source: Goldschmidt (1980), (6.11), printed p.403.
-/

@[expose] public section
open Subgroup SimpleGraph
open Theory.GroupAction.CubicTree
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

namespace CanonicalLabelSetup

private theorem folded_midpoint (d : CanonicalLabelSetup F s)
    (hmid : ∀ {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) 8 v),
      p.Nonbacktracking → v.type = d.side →
      ⁅d.label v, d.label p.endpoint⁆ = d.label (p.toWalk.getVert 4))
    (t : Track (RankTwo.graph F) G) (a : ℤ) (ha : (t.vertex a).type = d.side)
    (x : G) (hx : x • t.vertex (a+4) = t.vertex (a+4))
    (hmove : x • t.vertex (a+3) ≠ t.vertex (a+3)) :
    ⁅d.label (t.vertex a), x * d.label (t.vertex a) * x⁻¹⁆ =
      d.label (t.vertex (a+4)) := by
  have h01 := t.adjacent a
  have h12 : (RankTwo.graph F).Adj (t.vertex (a+1)) (t.vertex (a+2)) := by
    simpa only [show a+1+1=a+2 by omega] using t.adjacent (a+1)
  have h23 : (RankTwo.graph F).Adj (t.vertex (a+2)) (t.vertex (a+3)) := by
    simpa only [show a+2+1=a+3 by omega] using t.adjacent (a+2)
  have h34 : (RankTwo.graph F).Adj (t.vertex (a+3)) (t.vertex (a+4)) := by
    simpa only [show a+3+1=a+4 by omega] using t.adjacent (a+3)
  have h45 : (RankTwo.graph F).Adj (t.vertex (a+4)) (x • t.vertex (a+3)) := by
    simpa only [hx] using trackGraphAction.map_adj x h34.symm
  let p : BasedWalk (RankTwo.graph F) 8 (t.vertex a) :=
    ⟨⟨t.vertex (a+1), h01⟩, ⟨⟨t.vertex (a+2), h12⟩,
      ⟨⟨t.vertex (a+3), h23⟩, ⟨⟨t.vertex (a+4), h34⟩,
        ⟨⟨x • t.vertex (a+3), h45⟩,
          ⟨⟨x • t.vertex (a+2), trackGraphAction.map_adj x h23.symm⟩,
            ⟨⟨x • t.vertex (a+1), trackGraphAction.map_adj x h12.symm⟩,
              ⟨⟨x • t.vertex a, trackGraphAction.map_adj x h01.symm⟩,
                PUnit.unit⟩⟩⟩⟩⟩⟩⟩⟩
  have hp : p.Nonbacktracking := by
    refine ⟨?_, ?_, ?_, hmove, ?_, ?_, ?_, trivial⟩
    · intro he
      have := t.injective he
      omega
    · intro he
      have := t.injective he
      omega
    · intro he
      have := t.injective he
      omega
    · intro he
      have he' : x • t.vertex (a+2) = x • t.vertex (a+4) := he.trans hx.symm
      have := t.injective ((MulAction.toPerm x).injective he')
      omega
    · intro he
      have := t.injective ((MulAction.toPerm x).injective he)
      omega
    · intro he
      have := t.injective ((MulAction.toPerm x).injective he)
      omega
  have hh := hmid p hp ha
  change ⁅d.label (t.vertex a), d.label (x • t.vertex a)⁆ =
    d.label (t.vertex (a+4)) at hh
  rwa [d.conjugate x _ ha] at hh

/-- Goldschmidt (6.11)'s final contradiction once its eight-arc identity is
available. The whole-track fixed intervals avoid any extra bound on `s`. -/
theorem radius_ne_five_of_midpoint (d : CanonicalLabelSetup F s)
    (hmid : ∀ {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) 8 v),
      p.Nonbacktracking → v.type = d.side →
      ⁅d.label v, d.label p.endpoint⁆ = d.label (p.toWalk.getVert 4)) :
    d.radius ≠ 5 := by
  intro hr
  let t := d.track
  let c := d.center
  let z := d.label (t.vertex c)
  let w := d.label (t.vertex (c+10))
  have ht10 : (t.vertex (c+10)).type = d.side := by
    simpa only [show (2:ℤ)*5=10 by norm_num] using d.shifted_type 5
  have hwfix : w • t.vertex (c+4) = t.vertex (c+4) := by
    exact (d.shifted_fixed_iff 5 (c+4)).2 (by dsimp [c]; rw [hr]; norm_num; omega)
  have hwmove : w • t.vertex (c+3) ≠ t.vertex (c+3) := by
    intro he
    have hh := (d.shifted_fixed_iff 5 (c+3)).1 he
    rw [hr] at hh
    dsimp [c] at hh
    norm_num at hh
    omega
  have hzfix : z • t.vertex (c+6) = t.vertex (c+6) := by
    have hh := (d.shifted_fixed_iff 0 (c+6)).2 (by dsimp [c]; rw [hr]; norm_num; omega)
    simpa only [mul_zero, add_zero] using hh
  have hzmove : z • t.vertex (c+7) ≠ t.vertex (c+7) := by
    intro he
    have hh := (d.shifted_fixed_iff 0 (c+7)).1 (by simpa only [mul_zero, add_zero] using he)
    rw [hr] at hh
    dsimp [c] at hh
    norm_num at hh
  have hleft : ⁅z, w*z*w⁻¹⁆ = d.label (t.vertex (c+4)) :=
    d.folded_midpoint hmid t c d.center_type w hwfix hwmove
  have hright : ⁅w, z*w*z⁻¹⁆ = d.label (t.vertex (c+6)) := by
    have hh := d.folded_midpoint hmid t.reverse (-(c+10))
      (by simpa only [Track.reverse, neg_neg] using ht10) z
      (by simpa only [Track.reverse, show -(-(c+10)+4)=c+6 by omega] using hzfix)
      (by simpa only [Track.reverse, show -(-(c+10)+3)=c+7 by omega] using hzmove)
    simpa only [Track.reverse, neg_neg, show -(-(c+10)+4)=c+6 by omega] using hh
  have hz : z⁻¹ = z := d.label_inv d.center_type
  have hw : w⁻¹ = w := d.label_inv ht10
  have hpow : (z*w)^4 = d.label (t.vertex (c+4)) := by
    calc
      (z*w)^4 = ⁅z, w*z*w⁻¹⁆ := by
        simp only [commutatorElement_def, mul_inv_rev, hz, hw,
          pow_succ, pow_zero, one_mul, mul_assoc]
      _ = _ := hleft
  have hpow' : (w*z)^4 = d.label (t.vertex (c+6)) := by
    calc
      (w*z)^4 = ⁅w, z*w*z⁻¹⁆ := by
        simp only [commutatorElement_def, mul_inv_rev, hz, hw,
          pow_succ, pow_zero, one_mul, mul_assoc]
      _ = _ := hright
  have hlabels : d.label (t.vertex (c+4)) = d.label (t.vertex (c+6)) := by
    have ht4 : (t.vertex (c+4)).type = d.side := by
      simpa only [show (2:ℤ)*2=4 by norm_num] using d.shifted_type 2
    calc
      d.label (t.vertex (c+4)) = (d.label (t.vertex (c+4)))⁻¹ := (d.label_inv ht4).symm
      _ = ((z*w)^4)⁻¹ := congrArg Inv.inv hpow.symm
      _ = (w*z)^4 := by rw [← inv_pow, mul_inv_rev, hz, hw]
      _ = _ := hpow'
  have hfour : d.label (t.vertex (c+4)) • t.vertex (c-2) = t.vertex (c-2) := by
    exact (d.shifted_fixed_iff 2 (c-2)).2 (by dsimp [c]; rw [hr]; norm_num; omega)
  rw [hlabels] at hfour
  have hh := (d.shifted_fixed_iff 3 (c-2)).1 hfour
  rw [hr] at hh
  dsimp [c] at hh
  norm_num at hh

end CanonicalLabelSetup
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
