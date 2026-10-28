module
public import Theory.SpecificGroups.SymmetricFourWreath.ElementaryGeometry

/-!
# The dihedral base and its normalizer in the actual local model

Membership in the base and its four elementary subgroups is expressed by
the two literal coordinates. A normalizer of the dihedral base normalizes
the square-dihedral subgroup in each S4 coordinate; the latter subgroup is
self-normalizing. Thus its wreath normalizer is precisely the marked Sylow.

Source: Aschbacher–Smith 13.9.2(1–2), printed p.969 (PDF p.986).
-/

public section
namespace SymmetricFourWreath
open Subgroup

theorem c2_eq_one_or_turn (q : C2) : q=1 ∨ q=turn := by revert q;decide +kernel

theorem mem_standardSylow (w : W) : w∈(standardSylow:Subgroup W) ↔ ∀i,w.left i∈square.range := by
  constructor
  · rintro ⟨x,rfl⟩ i
    exact ⟨x.left i,rfl⟩
  · intro h
    choose a ha using h
    refine ⟨⟨a,w.right⟩,?_⟩
    exact RegularWreathProduct.ext (funext ha) rfl

theorem mem_J (w : W) : w∈J ↔ w.right=1 ∧ ∀i,w.left i∈square.range := by
  constructor
  · rintro ⟨_,⟨a,rfl⟩,rfl⟩
    exact ⟨rfl,fun i=>⟨(pair a).left i,rfl⟩⟩
  · rintro ⟨hw,h⟩
    obtain ⟨a,ha⟩ := h 1
    obtain ⟨b,hb⟩ := h turn
    refine ⟨pair (a,b),⟨(a,b),rfl⟩,?_⟩
    apply RegularWreathProduct.ext
    · funext i
      rcases c2_eq_one_or_turn i with rfl|rfl
      · exact ha
      · simpa [sylowEmbedding,pair,turn_ne_one] using hb
    · exact hw.symm

theorem mem_elementary (b c : Bool) (w : W) : w∈elementary b c ↔
    w.right=1 ∧ w.left 1∈(plane b).map square ∧ w.left turn∈(plane c).map square := by
  constructor
  · rintro ⟨_,⟨⟨a,d⟩,⟨ha,hd⟩,rfl⟩,rfl⟩
    exact ⟨rfl,⟨a,ha,rfl⟩,⟨d,hd,by simp [sylowEmbedding,pair,turn_ne_one]⟩⟩
  · rintro ⟨hw,⟨a,ha,hea⟩,⟨d,hd,hed⟩⟩
    refine ⟨pair (a,d),⟨(a,d),⟨ha,hd⟩,rfl⟩,?_⟩
    apply RegularWreathProduct.ext
    · funext i
      rcases c2_eq_one_or_turn i with rfl|rfl
      · exact hea
      · simpa [sylowEmbedding,pair,turn_ne_one] using hed
    · exact hw.symm

theorem card_J : Nat.card J=64 := by
  rw [J,card_map_of_injective sylowEmbedding_injective,
    ←Nat.card_congr (MonoidHom.ofInjective pair_injective).toEquiv,Nat.card_prod,
    DihedralGroup.nat_card]

theorem conjugate_left (g w : W) (hw : w.right=1) (i : C2) :
    (g*w*g⁻¹).left i=g.left i*w.left (g.right⁻¹*i)*(g.left i)⁻¹ := by
  simp [hw]

private theorem square_normalizer_test : ∀ g : S4,
    (∀a : D8, ∃b : D8,g*square a*g⁻¹=square b) → ∃a : D8,square a=g := by
  decide +kernel

theorem normalizer_J : normalizer (J:Set W)=(standardSylow:Subgroup W) := by
  apply le_antisymm
  · intro g hg
    apply (mem_standardSylow g).mpr
    intro i
    apply square_normalizer_test
    intro a
    have hx : (⟨fun _=>square a,1⟩:W)∈J := (mem_J _).mpr ⟨rfl,fun _=>⟨a,rfl⟩⟩
    have hy := (mem_J _).mp ((mem_normalizer_iff.mp hg _).mp hx)
    obtain ⟨b,hb⟩ := hy.2 i
    refine ⟨b,?_⟩
    exact (conjugate_left g ⟨fun _=>square a,1⟩ rfl i).symm.trans hb.symm
  · intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨w,hw,rfl⟩
      apply (mem_J _).mpr
      have hwr := ((mem_J w).mp hw).1
      refine ⟨by change (g*w*g⁻¹).right=1;simp [hwr],?_⟩
      intro i
      change (g*w*g⁻¹).left i∈square.range
      rw [conjugate_left g w hwr i]
      exact square.range.mul_mem (square.range.mul_mem ((mem_standardSylow g).mp hg i)
        (((mem_J w).mp hw).2 _)) (square.range.inv_mem ((mem_standardSylow g).mp hg i))
    · rw [card_map_of_injective (MulAut.conj g).injective]
end SymmetricFourWreath
