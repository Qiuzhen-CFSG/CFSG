module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ThirdSpaceAction

/-!
# The original A₅ three-space clauses in F.9.1

The arbitrary T-invariant subgroup V₃ of order eight contains the original
line strictly. The literal O²(C_L(V₁))T normalizes it and acts irreducibly
on V₃/V₁. The same residual generates V₃ as [V,O²(C_L(V₁))]. The preceding
coordinate and action constructions discharge every representation premise.

Source: Aschbacher–Smith, 13.5.7(b) and the A₅ case of 13.5.14.
-/
@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Subgroup Section06.CentralizerReduction Section06.TerminalContradiction.Ratio
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
open A5Module BinaryPermutation.AlternatingFiveFlag
open scoped commutatorElement
namespace ThirdSpace
variable {G : Type*} [Group G] [Finite G] {L V V₁ : Subgroup G}
    (s : Marking L V) (hz : (zpowers (Multiplicative.ofAdd z)).map s.map=V₁)

omit [Finite G] in
theorem commutator_formula (l : residualCentralizer L V₁) (x : Space) :
    ⁅(l : G),s.map (Multiplicative.ofAdd x)⁆=
      s.map (Multiplicative.ofAdd (rho (residualAction s hz l).val.val x-x)) := by
  rw [ofAdd_sub,map_div,div_eq_mul_inv,←equivariant s hz l x]
  rfl

include hz in
theorem commutator_eq_three : ⁅V,residualCentralizer L V₁⁆=three.map s.map := by
  apply le_antisymm
  · rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    obtain ⟨y,rfl⟩ := s.range_eq.symm ▸ hx
    change ⁅(⟨l,hl⟩ : residualCentralizer L V₁).val,s.map (Multiplicative.ofAdd y.toAdd)⁆ ∈ _
    rw [commutator_formula s hz]
    exact mem_map.mpr ⟨_,difference_mem_three _ y.toAdd,rfl⟩
  · have hle : three ≤ (⁅V,residualCentralizer L V₁⁆).comap s.map := by
      apply three_le_of_differences
      intro g x
      obtain ⟨l,hl⟩ := residualAction_surjective s hz g
      change s.map (Multiplicative.ofAdd (rho g.val.val x-x)) ∈ ⁅V,residualCentralizer L V₁⁆
      rw [←hl,←commutator_formula s hz,commutator_comm]
      have hxV : s.map (Multiplicative.ofAdd x) ∈ V :=
        s.range_eq.le ⟨Multiplicative.ofAdd x,rfl⟩
      exact commutator_mem_commutator l.property hxV
    exact (map_le_iff_le_comap).mpr hle
end ThirdSpace
namespace Context
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
include d

/-- The literal source line lies strictly inside the given third flag subgroup. -/
theorem third_strict : V₁<V₃ := by
  obtain ⟨s,hz,h3⟩ := d.third_coordinates
  have hle : V₁≤V₃ := by
    rw [←hz,←h3,←line_eq_zpowers]
    exact map_mono line_le_three
  refine lt_of_le_of_ne hle ?_
  intro he
  have hh := d.flag.one_card
  rw [he,d.third_card] at hh
  omega

/-- The exact normalization clause F.9.1(b), with its original residual and Sylow. -/
theorem third_normalizes : residualCentralizer L V₁ ⊔ (T : Subgroup G) ≤
    normalizer (V₃ : Set G) := by
  refine sup_le ?_ d.third_invariant
  obtain ⟨s,hz,h3⟩ := d.third_coordinates
  apply le_normalizer_iff.mpr
  intro l hl x hx
  obtain ⟨y,hy,rfl⟩ := h3.symm ▸ hx
  change MulAut.conj (⟨l,hl⟩ : residualCentralizer L V₁).val
    (s.map (Multiplicative.ofAdd y.toAdd)) ∈ V₃
  rw [ThirdSpace.equivariant s hz]
  rw [←h3]
  exact mem_map.mpr ⟨_,three_invariant _ y hy,rfl⟩

/-- Irreducibility of the literal V₃/V₁ section, expressed without changing
its subgroup or quotient conventions. -/
theorem third_irreducible (W : Subgroup G) (h₁ : V₁≤W) (h₃ : W≤V₃)
    (hn : residualCentralizer L V₁ ⊔ (T : Subgroup G) ≤ normalizer (W : Set G)) :
    W=V₁ ∨ W=V₃ := by
  obtain ⟨s,hz,h3⟩ := d.third_coordinates
  let U := W.comap s.map
  have hu₁ : line≤U := by
    intro x hx
    exact h₁ (hz ▸ mem_map.mpr ⟨x,line_eq_zpowers ▸ hx,rfl⟩)
  have hu₃ : U≤three := by
    intro x hx
    obtain ⟨y,hy,he⟩ := h3.symm ▸ h₃ hx
    exact s.injective he ▸ hy
  have hi (g : AlternatingFiveBorel.B) (x : Multiplicative Space) (hx : x∈U) :
      Multiplicative.ofAdd (rho g.val.val x.toAdd) ∈ U := by
    obtain ⟨l,hl⟩ := ThirdSpace.residualAction_surjective s hz g
    change s.map (Multiplicative.ofAdd (rho g.val.val x.toAdd)) ∈ W
    rw [←hl,←ThirdSpace.equivariant s hz]
    have hnR : residualCentralizer L V₁ ≤ normalizer (W : Set G) := le_sup_left.trans hn
    exact (hnR l.property (s.map x)).mp hx
  have hu : U.map s.map=W := by
    change (W.comap s.map).map s.map=W
    rw [map_comap_eq,s.range_eq,inf_eq_right.mpr (h₃.trans d.third_le)]
  rcases three_line_irreducible U hu₁ hu₃ hi with he|he
  · left
    rw [←hu,he,line_eq_zpowers,hz]
  · right
    rw [←hu,he,h3]

/-- The A₅ commutator identification used in original 13.5.14. -/
theorem third_eq_commutator : V₃=⁅V,residualCentralizer L V₁⁆ := by
  obtain ⟨s,hz,h3⟩ := d.third_coordinates
  exact h3.symm.trans (ThirdSpace.commutator_eq_three s hz).symm

/-- Literal simultaneous consumer of the three module clauses of 13.5.7. -/
theorem source13_5_7_b : V₁<V₃ ∧
    residualCentralizer L V₁ ⊔ (T : Subgroup G) ≤ normalizer (V₃ : Set G) ∧
    (∀ W : Subgroup G, V₁≤W → W≤V₃ →
      residualCentralizer L V₁ ⊔ (T : Subgroup G) ≤ normalizer (W : Set G) →
      W=V₁ ∨ W=V₃) :=
  ⟨d.third_strict,d.third_normalizes,d.third_irreducible⟩
end Context
end CFSG.Quasithin.Chapter13.Section05.A5Source
