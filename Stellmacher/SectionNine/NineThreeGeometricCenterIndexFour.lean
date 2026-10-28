module
public import Stellmacher.SectionNine.NineThreeGeometricCenterIntersections

/-!
# Exact index four between extracted centers

In the actual ambient setting of (9.3), retain the geometric extraction at
an edge in the terminal-vertex orbit. An intermediate subgroup Y contains
the intersection I of the original and extracted centers. Suppose that Y
has index two in the extracted center and has order at most twice |I|,
while the original center has order greater than four. Then |Y|=2|I| and
the extracted center has order 4|I|.

The proof excludes Y=I: the conjugate centers would then have intersection
of index two, and the extraction's core-edge generation equality lets
(9.2) force their order to be four. Subgroup index divisibility makes the
remaining lower bound 2|I|≤|Y| exact. This supplies the inner index in
Stellmacher (9.3)(4), Journal of Algebra 190 (1997), p.49,
`refs/files/stellmacher-n-group.pdf`, preserving the actual extracted data.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_geometric_center_index_four
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (d l : ctx.Γ.Vertex)
    (hd : IsConjugateVertex ctx.Γ ctx.criticalPath.a' d)
    (hl : l ∈ neighborhood ctx.Γ d)
    (V E A0 : Subgroup G) (hVQ : V ≤ QAt ctx.Γ l)
    (actor : G) (data : NineThreeGeometricData ctx.Γ d l V E A0 actor)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ l))
    (Y : Subgroup G)
    (hIY : ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓ ZAt ctx.Γ l ≤ Y)
    (_hYm : Y ≤ ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l))
    (hdouble : Nat.card (ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l)) = 2 * Nat.card Y)
    (hbound : Nat.card Y ≤ 2 * Nat.card ↥(ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓ ZAt ctx.Γ l)) :
    Nat.card Y = 2 * Nat.card ↥(ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓ ZAt ctx.Γ l) ∧
      Nat.card (ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l)) =
        4 * Nat.card ↥(ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓ ZAt ctx.Γ l) := by
  let Γ := ctx.Γ
  let m := Γ.act data.x⁻¹ l
  let I := ZAt Γ m ⊓ ZAt Γ l
  have hmlcard : Nat.card (ZAt Γ m) = Nat.card (ZAt Γ l) := by
    change Nat.card (z Γ (Γ.act data.x⁻¹ l)) = _
    rw [z_act,inv_inv]
    exact Subgroup.card_map_of_injective (MulAut.conj data.x).injective
  have hne : I ≠ Y := by
    intro he
    have hindex : QuotientCardEq (ZAt Γ l) (ZAt Γ l ⊓ ZAt Γ m) 2 := by
      change Nat.card (ZAt Γ l) = 2 * Nat.card ↥(ZAt Γ l ⊓ ZAt Γ m)
      rw [← hmlcard,inf_comm]
      exact hdouble.trans (congrArg (fun U : Subgroup G => 2 * Nat.card U) he.symm)
    have hgen := geometric_extraction_core_edge_generation ctx.sectionSeven Γ d l
      V E A0 actor hVQ data
    have hnine := lemma_nine_two_ambient ctx d l m hd hl data.neighbor hindex hgen
    exact (ne_of_gt hlarge) hnine.2
  have hlt : Nat.card I < Nat.card Y := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le hIY)
    intro he
    exact hne (Subgroup.eq_of_le_of_card_ge hIY he.ge)
  obtain ⟨n,hn⟩ := Subgroup.card_dvd_of_le hIY
  have hpos : 0 < Nat.card I := Nat.card_pos
  have hn2 : 2 ≤ n := by nlinarith
  have hlow : 2 * Nat.card I ≤ Nat.card Y := by nlinarith
  have hY : Nat.card Y = 2 * Nat.card I := le_antisymm hbound hlow
  refine ⟨hY,?_⟩
  calc
    Nat.card (ZAt Γ m) = 2 * Nat.card Y := hdouble
    _ = 2 * (2 * Nat.card I) := by rw [hY]
    _ = 4 * Nat.card I := by omega
end Stellmacher.SectionNine
