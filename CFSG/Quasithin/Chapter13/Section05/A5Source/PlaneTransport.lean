module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.PlaneCoordinates
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ThirdSpaceAction

/-!
# Original plane transport under O²(C_L(V₁))

Use one simultaneous marking of V₁,V₂,V₃. The literal residual maps onto
the full A₄ point stabilizer. Its transitivity outside the fixed line
therefore moves any subgroup strictly above V₁ in V₃ to contain V₂.
No transitivity or compatibility premise remains in this source step.
Source: Aschbacher–Smith13.5.13(1), printed p.919.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open Subgroup Section06.TerminalContradiction.Ratio
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
open BinaryPermutation.AlternatingFiveFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- The actual residual supplies the conjugator in the plane-transport step. -/
theorem plane_transport (W : Subgroup G) (hW : V₁ < W) (hW₃ : W ≤ V₃) :
    ∃ l ∈ residualCentralizer L V₁, V₂ ≤ W.map (MulAut.conj l).toMonoidHom := by
  obtain ⟨s,hz,hplane,hthree⟩ := d.plane_third_coordinates
  let U := W.comap s.map
  have hu : U.map s.map = W := by
    rw [map_comap_eq,s.range_eq,inf_eq_right.mpr (hW₃.trans d.third_le)]
  have hline : line < U := by
    apply lt_of_le_not_ge
    · intro x hx
      exact hW.le (hz ▸ mem_map_of_mem s.map (line_eq_zpowers ▸ hx))
    · intro hle
      apply hW.not_ge
      rw [←hu,←hz,←line_eq_zpowers]
      exact map_mono hle
  have hUthree : U ≤ three := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hthree.symm ▸ hW₃ hx
    exact s.injective he ▸ hy
  obtain ⟨g,hg⟩ := plane_le_image U hline hUthree
  obtain ⟨l,hl⟩ := ThirdSpace.residualAction_surjective s hz g
  refine ⟨l,l.property,?_⟩
  rw [←hplane]
  rintro y ⟨a,ha,rfl⟩
  obtain ⟨b,hb,he⟩ := hg ha
  refine ⟨s.map b,hb,?_⟩
  change MulAut.conj (l : G) (s.map (Multiplicative.ofAdd b.toAdd)) = s.map a
  rw [ThirdSpace.equivariant s hz,hl]
  exact congrArg s.map he

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
