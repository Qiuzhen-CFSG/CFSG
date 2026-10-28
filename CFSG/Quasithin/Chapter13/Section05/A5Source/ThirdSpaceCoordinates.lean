module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Context
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.SylowCalculation
public import Theory.Representation.BinaryAlternatingFiveFlag.Borel

/-!
# The original invariant order-eight subgroup in five-point coordinates

Relabel the given source flag using its already proved Sylow alignment.
The line is then the all-one four-vector. Its Sylow image fixes the fifth
letter and contains the regular Klein four group. The orbit-basis argument
forces the arbitrary original invariant subgroup of order eight to be the
standard coordinate hyperplane. No coordinate condition on V₃ is assumed.

Source: Aschbacher–Smith, 13.5.7(b) and the A₅ case of 13.5.14.
-/
@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Subgroup Section06.CentralizerReduction
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
open A5Module A5Module.FlagCoordinates
namespace Context
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
include d

/-- A single relabelling marks both the original central line and its original
Sylow-invariant three-space. -/
theorem third_coordinates : ∃ s : Marking L V,
    (zpowers (Multiplicative.ofAdd z)).map s.map = V₁ ∧
    BinaryPermutation.AlternatingFiveFlag.three.map s.map = V₃ := by
  obtain ⟨g,hz,hv,hvn,hN,hT⟩ := d.flag.exists_coordinate_witness
  let f := d.flag.relabel g
  have hline : (zpowers (Multiplicative.ofAdd z)).map f.module.map=V₁ := by
    have hh := congrArg (Subgroup.map d.flag.module.map) hz
    rw [MonoidHom.map_zpowers,d.flag.preimage_map V₁ (d.flag.one_le_two.trans d.flag.two_le_V)] at hh
    rw [MonoidHom.map_zpowers]
    exact hh
  have hpre : f.preimage V₁=zpowers (Multiplicative.ofAdd z) := by
    apply (Subgroup.map_injective f.module.injective)
    rw [f.preimage_map V₁ (d.flag.one_le_two.trans d.flag.two_le_V),hline]
  have hfix (p : f.image) (hp : p∈f.imageSylow) : rho p.val z=z := by
    have hm := f.preimage_invariant V₁ f.one_invariant p hp (Multiplicative.ofAdd z)
      (hpre.symm ▸ mem_zpowers (Multiplicative.ofAdd z))
    rw [hpre] at hm
    have he : Multiplicative.ofAdd (rho p.val z)=1 ∨
        Multiplicative.ofAdd (rho p.val z)=Multiplicative.ofAdd z := by
      change Multiplicative.ofAdd (rho p.val z) ∈ BinaryPermutation.AlternatingFiveFlag.line
      rw [BinaryPermutation.AlternatingFiveFlag.line_eq_zpowers]
      exact hm
    rcases he with he|he
    · have hh : coordinateEquiv p.val (Multiplicative.ofAdd z)=coordinateEquiv p.val 1 :=
        he.trans (map_one _).symm
      exact (z_ne_zero ((coordinateEquiv p.val).injective hh)).elim
    · exact he
  have hfour := BinaryPermutation.AlternatingFiveFlag.four_le_sylow f.image f.alternating_le_image
    f.imageSylow hfix
  have hthree : f.preimage V₃=BinaryPermutation.AlternatingFiveFlag.three := by
    apply BinaryPermutation.AlternatingFiveFlag.three_eq_of_card_invariant
    · exact (f.preimage_card V₃ d.third_le).trans d.third_card
    · intro k hk x hx
      obtain ⟨p,hp,he⟩ := hfour hk
      rw [←he]
      exact f.preimage_invariant V₃ d.third_invariant p hp x hx
  refine ⟨f.module,hline,?_⟩
  rw [←hthree,f.preimage_map V₃ d.third_le]

end Context
end CFSG.Quasithin.Chapter13.Section05.A5Source
