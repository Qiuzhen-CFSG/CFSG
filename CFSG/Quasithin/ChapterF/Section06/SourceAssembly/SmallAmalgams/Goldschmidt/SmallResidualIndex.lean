module
public import Theory.GroupTheory.SmallInvolutionResidual
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallResidualCubicIndex

/-!
# The opposite local residual in Goldschmidt (4.2)

For a finite local group with symmetric-three quotient over its two-core,
an outside involution with core-centralizer index at most two forces the
two-residual to be cyclic of order three or alternating of degree four.
The central-displacement argument bounds the literal cubic commutator by
four; the existing residual decomposition and order recognition then apply.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (4.2),
printed pp.392--393. The crossing element of the original elementary four
supplies this involution and its centralizer bound in the source consumer.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] [Finite G]

theorem residual_cubic_or_alternatingFour_of_involution_index_le_two
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) {z : G}
    (hz : orderOf z = 2) (hn : z ∉ pCore 2 G)
    (hi : (centralizer ({z} : Set G)).relIndex (pCore 2 G) ≤ 2) :
    Nonempty ((pResidual 2 G) ≃* Multiplicative (ZMod 3)) ∨
      Nonempty ((pResidual 2 G) ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨x,hx,hsmall⟩ := SmallInvolutionResidual.exists_cubic_small_commutator e hz hn hi
  exact residual_cubic_or_alternatingFour_of_small_cubic_commutator e x hx hsmall

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
