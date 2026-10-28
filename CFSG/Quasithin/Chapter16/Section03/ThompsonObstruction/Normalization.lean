module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Normalization.Normality
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Normalization.Marking
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Normalization.WreathModel

/-!
# Normalization for the terminal Thompson obstruction

`exists_selected` chooses the permitted conjugate, transports the actual marked
layer enlargement, and constructs the two local Sylow subgroups. The enlargement
is normal in C_G(t), and its centralizer in the chosen P is exactly ⟨t⟩. Constructing
`Prepared` still requires a compatible marking placing the double transposition
in T and in C_G(T_L), and the actual C₂ × (D₈ wreath C₂) isomorphism with its two
specified factor equations. Those remaining obligations belong to this module's
assembly; no Thompson-subgroup or rank assertion is used for normalization.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1181–1182 / PDF pp.1198–1199.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction
variable {G : Type*} [Group G]

/-! The final normalization packages the selected conjugate, compatible
marking, and concrete local Sylow model into the complete `Prepared` input
used by the Thompson obstruction. -/

theorem exists_prepared [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}
    (h : TerminalCounterexample T z L t)
    (shape : NonterminalCentralizerShape T z L t)
    (d : MarkedEnlargement z t L) :
    ∃ c : G, c ∈ involutionCentralizer z ∧
      Nonempty (Prepared T z ((MulAut.conj c) t) L) := by
  obtain ⟨c, hc, hs⟩ := exists_selected h shape d
  obtain ⟨s⟩ := hs
  obtain ⟨marked, huT, huC⟩ := s.exists_compatible_marking
  obtain ⟨model, hcentral, hwreath⟩ := s.exists_marked_model
  refine ⟨c, hc, ⟨{
    counterexample := s.counterexample
    shape := s.shape
    marked := marked
    centralizer_sylow := s.centralizer_sylow
    P := s.P
    centralizer_le := s.centralizer_le
    u_mem := huT
    u_centralizes_componentSylow := huC
    model := model
    model_centralFactor := hcentral
    model_wreathFactor := hwreath }⟩⟩

end CFSG.Quasithin.Chapter16.ThompsonObstruction
