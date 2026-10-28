module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.CriticalPairCentralized
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParity

/-!
# The remaining critical pair on the original chosen setup

Compatible Cartans and the specialized module give the actual critical path.
The first terminal branch of 5.1.17 is excluded, and the opposite kernel moves
an endpoint conjugate of the natural module. The commutator, normalizer and
opposite-core containments all retain the source subgroups.

The odd preparation and the displacement lower bound are still explicit
source inputs. Their discharge and the second terminal branch remain with
`qt-d-1222-linear-field-parity`; this is not an unconditional parity theorem.
Source: Aschbacher–Smith, 5.1.17, printed pp.641–642, and its application in
12.2.2, printed p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The literal chosen-module application, leaving only the proper-centralizer
branch after the two earlier parity inputs have been supplied. -/
theorem rankOne_odd_critical_moved_module_of_parity_sources
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hodd : Odd n)
    (hseed : OddSeedSource T L H n)
    (hlower : DisplacementSource T L H n) :
    ∃ A B : Subgroup G, CartanPair T L H A B ∧
      ∃ (s : Seed T L H A n) (C : s.f8.CriticalPath),
        C.Dg ≠ C.Ug ∧ ⁅C.DH,C.Ug⁆ ≠ ⊥ ∧
        ∃ b : (setup T L s.V H A).H,
          let W := s.V.map (MulAut.conj ((C.g : G) * b)).toMonoidHom
          W ≤ C.Ug ∧ C.A₁ ≤ W ∧ ⁅C.DH,W⁆ ≠ ⊥ ∧
            C.DH ≤ normalizer (W : Set G) ∧
            W ⊓ (setup T L s.V H A).QH ≤ centralizer (C.DH : Set G) := by
  obtain ⟨A,B,c⟩ := D.rankOne_exists_cartanPair h.toHypothesis1221 hn hpsl hH hgen
  obtain ⟨s⟩ := hseed A B c hodd
  obtain ⟨C⟩ := s.f8.exists_criticalPath
  have hlarge := hlower A B c hodd s
  exact ⟨A,B,c,s,C,s.critical_centralizer_ne_span C hlarge,
    s.critical_kernels_do_not_centralize C hlarge,
    s.exists_moved_endpoint_module C hlarge⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
