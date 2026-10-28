module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Descent
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group

/-!
# Choosing the moved component after B.5.8

A nontrivial elementary two-subgroup centralizing F(G) must move some
component: otherwise it centralizes F*(G), whose centralizer meets it
trivially when O₂(G)=1. The component commutator dichotomy and the actual
normality supplied by B.5.5(1)(i) then give L=[L,A].

This proves the component-selection paragraph preceding B.5.9, using the
minimal offender constructed from the original B.5.3 hypotheses. Component
normality and B.5.8's centralization remain explicit earlier inputs; no
component classification is assumed.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.106.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem exists_component_moved (hcore : pCore 2 G = ⊥)
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hfit : A ≤ centralizer (fittingSubgroup G : Set G)) :
    ∃ L, IsComponent G L ∧ ⁅L,A⁆ ≠ ⊥ := by
  by_contra! hn
  have hEA : componentLayer G ≤ centralizer (A : Set G) := by
    apply sSup_le
    intro L hL
    exact commutator_eq_bot_iff_le_centralizer.mp (hn L hL)
  have hFA : generalizedFitting G ≤ centralizer (A : Set G) :=
    sup_le (le_centralizer_iff.mp hfit) hEA
  let : IsElementaryAbelian 2 A := hA.1.2
  exact hA.1.1 ((ChapterB.QuasisimpleSections.disjoint_centralizer_fitting hcore A
    (IsElementaryAbelian.isPGroup 2 A)).eq_bot_of_le (le_centralizer_iff.mp hFA))

theorem exists_component_commutator (hcore : pCore 2 G = ⊥)
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hfit : A ≤ centralizer (fittingSubgroup G : Set G))
    (hn : ∀ L, IsComponent G L → L.Normal) :
    ∃ L, IsComponent G L ∧ L.Normal ∧ ⁅L,A⁆ = L ∧ L ≠ ⊥ := by
  obtain ⟨L,hL,hne⟩ := exists_component_moved ρ hcore hA hfit
  have hnormal := hn L hL
  let : L.Normal := hnormal
  have he : ⁅L,A⁆ = L := by
    rcases hL.commutator_dichotomy A with hz | he
    · exact (hne hz).elim
    · simpa only [MulEquiv.toMonoidHom_eq_coe, Subgroup.Normal.map_conj_eq,
        iSup_const] using he
  exact ⟨L,hL,hnormal,he,fun hz => hne (he.trans hz)⟩

/-- Apply the selection to an actual minimal offender from B.5.3. The two
remaining premises are B.5.8 and B.5.5(1)(i), respectively. -/
theorem select_component [Nontrivial G] {K : CFSG.Quasithin.GroupClass}
    (hyp : FFHypothesis K ρ)
    (hfit : ∀ A, IsMinimalBestOffender ρ A →
      A ≤ centralizer (fittingSubgroup G : Set G))
    (hn : ∀ L, IsComponent G L → L.Normal) :
    ∃ A L, IsMinimalBestOffender ρ A ∧ IsComponent G L ∧
      L.Normal ∧ ⁅L,A⁆ = L ∧ L ≠ ⊥ := by
  obtain ⟨A,hA⟩ := hyp.exists_minimalBestOffender ρ
  obtain ⟨L,hL,hnL,hLA,hne⟩ :=
    exists_component_commutator ρ hyp.twoCore hA.1 (hfit A hA) hn
  exact ⟨A,L,hA,hL,hnL,hLA,hne⟩

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
