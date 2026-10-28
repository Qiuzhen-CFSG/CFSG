module
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Bounds
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Transport
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Quotient
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.HigmanSims.Inputs
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.HigmanSims.Projection

/-!
# Conditional HS pair-fixer assembly

Project the actual smaller component and the actual source involution through
I → I/O₂(I) ≅ HS. The projection results preserve its component position and
alternating isomorphism type. An intrinsic A₆ or A₈ fixer calculation then
transfers through the faithful automorphism descent of the perfect central
cover, giving both the upper cardinality bound and the square identities.

The two intrinsic calculations remain explicit inputs. This module does not
yet assert `HigmanSimsBound` from `PairContext` alone. In particular it neither
assumes a fixer order of four for every embedding nor constructs the mixed HS
layers; the faithful actor supplies the lower bound in the parent assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(10), 16.1.7(3h), and 16.3.5, printed pp.1172–1173 and 1178–1179.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
open Subgroup Theory.GroupTheory ClassificationModels HigmanSims
universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
variable {E L I : Subgroup G} {t i : G}

/-- Transfer one intrinsic alternating-component calculation through the actual cover. -/
theorem fourBound_of_hs_component_bound (hG : Hypothesis1611 𝒦 G)
    (h : PairContext E L I t i) {n : ℕ} (hn : 5 ≤ n)
    (hb : ComponentFixerBound n)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier)
    (eL : L ≃* alternatingGroup (Fin n)) : FourBound L I := by
  let : IsSimpleGroup Sporadic.LeechRelated.HS.Carrier := quotient_simple h hG e
  let : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier := quotient_perfect h hG e
  obtain ⟨eK⟩ := projected_equiv h hG e (by omega) eL
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  let : IsSimpleGroup (projected h hG e) := eK.isSimpleGroup
  have hne : projected h hG e ≠ ⊥ := (nontrivial_iff_ne_bot _).mp inferInstance
  have hh := hb (quotientInvolution h hG e) (projected h hG e)
    (quotientInvolution_order h hG e) (component_quotient_fixed h hG e hne) ⟨eK⟩
  exact fourBound_of_cover (h.coreCover hG e) (h.coreCover_kernel hG e) hh.1 hh.2

/-- Conditional assembly of the two HS rows. The intrinsic component-fixer
calculations remain explicit until their separate owners discharge them. -/
theorem higmanSimsBound_of_component_bounds (hG : Hypothesis1611 𝒦 G)
    (h : PairContext E L I t i)
    (h6 : ComponentFixerBound 6) (h8 : ComponentFixerBound 8) : HigmanSimsBound L I := by
  intro he hL
  obtain ⟨e⟩ := he
  rcases hL with hL | hL
  · obtain ⟨eL⟩ := hL
    exact fourBound_of_hs_component_bound hG h (by decide) h6 e eL
  · obtain ⟨eL⟩ := hL
    exact fourBound_of_hs_component_bound hG h (by decide) h8 e eL

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
