module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Bounds
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Janko.AlternatingModel
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Janko.Reduction

/-!
# The two J₂ pair-fixer bounds

The PSL₃(2) row is excluded by the given faithful order-four action and the
checked inner-centralizer orders. The A₅ row reduces to the full pointwise
fixer of the actual projected component. Its intrinsic bound remains an
explicit input below; this file does not yet discharge that calculation.

Source: Aschbacher–Smith, 16.1.5(8), 16.1.7(3f,g), and 16.3.5,
combined manuscript of 1 March 2004, printed pp.1172–1173 and 1178–1179.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Janko
universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
variable {E L I : Subgroup G} {t i : G}

/-- The linear field is proved; only the embedded A₅ model calculation remains. -/
theorem bounds_of_a5_component_fixer_bound
    (hA5 : A5ComponentFixerBound) (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) : JankoBounds L I :=
  ⟨a5_fixer_of_model hA5 h hG, l3Two_fixer h hG⟩

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Janko
