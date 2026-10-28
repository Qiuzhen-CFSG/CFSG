module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.NormalizerAction
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Assembly

/-!
# The L₃ commutator consumer with its normalizer action discharged

The full-normalizer input to the numerical bound and symmetric-plane argument
now follows from the structural and marked-module implications of 12.2.2.
The hyperplane-centralizer and noncommuting-conjugate inputs remain explicit,
as do those two earlier implications. Their final discharge belongs to the
original 12.4.2 assembly; no fusion theorem is used here.

Source: Aschbacher–Smith, 12.4.1 and the final proof of 12.4.2, printed pp.812,816.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
open Section02 SmallFusion
universe u

/-- Supply the proved full-normalizer action to both the local parameter
bound and the literal symmetric commutator-plane construction. -/
theorem source_commutator_plane_of_remaining_sources
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (centralizers : HyperplaneCentralizers1248.{u})
    (conjugate : NoncommutingConjugate1241.{u})
    {G : Type u} [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ∃ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ∧
      fixedSubgroup L V ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g).toMonoidHom =
        ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ :=
  source_commutator_plane structural marked
    (normalizerAction_of_structural_marked structural marked) centralizers conjugate
    T L V h D hmodel hne

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
