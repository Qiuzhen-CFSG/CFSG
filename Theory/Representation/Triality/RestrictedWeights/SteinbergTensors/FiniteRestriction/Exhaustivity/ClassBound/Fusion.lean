module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Passage
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.Restriction

/-!
# Geometric assembly for odd-order conjugacy descent

The graph-field map restricts regularly to the actual closed centralizer of
each fixed point. Connectedness of an odd-order point's centralizer and Lang
surjectivity for that connected restriction supply the centralizing correction
from `Passage`, hence descent of ambient conjugacy to the fixed group.

The two geometric inputs remain explicit below. This module does not yet
assert unconditional odd-order fusion. The connected-centralizer theorem and
the connected Lang theorem are separate obligations; the latter may be proved
without assuming the former.

Sources: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 8.5, 10.1 and 12.5.
-/

public section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound

open Theory.AlgebraicGroup

universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Assemble the two geometric inputs on the literal centralizer. Connectedness
and Lang surjectivity are needed only for odd-order fixed points. The Lang
theorem can be established independently under a connectedness hypothesis. -/
theorem oddCentralizerLang_of_connected_centralizers_of_lang
    (S : Geometry K) (n : ℕ)
    (hconnected : ∀ x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n,
      ¬ 2 ∣ orderOf x → Variety.IsConnected (fixedCentralizer S n x).carrierVariety)
    (hLang : ∀ x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n,
      ¬ 2 ∣ orderOf x → Variety.IsConnected (fixedCentralizer S n x).carrierVariety →
        Function.Surjective (langMorphism (centralizerRestriction S n x)).toFun) :
    OddCentralizerLang S n := by
  intro x hx a ha
  exact centralizer_lang_solution S n x (hLang x hx (hconnected x hx)) a ha

/-- Connected centralizers and their Lang solutions imply the required fusion
statement, with no elementary-generation or representation-theoretic premise. -/
theorem oddClassFusion_of_connected_centralizers_of_lang
    (S : Geometry K) (n : ℕ)
    (hconnected : ∀ x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n,
      ¬ 2 ∣ orderOf x → Variety.IsConnected (fixedCentralizer S n x).carrierVariety)
    (hLang : ∀ x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n,
      ¬ 2 ∣ orderOf x → Variety.IsConnected (fixedCentralizer S n x).carrierVariety →
        Function.Surjective (langMorphism (centralizerRestriction S n x)).toFun) :
    OddClassFusion S n :=
  oddClassFusion_of_centralizerLang S n
    (oddCentralizerLang_of_connected_centralizers_of_lang S n hconnected hLang)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
