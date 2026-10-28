module

public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Faithfulness detected on the generalized Fitting subgroup

The kernel of a homomorphism is normal. If its intersection with F*(G) is
trivial, its commutator with F*(G) vanishes. Self-centralization places the
kernel in F*(G), so it is trivial. The target need only be a monoid, allowing
application directly to linear representations.

Source: the generalized-Fitting self-centralizer theorem, Aschbacher,
*Finite Group Theory*, 31.13; applied to the natural quotient in
Aschbacher–Smith C.1.17, printed p.126.
-/

public section

namespace Theory.GroupTheory
open Subgroup
variable {G M : Type*} [Group G] [Finite G] [Monoid M]
/-- Injectivity on F*(G) implies injectivity on the whole finite group. -/
theorem injective_of_injective_on_generalizedFitting (f : G →* M)
    (hi : Function.Injective (f.comp (generalizedFitting G).subtype)) :
    Function.Injective f := by
  have hinf : f.ker ⊓ generalizedFitting G = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have he : (⟨x,hx.2⟩ : generalizedFitting G) = 1 :=
      hi (by change f x = f 1; rw [map_one]; exact hx.1)
    exact congrArg Subtype.val he
  have hc : ⁅f.ker,generalizedFitting G⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_le_inf _ _).trans hinf.le)
  have hk : f.ker ≤ generalizedFitting G :=
    (commutator_eq_bot_iff_le_centralizer.mp hc).trans (centralizer_generalizedFitting_le G)
  apply f.ker_eq_bot_iff.mp
  exact le_bot_iff.mp ((le_inf le_rfl hk).trans hinf.le)
end Theory.GroupTheory
