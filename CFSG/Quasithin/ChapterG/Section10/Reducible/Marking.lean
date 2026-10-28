module
public import CFSG.Quasithin.ChapterG.Section10.Lagrangian
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.DoubleNatural
public import Theory.Representation.BinaryFullLinearRecognition

/-!
# The actual natural-by-dual input to B.4.9 in G.10.4

The faithful full action on the original invariant U supplies its special
linear coordinates. The quotient marking is induced by the original
symplectic pairing. Thus the B.4.9 input retains U and V/U literally.
Source: Aschbacher--Smith G.10.4, printed p.358, case H=G.
-/

@[expose] public section
open Module Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterB.NaturalExtensions
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
  (U : Subrepresentation ρ) [IsIrreducible U.toRepresentation]
  (hU0 : U.toSubmodule ≠ ⊥) (hUt : U.toSubmodule ≠ ⊤)
  (hdim : 3 ≤ finrank (ZMod 2) U.toSubmodule)
include h hU0 hUt hdim

theorem natural_action_of_large_submodule :
    Nonempty (ActionEquiv U.toRepresentation
      (linearNatural BinaryField.two (finrank (ZMod 2) U.toSubmodule))) := by
  let n := finrank (ZMod 2) U.toSubmodule
  let c : U.toSubmodule ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [n])
  obtain ⟨e, _⟩ := h.exists_full_linear_marking_of_large_irreducible_submodule U hU0 hUt hdim
  let f := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U.toSubmodule).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv c).trans
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2)).trans
        (BinaryLinear.OuterCyclic.slEquivLinear n).symm))
  obtain ⟨e', c', he⟩ := BinaryFullLinearRecognition.exists_natural_equiv U.toRepresentation
    (h.faithful_on_large_irreducible_submodule U hU0 hUt hdim) (e.trans f) rfl
  exact ⟨⟨e', c', he⟩⟩

/-- The genuine marked B.4.9 data, with no quadratic or splitting premise. -/
noncomputable def largeDoubleNatural :
    DoubleNatural BinaryField.two (finrank (ZMod 2) U.toSubmodule) ρ where
  faithful := h.faithful
  space := U
  natural := Classical.choice (h.natural_action_of_large_submodule U hU0 hUt hdim)
  quotient := Or.inr ⟨(h.quotient_dual_of_large_irreducible_submodule U hU0 hUt hdim).choose⟩

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
