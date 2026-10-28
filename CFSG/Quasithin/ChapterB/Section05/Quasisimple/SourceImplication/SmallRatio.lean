module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Statement
public import Mathlib.Data.ENNReal.Real

/-!
# The small-ratio rows of the complete B.4.2 list

Inspection of the full action list at ratio at most one half leaves the
natural SL₃ modules and the binary natural modules of degrees four and five.
Every row has ratio at least one quarter. The universal earlier-source input
retains the full finite SQTK hypotheses and the complete offender/action
conclusions; it does not classify a reducible B.5.1 module by assumption.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2, printed
p.86, and the reduction (**) in B.5.1, printed p.100. The B.5.1 owner must
still prove the irreducibility of its chosen constituent before this applies.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped ENNReal
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem IrreducibleActionCase.natural_of_ratio_le_half {L H : Subgroup G}
    (h : IrreducibleActionCase ρ L H) (hq : quadraticRatio ρ ≤ 1 / 2) :
    (∃ F : BinaryField, IsLinearNatural (ρ.comp L.subtype) F 3) ∨
    ∃ d, (d = 4 ∨ d = 5) ∧ IsLinearNatural (ρ.comp L.subtype) BinaryField.two d := by
  cases h with
  | linearThree F _ e _ => exact Or.inl ⟨F, ⟨e⟩⟩
  | binaryLinear d hd _ e _ => exact Or.inr ⟨d, hd, ⟨e⟩⟩
  | linearTwo _ _ _ _ he => rw [he] at hq; norm_num at hq
  | symplectic _ _ _ _ he =>
    have hr := ENNReal.toReal_mono (by norm_num) hq
    rw [he] at hr
    norm_num [ENNReal.toReal_div] at hr
  | symplecticTwo _ he =>
    have hr := ENNReal.toReal_mono (by norm_num) hq
    rw [he] at hr
    norm_num [ENNReal.toReal_div] at hr
  | g2 _ _ _ _ _ he => rw [he] at hq; norm_num at hq
  | g2Two _ _ he => rw [he] at hq; norm_num at hq
  | symmetric _ _ _ _ he => rw [he] at hq; norm_num at hq
  | alternatingSix _ _ _ he => rw [he] at hq; norm_num at hq
  | alternatingSeven _ _ _ _ _ he => rw [he] at hq; norm_num at hq
  | tripleSix _ _ he => rw [he] at hq; norm_num at hq
  | orthogonalSix _ _ _ _ he => rw [he] at hq; norm_num at hq
  | symmetricEight _ _ he =>
    have hr := ENNReal.toReal_mono (by norm_num) hq
    rw [he] at hr
    norm_num [ENNReal.toReal_div] at hr
  | exteriorFive _ _ _ _ _ he => rw [he] at hq; norm_num at hq

/-- The whole irreducible catalogue has a uniform lower bound. -/
theorem IrreducibleActionCase.quarter_le_ratio {L H : Subgroup G}
    (h : IrreducibleActionCase ρ L H) : 1 / 4 ≤ quadraticRatio ρ := by
  cases h with
  | binaryLinear d hd _ _ he =>
    rcases hd with rfl | rfl <;> rw [he] <;> norm_num
  | linearThree _ _ _ he => rw [he]; norm_num
  | linearTwo _ _ _ _ he => rw [he]; norm_num
  | symplectic _ _ _ _ he =>
    rw [he]
    apply (ENNReal.toReal_le_toReal (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
    norm_num [ENNReal.toReal_div]
  | symplecticTwo _ he =>
    rw [he]
    apply (ENNReal.toReal_le_toReal (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
    norm_num [ENNReal.toReal_div]
  | g2 _ _ _ _ _ he => rw [he]; norm_num
  | g2Two _ _ he => rw [he]; norm_num
  | symmetric _ _ _ _ he => rw [he]; norm_num
  | alternatingSix _ _ _ he => rw [he]; norm_num
  | alternatingSeven _ _ _ _ _ he => rw [he]; norm_num
  | tripleSix _ _ he => rw [he]; norm_num
  | orthogonalSix _ _ _ _ he => rw [he]; norm_num
  | symmetricEight _ _ he =>
    rw [he]
    apply (ENNReal.toReal_le_toReal (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
    norm_num [ENNReal.toReal_div]
  | exteriorFive _ _ _ _ _ he => rw [he]; norm_num

/-- The complete earlier B.4.2 implication, not a hypothesis about a B.5.1 module.
The class K must be instantiated by the source owner, along with this universal
classification implication. Every offender clause is retained in the output. -/
def IrreducibleClassificationInput (K : CFSG.Quasithin.GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (V : Type v) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V),
    CFSG.Quasithin.IsSQTK K G →
    Theory.GroupTheory.IsQuasisimple (Theory.GroupTheory.generalizedFitting G) →
    Function.Injective ρ →
    IsIrreducible (ρ.comp (Theory.GroupTheory.generalizedFitting G).subtype) →
    (∃ A, IsBestOffender ρ A) →
    IrreducibleActionCase ρ (Theory.GroupTheory.generalizedFitting G) (offenderSubgroup ρ)

/-- Instantiate the complete earlier source theorem to obtain the natural
rows forced by the half-ratio bound. No B.5.1 classification is assumed. -/
theorem natural_of_irreducible_small_ratio [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : CFSG.Quasithin.GroupClass.{u}} (earlier : IrreducibleClassificationInput.{u, v} K)
    (hsqtk : CFSG.Quasithin.IsSQTK K G)
    (hL : Theory.GroupTheory.IsQuasisimple (Theory.GroupTheory.generalizedFitting G))
    (hfaith : Function.Injective ρ)
    (hirr : IsIrreducible (ρ.comp (Theory.GroupTheory.generalizedFitting G).subtype))
    (hbest : ∃ A, IsBestOffender ρ A) (hq : quadraticRatio ρ ≤ 1 / 2) :
    (∃ F : BinaryField, IsLinearNatural
      (ρ.comp (Theory.GroupTheory.generalizedFitting G).subtype) F 3) ∨
    ∃ d, (d = 4 ∨ d = 5) ∧ IsLinearNatural
      (ρ.comp (Theory.GroupTheory.generalizedFitting G).subtype) BinaryField.two d := by
  exact (earlier G V ρ hsqtk hL hfaith hirr hbest).natural_of_ratio_le_half ρ hq

end CFSG.Quasithin.ChapterB.QuasisimpleSource
