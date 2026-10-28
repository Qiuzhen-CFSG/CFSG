module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Models
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The conjugation and outer actions of the terminal star quotient

Write X = H/O₂(H) and L for the actual image of H∞. When F*(X) = L and
Z(L) = 1, generalized-Fitting self-centralization gives C_X(L) = 1.
Thus conjugation X → Aut(L) has trivial kernel, and X → Out(L) has kernel
exactly L. Its restriction to any subgroup disjoint from L is injective.
If |Out(L)| divides twelve, an elementary binary actor therefore has
rank at most two. The parent module discharges the center and order inputs
for all three exact terminal models.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), terminal
paragraph of §13.6, printed p.935. Generalized-Fitting self-centralization
uses the proved Chapter B bridge to Gorenstein–Walter's Bender theorem.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.ModelFacts
open Section08
variable {G : Type*} [Group G] [Finite G]

instance residualImage_normal (H : Subgroup G) :
    (Source.starImage H (terminalResidual H)).Normal := by
  rw [terminalResidual_star]
  infer_instance

noncomputable def residualConjugation (H : Subgroup G) :
    Source.Hstar H →* MulAut (Source.starImage H (terminalResidual H)) := MulAut.conjNormal

noncomputable def residualOuterAction (H : Subgroup G) :
    Source.Hstar H →* MulAut.Outer (Source.starImage H (terminalResidual H)) :=
  (QuotientGroup.mk' (MulAut.innerSubgroup (Source.starImage H (terminalResidual H)))).comp
    (residualConjugation H)

/-- Conjugation on the literal residual image has the usual element formula. -/
theorem residualConjugation_apply (H : Subgroup G) (x : Source.Hstar H)
    (y : Source.starImage H (terminalResidual H)) :
    (residualConjugation H x y : Source.Hstar H) = x * y * x⁻¹ := by
  rfl

/-- The outer action is the class of the actual conjugation automorphism. -/
theorem residualOuterAction_apply (H : Subgroup G) (x : Source.Hstar H) :
    residualOuterAction H x = QuotientGroup.mk (residualConjugation H x) := by
  rfl

theorem residual_centralizer (H : Subgroup G)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H (terminalResidual H))
    (hz : center (Source.starImage H (terminalResidual H)) = ⊥) :
    centralizer (Source.starImage H (terminalResidual H) : Set (Source.Hstar H)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hl : x ∈ Source.starImage H (terminalResidual H) := by
    rw [← hfit] at hx ⊢
    exact CFSG.Quasithin.ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le hx
  have hc : (⟨x, hl⟩ : Source.starImage H (terminalResidual H)) ∈
      center (Source.starImage H (terminalResidual H)) := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
  rw [hz] at hc
  exact congrArg Subtype.val hc

theorem residualConjugation_kernel (H : Subgroup G)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H (terminalResidual H))
    (hz : center (Source.starImage H (terminalResidual H)) = ⊥) :
    (residualConjugation H).ker = ⊥ := by
  rw [residualConjugation, MulAut.conjNormal_ker_eq_centralizer]
  exact residual_centralizer H hfit hz

theorem residualOuterAction_kernel (H : Subgroup G)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H (terminalResidual H))
    (hz : center (Source.starImage H (terminalResidual H)) = ⊥) :
    (residualOuterAction H).ker = Source.starImage H (terminalResidual H) := by
  rw [residualOuterAction, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', residualConjugation,
    MulAut.conjNormal_comap_innerSubgroup, residual_centralizer H hfit hz, sup_bot_eq]

theorem disjoint_outer_injective (H : Subgroup G)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H (terminalResidual H))
    (hz : center (Source.starImage H (terminalResidual H)) = ⊥)
    (A : Subgroup (Source.Hstar H)) (hd : Disjoint A (Source.starImage H (terminalResidual H))) :
    Function.Injective ((residualOuterAction H).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  apply Subtype.ext
  have hx' : x.val ∈ (residualOuterAction H).ker := hx
  rw [residualOuterAction_kernel H hfit hz] at hx'
  exact disjoint_iff_inf_le.mp hd ⟨x.property, hx'⟩

theorem rank_le_two_of_injective_outer (H : Subgroup G)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H (terminalResidual H))
    (hz : center (Source.starImage H (terminalResidual H)) = ⊥)
    (hout : Nat.card (MulAut.Outer (Source.starImage H (terminalResidual H))) ∣ 12)
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (hd : Disjoint A (Source.starImage H (terminalResidual H))) : rank A ≤ 2 := by
  have hh := (card_dvd_of_injective ((residualOuterAction H).comp A.subtype)
    (disjoint_outer_injective H hfit hz A hd)).trans hout
  rw [hA.card_eq_two_pow_rank] at hh
  by_contra hr
  have ht : 3 ≤ rank A := by omega
  have he : 2 ^ 3 ∣ 12 := (pow_dvd_pow 2 ht).trans hh
  norm_num at he

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.ModelFacts
