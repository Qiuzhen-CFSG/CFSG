module
public import CFSG.Quasithin.Chapter13.Section04.SolvableCentralizerRecognition
public import BenderSuzuki.ZD.FusionCriterion
public import Theory.SpecificGroups.SymplecticSix.Simplicity

/-!
# Closing the literal generated subgroup in 13.4.9

The generated subgroup E=M∨C_G(z)∨H0 is recognized from the original
D1--D5 system. Its faithful Sp6(2) identification supplies nonsolvability.
The original Sylow subgroup lies in M, and the distinguished involution d
has its full centralizer in M. Consequently the source involution-fusion
and commuting-product centralizer calculations force E=G by the genuine
product-disconnected theorem ZD. The concluding ambient isomorphism uses
exactly the same generated subgroup and C3 recognition map.

The construction of the D-system from13.4.7--8 and the concrete fusion and
product-centralizer calculations remain explicit earlier obligations. This
module proves the terminal implication, not the full source proposition.
Source: Aschbacher--Smith13.4.9, printed pp.906--907.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section04.SolvableCentralizerC3
open Subgroup Quasithin.I5 Theory.SpecificGroups.SymplecticSix

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The original recognized subgroup cannot be a solvable Borel subgroup. -/
theorem generated_not_solvable (M H₀ : Subgroup G) (z : G)
    (S : DSystem .C3 (generated M z H₀)) : ¬ Group.IsSolvable (generated M z H₀) := by
  intro hsolv
  let := hsolv
  let e := generated_equiv_sp6_of_DSystem M H₀ z S
  let : Group.IsPerfect (Sp (ZMod 2)) := perfect_binary
  let : Nontrivial (Sp (ZMod 2)) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [card_sp_of_card_two (by simp)]
    decide)
  have hh : Group.IsSolvable (Sp (ZMod 2)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact Group.IsPerfect.not_isSolvable (Sp (ZMod 2)) hh

/-- The final source generation equality follows from its literal fusion and
centralizer calculations, without an E=G or a ZD callback. -/
theorem generated_eq_top_of_fusion (M H₀ : Subgroup G) (z d : G)
    (S : DSystem .C3 (generated M z H₀)) (T : Sylow 2 G)
    (hs : IsSimpleGroup G) (hna : ¬ IsMulCommutative G)
    (hTM : (T : Subgroup G) ≤ M) (hd : BenderSuzuki.PFAppendixIII.IsInvolution d) (hdM : d ∈ M)
    (hc : centralizer ({d} : Set G) ≤ M)
    (hf : ∀ a ∈ generated M z H₀, ∀ b ∈ generated M z H₀,
      BenderSuzuki.PFAppendixIII.IsInvolution a → IsConj a b → ∃ c ∈ generated M z H₀, MulAut.conj c a = b)
    (hp : ∀ e ∈ generated M z H₀, IsConj d e → Commute d e → e ≠ d →
      centralizer ({d*e} : Set G) ≤ generated M z H₀) : generated M z H₀ = ⊤ := by
  have hME := first_le_generated M z H₀
  exact BenderSuzuki.ZD.eq_top_of_involution_fusion _ T hs hna
    (generated_not_solvable M H₀ z S) (hTM.trans hME) d hd (hME hdM) hf (hc.trans hME) hp

/-- The terminal ambient recognition retains the original marked generated
subgroup and discharges its equality-to-top premise. -/
def ambient_equiv_sp6_of_fusion (M H₀ : Subgroup G) (z d : G)
    (S : DSystem .C3 (generated M z H₀)) (T : Sylow 2 G)
    (hs : IsSimpleGroup G) (hna : ¬ IsMulCommutative G)
    (hTM : (T : Subgroup G) ≤ M) (hd : BenderSuzuki.PFAppendixIII.IsInvolution d) (hdM : d ∈ M)
    (hc : centralizer ({d} : Set G) ≤ M)
    (hf : ∀ a ∈ generated M z H₀, ∀ b ∈ generated M z H₀,
      BenderSuzuki.PFAppendixIII.IsInvolution a → IsConj a b → ∃ c ∈ generated M z H₀, MulAut.conj c a = b)
    (hp : ∀ e ∈ generated M z H₀, IsConj d e → Commute d e → e ≠ d →
      centralizer ({d*e} : Set G) ≤ generated M z H₀) : G ≃* Sp (ZMod 2) :=
  ambient_equiv_sp6_of_generated_eq_top M H₀ z S
    (generated_eq_top_of_fusion M H₀ z d S T hs hna hTM hd hdM hc hf hp)

end CFSG.Quasithin.Chapter13.Section04.SolvableCentralizerC3
