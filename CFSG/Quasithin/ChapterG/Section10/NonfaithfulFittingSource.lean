module
public import Theory.Representation.SmallSymplecticNormalThree
public import CFSG.Quasithin.ChapterG.Section10.FittingSource
public import CFSG.Quasithin.ChapterG.Section10.Reducible.Solvable
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six.SourceCubic
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.OrthogonalOrder
public import Theory.GroupAction.FiveSixteenCentralizer
public import Theory.GroupTheory.CyclicFifteen
public import Theory.Representation.BinaryGroupAction

/-!
# The faithful-Fitting exclusion in the original symplectic context

Assume the G.10 actor acts faithfully on the Fitting subgroup. The proved
G.9 source reductions leave the plane, normal-five, orthogonal-nine, and
normal-cubic cases. The first three are solvable by their actual small
actions. The remaining normal-cubic actions are symplectic of dimension at
most six, so the quadratic census makes them solvable as well. This gives
the contradiction needed in the nonsolvable branch without full G.9.4
normalizer recognition or any assumption about the terminal action kernel.

The public result retains the literal G.10 representation, actor and Fitting
centralizer. Source: Aschbacher--Smith G.9.4 and G.11.5, pp.354--355,365.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

private theorem solvable_of_degree_le_two (hf : Function.Injective ρ)
    (hd : finrank (ZMod 2) V ≤ 2) : Group.IsSolvable G := by
  have hdiv := Representation.card_dvd_card_GL_of_injective ρ hf
  have hd6 : Nat.card G ∣ 6 := by
    apply hdiv.trans
    rw [Matrix.card_GL_field]
    interval_cases hdim : finrank (ZMod 2) V <;> norm_num [Fin.prod_univ_succ]
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hpd
  have hh : p ∣ 2 * 3 := hpd.trans hd6
  exact (hp.dvd_mul.mp hh).elim
    (fun h => Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
    (fun h => Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h))

private theorem solvable_of_normal_five (hf : Function.Injective ρ)
    (hd : finrank (ZMod 2) V = 4) (C : Subgroup G) [C.Normal]
    (hC : Nat.card C = 5) : Group.IsSolvable G := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := Representation.BinaryGroupAction.action ρ
  let : FaithfulSMul G (Multiplicative V) := Representation.BinaryGroupAction.faithful ρ hf
  have hV : Nat.card (Multiplicative V) = 16 := by
    change Nat.card V = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    decide
  let D := centralizer (C : Set G)
  have hD : Nat.card D ∣ 15 := card_centralizer_five_dvd_fifteen (V := Multiplicative V) C hC hV
  have hcases : Nat.card D = 1 ∨ Nat.card D = 3 ∨ Nat.card D = 5 ∨ Nat.card D = 15 := by
    have hh := Nat.mem_divisors.mpr ⟨hD, by decide⟩
    rw [show Nat.divisors 15 = {1,3,5,15} by decide] at hh
    simpa using hh
  let : Group.IsSolvable D := by
    rcases hcases with h1 | h3 | h5 | h15
    · let : Subsingleton D := (Nat.card_eq_one_iff_unique.mp h1).1
      exact Group.isSolvable_of_comm (fun _ _ => Subsingleton.elim _ _)
    · let : IsCyclic D := isCyclic_of_prime_card h3
      exact Group.isSolvable_of_comm (fun _ _ => mul_comm' _ _)
    · let : IsCyclic D := isCyclic_of_prime_card h5
      exact Group.isSolvable_of_comm (fun _ _ => mul_comm' _ _)
    · let : IsCyclic D := isCyclic_of_card_eq_fifteen h15
      exact Group.isSolvable_of_comm (fun _ _ => mul_comm' _ _)
  let : IsCyclic C := isCyclic_of_prime_card hC
  have hAut : Nat.card (MulAut C) = 4 := by rw [IsCyclic.card_mulAut,hC]; decide
  let f : G →* MulAut C := MulAut.conjNormal
  apply D.isSolvable_of_index_le_four
  change (centralizer (C : Set G)).index ≤ 4
  rw [← MulAut.conjNormal_ker_eq_centralizer C,Subgroup.index_ker]
  exact hAut ▸ f.range.card_le_card_group

private theorem orthogonalFour_solvable : Group.IsSolvable Section09.FittingRecognition.OrthogonalFour := by
  have hcard := Section09.FittingRecognition.Four.card_orthogonalFour
  let : Finite Section09.FittingRecognition.OrthogonalFour := Nat.finite_of_card_ne_zero (by omega)
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hpd
  rw [hcard,show 72=2^3*3^2 by decide] at hpd
  exact (hp.dvd_mul.mp hpd).elim
    (fun h => Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)))
    (fun h => Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)))

private theorem solvable_of_cubic_four {K : GroupClass.{u}} {X : Subgroup G} {m : ℕ}
    (d : Section09.FittingHypothesis K ρ X m) (hm : 0 < m)
    (hc : IsPGroup 3 (⁅fittingSubgroup G,X⁆ : Subgroup G))
    (hd : finrank (ZMod 2) V = 4)
    (B : LinearMap.BilinForm (ZMod 2) V) (ha : B.IsAlt) (hn : B.Nondegenerate)
    (hi : ∀ g u v, B (ρ g u) (ρ g v) = B u v) : Group.IsSolvable G := by
  let : Representation.IsIrreducible ρ := d.irreducible
  have data := Section09.FittingRecognition.threeCoreData_from_source d hm hc
  rcases Section09.FittingRecognition.Four.threeCore_card_cases d.toSetup hm data hd with h3 | h9
  · exact SmallSymplecticNormalThree.isSolvable_of_normal_cubic ρ d.faithful B ha hn hi
      (by omega) (pCore 3 G) h3
  · obtain ⟨H,_,e,f,he⟩ := Section09.FittingRecognition.Four.NineNormalizer.core_realization ρ d.faithful hd h9
    let : Group.IsSolvable Section09.FittingRecognition.OrthogonalFour := orthogonalFour_solvable
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

variable {B : LinearMap.BilinForm (ZMod 2) V} {v : V} {W : Submodule (ZMod 2) V}
  {X : Subgroup G} [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- Nonsolvability in the original symplectic G.10 context forces the actor to
have nontrivial centralizer on F(G), the exact conclusion needed in G.11.5. -/
theorem fitting_centralizer_ne_bot_of_not_solvable {K : GroupClass.{u}}
    (cover : Nonempty (Section09.SQTKCover K G)) (hs : ¬ Group.IsSolvable G) :
    X ⊓ centralizer (fittingSubgroup G : Set G) ≠ ⊥ := by
  intro hbot
  let m := finrank (ZMod 2) (Additive X)
  have hirr := h.irreducible_of_not_solvable hs
  let : Representation.IsIrreducible ρ := hirr
  have d : Section09.FittingHypothesis K ρ X m := {
    faithful := h.faithful
    elementary := inferInstance
    card_actor := by
      change Nat.card (Additive X) = _
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    degree_le := by
      have hr := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
        (QuotientGroup.mk'_surjective X₀)).trans (IsElementaryAbelian.rank_le_finrank (p := 2) X)
      exact h.dimension_bound.1.trans (by dsimp [m]; omega)
    quotient := cover
    irreducible := hirr
    faithful_fitting := hbot }
  have hm : 0 < m := by
    by_contra hm
    have hdeg := d.degree_le
    exact hs (solvable_of_degree_le_two h.faithful (by omega))
  by_cases hc : IsPGroup 3 (⁅fittingSubgroup G,X⁆ : Subgroup G)
  · rcases Section09.FittingRecognition.source_cubic_degree_cases d hm hc with
      hone | ⟨h1,h4⟩ | ⟨h2,h4⟩ | ⟨h2,h6⟩
    · exact hs (solvable_of_degree_le_two h.faithful (by rw [hone.2.1]))
    · exact hs (solvable_of_cubic_four d hm hc h4 B h.alternating h.nondegenerate h.preserves)
    · exact hs (solvable_of_cubic_four d hm hc h4 B h.alternating h.nondegenerate h.preserves)
    · have d2 : Section09.FittingHypothesis K ρ X 2 := h2 ▸ d
      obtain ⟨C,hCn,hCc⟩ := Section09.FittingRecognition.Six.normal_cubic_of_source_degree_six d2 hc h6
      let : C.Normal := hCn
      exact hs (SmallSymplecticNormalThree.isSolvable_of_normal_cubic ρ h.faithful B h.alternating
        h.nondegenerate h.preserves (by omega) C hCc)
  · have ht := Section09.FittingRecognition.caseTwo_from_source d hm hc
    have hne := Section09.FittingRecognition.FiveCore.fiveCore_ne_bot d
      (Section09.FittingRecognition.nilpotentRigidityInput ρ) hc
    have hcard := Section09.FittingRecognition.FiveCore.fiveCore_card h.faithful ht.2.1 hne
    exact hs (solvable_of_normal_five h.faithful ht.2.1 (pCore 5 G) hcard)
end CFSG.Quasithin.ChapterG.Section10.Hypothesis
