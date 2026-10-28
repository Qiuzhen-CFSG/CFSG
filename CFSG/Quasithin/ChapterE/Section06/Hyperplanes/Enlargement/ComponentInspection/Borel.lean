module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection.Transport
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection.Borel.Unitary
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import Theory.SpecificGroups.PSL2.SylowFixedSolvable
public import Theory.SpecificGroups.PSL3.SmallSylowFixed

/-!
# The small Borel-model inspections in E.6.22

Every nonidentity automorphism fixing an actual Sylow two-subgroup of a binary
PSL₂ model has solvable fixed group. For PSL₃(2) and PSL₃(4), the fixed group is
conjugate to the full highest-root centralizer, which is a two-group. The
faithful quotient action and a central fixed-group kernel lift solvability to
every perfect central cover of PSL₃(4), including all source two-covers.

The final inspection retains every constructor of `BorelComponentModel`.
Suzuki parameters are arithmetically impossible when n ≤ 2, and PSL₂(2) is
excluded by quasisimplicity and solvability. The unitary calculation excludes
PSU₃(2) in the same way and places the fixed subgroup in a solvable Borel for
PSU₃(4). Transport through actual model equivalences excludes ordinary components
of the fixed subgroup for every order-two Sylow-central action.

Source: Aschbacher--Smith, E.6.8(1), printed pp.247--248 (PDF pp.258--259),
and its use in E.6.22, printed p.254 (PDF p.265).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
open Components
variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
private theorem not_quasisimple_linear_two_two (hY : IsQuasisimple Y)
    (hm : ClassicalGroup.IsPSL Y 2 2) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let := hY
  let : IsSimpleGroup (Y ⧸ center Y) := IsQuasisimple.simple
  let : Nontrivial Y := (QuotientGroup.mk'_surjective (center Y)).nontrivial
  let := Theory.PSL2.OuterSolvable.isSolvable_of_card_two hF
  have hs : Group.IsSolvable Y :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.IsPerfect.not_isSolvable Y hs

/-- The actual binary PSL₂ models satisfy the Sylow-central component exclusion. -/
theorem borel_linear_two_noCentralInvolutionComponent {n : ℕ} (hn : 1 ≤ n)
    (hm : ClassicalGroup.IsPSL Y 2 (2 ^ n)) : NoCentralInvolutionComponent Y := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, show n ≠ 0 by omega])
  let : CharP F 2 := ringChar.of_eq hc
  apply noCentralInvolutionComponent_of_fixedSubgroup e
  intro a ha S hS D
  have hne : a ≠ 1 := by intro he; simp [he] at ha
  let := Theory.PSL2.sylow_fixed_solvable F S a hne hS
  exact not_isComponent_of_solvable D

/-- Both small binary PSL₃ models satisfy the Sylow-central component exclusion. -/
theorem borel_linear_three_noCentralInvolutionComponent {n : ℕ}
    (hn : 1 ≤ n) (hn2 : n ≤ 2) (hm : ClassicalGroup.IsPSL Y 3 (2 ^ n)) :
    NoCentralInvolutionComponent Y := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  apply noCentralInvolutionComponent_of_fixedSubgroup e
  intro a ha S hS D
  have hne : a ≠ 1 := by intro he; simp [he] at ha
  let := Matrix.PSL3.EvenInnerCentralizers.small_sylow_fixed_solvable F hn hn2 hF S a hne hS
  exact not_isComponent_of_solvable D

/-- Every perfect central cover of PSL₃(4) satisfies the inspection. Central
fixed-group kernels suffice, without any fixed-point lifting assumption. -/
theorem borel_linear_three_cover_noCentralInvolutionComponent [Group.IsPerfect Y]
    (hm : ClassicalGroup.IsPSL (Y ⧸ center Y) 3 4) :
    NoCentralInvolutionComponent Y := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  apply noCentralInvolutionComponent_of_fixedSubgroup (MulEquiv.refl Y)
  intro a ha S hS D
  have hmodel (Q : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
      (b : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
      (hb : orderOf b = 2) (hQ : ∀ x ∈ Q, b x = x) :
      Group.IsSolvable b.fixedSubgroup := by
    have hne : b ≠ 1 := by intro he; simp [he] at hb
    exact Matrix.PSL3.EvenInnerCentralizers.small_sylow_fixed_solvable F
      (n := 2) (by decide) (by decide) hF Q b hne hQ
  let := MulAut.fixed_solvable_of_centralQuotient e hmodel S a ha hS
  exact not_isComponent_of_solvable D

/-- Reduction of all source Borel constructors to the unitary inspection. -/
theorem borel_noCentralInvolutionComponent_of_unitary
    {G : Type*} [Group G] [Finite G] (L : Subgroup G) (hL : IsQuasisimple L)
    (hunitary : ∀ n : ℕ, 1 ≤ n → n ≤ 2 → ClassicalGroup.IsPSU L 3 (2 ^ n) →
      NoCentralInvolutionComponent L)
    {n : ℕ} (hn : n ≤ 2) (hm : BorelComponentModel L n) :
    NoCentralInvolutionComponent L := by
  cases hm with
  | linear_two hn0 he =>
    by_cases hn1 : n = 1
    · exact (not_quasisimple_linear_two_two hL (by simpa [hn1] using he)).elim
    · exact borel_linear_two_noCentralInvolutionComponent hn0 he
  | suzuki m hm he _ => omega
  | linear_three hn0 he => exact borel_linear_three_noCentralInvolutionComponent hn0 hn he
  | unitary_three hn0 he => exact hunitary n hn0 hn he
  | linear_three_cover _ _ he =>
    let := hL
    exact borel_linear_three_cover_noCentralInvolutionComponent he

/-- Every quasisimple Borel model with parameter at most two satisfies the
Sylow-central component exclusion used in E.6.22. All five model constructors,
including every central two-cover of PSL₃(4), are retained. -/
theorem borel_noCentralInvolutionComponent
    {G : Type*} [Group G] [Finite G] (L : Subgroup G) (hL : IsQuasisimple L)
    {n : ℕ} (hn : n ≤ 2) (hm : BorelComponentModel L n) :
    NoCentralInvolutionComponent L := by
  exact borel_noCentralInvolutionComponent_of_unitary L hL
    (fun _ hn0 hn2 he => borel_unitary_three_noCentralInvolutionComponent L hL hn0 hn2 he)
    hn hm

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
