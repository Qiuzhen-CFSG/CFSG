module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection.Transport
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.SpecificGroups.SU3.FixedFieldTwo

/-!
# The small unitary Borel-model inspections in E.6.22

The PSU₃(2) endpoint is excluded by solvability and quasisimplicity. In
PSU₃(4), an involutory automorphism has a proper fixed subgroup. When it
fixes a Sylow two-subgroup pointwise, the proved concrete rank-one Borel
theorem places that fixed subgroup in the solvable Sylow normalizer.
Consequently it has no ordinary component.

The rank-one theorem supplies its proper-overgroup and solvability facts
from explicit Bruhat and root calculations, including transport of arbitrary
Hermitian forms by actual matrix equivalences. No automorphism coverage,
innerness or full involution-centralizer classification is required.

Source: Aschbacher–Smith, E.6.8(1), printed pp.247–248 (PDF pp.258–259),
and E.6.22, printed p.254 (PDF p.265); the concrete Borel calculation is
F.1.3(1), printed pp.259–260. The parent retains the full Borel assembly.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
/-- The PSU₃(2) endpoint cannot be the quasisimple component in E.6.8. -/
theorem borel_unitary_two_not_quasisimple (hm : ClassicalGroup.IsPSU Y 3 2) :
    ¬ IsQuasisimple Y := by
  intro hY
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hm
  let := hY
  let : IsSimpleGroup (Y ⧸ center Y) := IsQuasisimple.simple
  let : Nontrivial Y := (QuotientGroup.mk'_surjective (center Y)).nontrivial
  let := BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwo.projective_isSolvable
    J hF hconj
  have hs : Group.IsSolvable Y :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.IsPerfect.not_isSolvable Y hs

/-- A Sylow-central involution in PSU₃(4) has solvable fixed subgroup. -/
theorem borel_unitary_four_fixedSubgroup_solvable
    (hm : ClassicalGroup.IsPSU Y 3 4) (a : MulAut Y) (ha : orderOf a = 2)
    (S : Sylow 2 Y) (hfix : ∀ x ∈ (S : Subgroup Y), a x = x) :
    Group.IsSolvable a.fixedSubgroup := by
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hm
  have hB := rankOneSylowFacts_of_equiv S e
    (rankOneSylowFacts_psu3 J 2 (by decide) hF hconj _)
  have hSN : (S : Subgroup Y) ≤ a.fixedSubgroup := by
    intro x hx
    exact (MulAut.mem_fixedSubgroup a x).mpr (hfix x hx)
  have hproper : a.fixedSubgroup < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have ha1 : a = 1 := by
      ext x
      exact (MulAut.mem_fixedSubgroup a x).mp (he ▸ mem_top x)
    simp [ha1] at ha
  have hN := hB.unique_maximal a.fixedSubgroup hSN hproper
  let := hB.solvable
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hN)

/-- Both source endpoints satisfy the exact Sylow-central component inspection. -/
theorem borel_unitary_three_noCentralInvolutionComponent
    {G : Type*} [Group G] [Finite G] (L : Subgroup G) (hL : IsQuasisimple L)
    {n : ℕ} (hn : 1 ≤ n) (hn2 : n ≤ 2)
    (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) :
    NoCentralInvolutionComponent L := by
  have hcases : n = 1 ∨ n = 2 := by omega
  rcases hcases with rfl | rfl
  · exact (borel_unitary_two_not_quasisimple (by simpa using hm) hL).elim
  · apply noCentralInvolutionComponent_of_fixedSubgroup (MulEquiv.refl L)
    intro a ha S hS D
    let := borel_unitary_four_fixedSubgroup_solvable (by simpa using hm) a ha S hS
    exact not_isComponent_of_solvable D

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
