module

public import CFSG.Quasithin.RegularCyclicNormalClosure.FactorConstruction.LocalExceptional
public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.ComplementExclusion

/-!
# Conditional local construction from GLS Step 2

The exact Step 2 disjunction is taken explicitly. The original ambient
input excludes the singleton, swapped and complement alternatives. In the
transitive alternative, direct local oddness and the published odd terminal
produce the actual order-twenty-one candidate inside the normal closure.

The candidate still lacks global compatibility of distinct conjugate
factors. Neither theorem is the unconditional full FactorSeed existence
statement. GLS Step 2 is owned by the existing OrbitGeometry development;
its premise must be discharged by that theorem when published. The odd-order
source dependency remains above Theory, without promoting its standalone
closure or an unconditional lower-Theory factor theorem.

Sources: GLS Number 2 C.14.2, Steps 1–2 and the terminal argument, printed
pp.85–89; Aschbacher–Smith E.6.24, printed p.255.
-/

public section

open Module Subgroup Representation Representation.BinaryOffender
open Representation.RegularCyclicNormalClosure
open Representation.RegularCyclicNormalClosure.FactorConstruction
open Representation.GoldschmidtONan (SingletonCase SwappedCase ComplementCase TransitiveGeometry)
namespace CFSG.Quasithin.RegularCyclicNormalClosure
variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- Conditional assembly of the exact four-way GLS Step 2 result for the
local quotient. The first three alternatives are excluded from the original
ambient input, and the odd terminal handles the transitive alternative. -/
theorem exceptionalCandidate_of_stepTwo (h : Input ρ C)
    (a : A) (hnc : ¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d)
    (F : Submodule (ZMod 2) W)
    (hF : F = fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a))
    (hmax : ∀ b : A, (fixedSpace ρ C).map (ρ b) ≠ fixedSpace ρ C →
      finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ b)) ≤ finrank (ZMod 2) F)
    (hlocal : Representation.GoldschmidtONan.Input (quotientOnFixer ρ F)
      (C.subgroupOf (pointwiseFixer ρ F)))
    (hcases : SingletonCase (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) ∨
      SwappedCase (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) ∨
      ComplementCase (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) ∨
      TransitiveGeometry (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F))) :
    ExceptionalCandidate ρ C (pointwiseFixer ρ F) := by
  have hFU : F ≤ fixedSpace ρ C := hF.le.trans inf_le_left
  have hDK : C.map (MulAut.conj a).toMonoidHom ≤ pointwiseFixer ρ F := by
    apply (le_pointwiseFixer_iff ρ _ F).mpr
    rw [fixedSpace_map_conj]
    exact hF.le.trans inf_le_right
  rcases hcases with hs | hs | hs | hs
  · exact (h.not_singleton_onFixer a hnc F hFU hDK hs).elim
  · exact (h.not_swapped_onFixer a hnc F hFU hDK hlocal hs).elim
  · have hsmall : finrank (ZMod 2) (fixedSpace ρ C) ≤ finrank (ZMod 2) F +
        finrank (ZMod 2) (displacementSpan ρ C ⊤) := by
      have hb := h.le_fixed_inf_finrank a
      rw [← hF] at hb
      have hd := Submodule.finrank_add_eq_of_isCompl h.split
      omega
    exact (h.not_complement_onFixer F hFU hsmall hmax hlocal hs).elim
  · exact exceptionalCandidate_of_transitiveGeometry h a hnc F hF hmax hs

/-- The noncommuting branch has an actual exceptional local candidate,
conditional only on GLS Step 2 for its actual maximal-intersection quotients.
This conclusion does not include the remaining global cross-fixation. -/
theorem exists_exceptionalCandidate_of_stepTwo (h : Input ρ C)
    (hex : ∃ a : A, ¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d)
    (hstep : ∀ a : A,
      let F := fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a)
      Representation.GoldschmidtONan.Input (quotientOnFixer ρ F)
          (C.subgroupOf (pointwiseFixer ρ F)) →
        SingletonCase (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) ∨
        SwappedCase (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) ∨
        ComplementCase (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) ∨
        TransitiveGeometry (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F))) :
    ∃ B : Subgroup A, ExceptionalCandidate ρ C B := by
  obtain ⟨a, hnc, hmax, hlocal, _, _⟩ := h.exists_local_quotient hex
  exact ⟨_, exceptionalCandidate_of_stepTwo h a hnc _ rfl hmax hlocal (hstep a hlocal)⟩

end CFSG.Quasithin.RegularCyclicNormalClosure
