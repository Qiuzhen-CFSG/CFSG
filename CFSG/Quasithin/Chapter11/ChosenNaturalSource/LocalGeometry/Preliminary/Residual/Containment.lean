module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual

/-!
# The original normalizer p-subgroups lie in the chosen component

Apply 11.0.4 to elements of an actual subgroup of N_G(L). Every p-element
belongs to the prime-to-p residual, so the residual equality places the
whole subgroup in L. The cubic Sp₄/G₂ specializations retain the supplied
natural-action markings. These are the containment forms used in the
local subgroup analysis of 11.1--11.2, printed pp.760--766.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Source-prime subgroups of the literal normalizer lie in the original L. -/
theorem pSubgroup_le_component {p : ℕ} (hp : p.Prime) (hc : SourcePrime D S p)
    (P : Subgroup G) (hP : IsPGroup p P) (hPM : P ≤ normalizer (L : Set G)) : P ≤ L := by
  intro x hx
  obtain ⟨k,hk⟩ := hP.exists_pow_pow_eq_one (⟨x,hx⟩ : P)
  exact primePower_mem_component D S hp hc (hPM hx) (congrArg Subtype.val hk)

/-- The full symplectic cubic conclusion includes nonsplit cubic tori. -/
theorem sp4_threeSubgroup_le_component
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (P : Subgroup G) (hP : IsPGroup 3 P) (hPM : P ≤ normalizer (L : Set G)) : P ≤ L := by
  intro x hx
  obtain ⟨k,hk⟩ := hP.exists_pow_pow_eq_one (⟨x,hx⟩ : P)
  rw [sp4_cubic_residual D S m]
  refine ⟨⟨x,hPM hx⟩,mem_primeToResidual_of_pow (n := k) ?_,rfl⟩
  exact Subtype.ext (congrArg (fun y : P => (y : G)) hk)

/-- The cubic containment in the original G₂ normalizer. -/
theorem g2_threeSubgroup_le_component
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (P : Subgroup G) (hP : IsPGroup 3 P) (hPM : P ≤ normalizer (L : Set G)) : P ≤ L := by
  intro x hx
  obtain ⟨k,hk⟩ := hP.exists_pow_pow_eq_one (⟨x,hx⟩ : P)
  rw [g2_cubic_residual D S m]
  refine ⟨⟨x,hPM hx⟩,mem_primeToResidual_of_pow (n := k) ?_,rfl⟩
  exact Subtype.ext (congrArg (fun y : P => (y : G)) hk)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
