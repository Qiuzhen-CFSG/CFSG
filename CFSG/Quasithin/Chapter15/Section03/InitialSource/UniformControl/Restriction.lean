module
public import CFSG.Quasithin.Chapter15.Section03.Constructions
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan

/-!
# Restricting the original central seed closure to a Sylow overgroup

The intrinsic Ω₁Z(T|M) is the restriction of the ambient central seed.
Normal closure inside M is therefore the original M-conjugate span,
restricted to M. This supplies the exact quotient denominator for the
fixed-pair C.1.28 application in Aschbacher--Smith14.1.11, p.978.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
variable {G : Type*} [Group G]

theorem omegaClosure_eq_localModule (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) :
    normalClosure (omegaOneCenterAmbient (T.subtype hTM : Subgroup M) : Set M) =
      (localModule T M).subgroupOf M := by
  have hz : omegaOneCenterAmbient (T.subtype hTM : Subgroup M) =
      (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [←omegaOneCenterAmbient_map_injective M.subtype M.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]
    exact (map_subgroupOf_eq_of_le (show omegaOneCenterAmbient (T : Subgroup G) ≤ M from
      fun _ hx => hTM ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)).symm
  rw [hz,normalClosure_subgroupOf_eq_conjugateSpanBy _ M
    (show omegaOneCenterAmbient (T : Subgroup G) ≤ M from
      fun _ hx => hTM ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)]
  rfl

end CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
