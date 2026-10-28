module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs.ParabolicCore

/-!
# The exceptional critical pair and its marked parabolic placement

The no-transvection consequence of the full coordinates on W = [U,K*]
selects a genuine critical pair using 13.8.8(2). The component-generation
argument of 13.8.18(4) gives rank(Vγ*) > 1, and 13.8.4(6) gives quadraticity
on the original U = U_H/V₁. These conclusions and the actual H-conjugator
are retained together in `SelectedWitness`.

The covered local geometry identifies O₂(L₁*T*) with T* ∩ K*. Combining
this calculation with the selected endpoint placement supplies Vα* ≤ T₀*,
where T₀ is literally T ∩ K. The star-intersection identity retains the
kernel O₂(H) ≤ T. No equality W = U or separate faithfulness on W is used.

`exists_critical_witness` constructs the witness family needed by
`FiveReconstruction.tensor_branch_impossible_on_moved`. Its rank input is
`w.rank_gt_one`, its quadratic input is `w.quadratic`, and its conjugation
identity is the definition of `w.alpha`. The final external-X contradiction
remains with the external FF assembly. Only the enumerated earlier F.9 and
§13.5/13.7 implications in `EarlierInputs` remain explicit here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.8.20(a), printed pp.954–955, using 13.8.4(6), 13.8.8(2),
13.8.18(4), and the marked local notation 13.2.1, printed p.877.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs
open CriticalGeometry Components.Swapped.LinearTwo FFSections
open LinearThree.Geometry.CoveredProduct.ResidualPlacement

universe u
variable {G : Type u} [Group G] [Finite G]
  (H K X L V V₃ V₁ M : Subgroup G) (T : Sylow 2 G)
  [(K.subgroupOf H).Normal]
  [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (P : Sylow 2 (Source.Hstar H)) {𝒦 : GroupClass.{u}}
  (f : SourceOrbit.F918Hypotheses H K L (one L (T : Subgroup G) V₁)
    (T : Subgroup G) V V₃ V₁ ρ P 𝒦)
  (S : Sylow 2 (Source.starImage H K))
  (d : LocalData H K X L (T : Subgroup G) V V₃ V₁ M f.component_le S)

include f d in
/-- Construct one source critical pair with rank greater than one, quadratic
action on the original U, and its actual H-conjugate placed in T₀* ≤ K*.
The output identifies T₀* both as T* ∩ K* and as O₂(L₁*T*). -/
theorem exists_critical_witness
    (ha : ExternalXAlternative H K X) (hVH : V ≤ H)
    (initial : CriticalPair L (T : Subgroup G) H V)
    (e : EarlierInputs L (T : Subgroup G) H V V₃ V₁ ρ)
    (s : Equiv.Perm (Fin 3) →* Source.Hstar H) (W : Subrepresentation ρ)
    (hW : W.toSubmodule = subspaceCommutator ρ ⊤ (Source.starImage H K))
    (c : LinearTwo.FiveReconstruction.FullCoordinates W.toRepresentation
      (Source.starImage H K) s)
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X) :
    ∃ w : SelectedWitness L (T : Subgroup G) H V (one L (T : Subgroup G) V₁) V₃ V₁ ρ,
      Source.starImage H w.alpha ≤ Source.starImage H ((T : Subgroup G) ⊓ K) ∧
      Source.starImage H ((T : Subgroup G) ⊓ K) =
        Source.starImage H (T : Subgroup G) ⊓ Source.starImage H K ∧
      Source.starImage H ((T : Subgroup G) ⊓ K) =
        (Source.starImage H (one L (T : Subgroup G) V₁) ⊔
          Source.starImage H (T : Subgroup G)).pCoreIn 2 ∧
      Source.starImage H ((T : Subgroup G) ⊓ K) ≤ Source.starImage H K := by
  obtain ⟨w⟩ := exists_selected_witness H K L (one L (T : Subgroup G) V₁)
    (T : Subgroup G) V V₃ V₁ ρ P f initial hVH e s W hW c
  have hcore := ParabolicCore.twoCore_eq_star_intersection
    H K X L V V₃ V₁ M T ρ P f S d ha hVH s W hW c hmark
  refine ⟨w, ?_, LocalBorel.star_intersection H K (T : Subgroup G) d.sylow,
    hcore.symm, map_mono (subgroupOf_mono H inf_le_right)⟩
  rw [← hcore]
  exact w.alpha_star_le_core (le_sup_left.trans f.setup.local_le)
    (le_sup_right.trans f.setup.local_le)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs

end
