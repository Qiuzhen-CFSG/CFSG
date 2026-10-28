module

public import CFSG.Quasithin.Chapter3.Section02.SourceLocalConsequences
public import CFSG.Quasithin.ChapterD.Section03.SourceFitting

/-!
# Generalized Fitting structure on the original local FSU module

The original reduced seed supplies the internal source hypotheses in XT.
Its full local orbit is the original T-orbit V by SourceLocalConsequences.
The faithful conjugation action on this orbit therefore has generalized
Fitting subgroup equal to the actual image of X. Both original structural
alternatives are retained, including the semisimple or odd-prime conclusion.

Source: Aschbacher–Smith, Lemmas D.3.4(5) and 3.2.2(8),
combined manuscript of 1 March 2004, printed pp.194 and 579.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  (T : Sylow 2 G) (X M : Subgroup G) (hXM : X ≤ M) (hTM : (T : Subgroup G) ≤ M)
  [(X.subgroupOf M).Normal]
  (hG : IsSimpleQTKE K G) (hM : IsMaximalTwoLocal M)
  (hX : pResidual 2 (X.subgroupOf M) = ⊤)
  (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
    le_normalizer_of_normal)
  (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G)))))
  (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
    (X.subgroupOf (X ⊔ (T : Subgroup G))) I)

local notation "V₀" => ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I
local notation "V_T" => componentOrbit V₀ (T : Subgroup G)

include hXM hTM hG hM hX hc hI

theorem source_reduced_seed_local_fitting :
    let ρ := ReducedNormal.representation (X ⊔ (T : Subgroup G))
    let W := orbitSpan ρ ⊤ I
    generalizedFitting (subspaceActionImage ρ W) =
        restrictedSubgroup ρ W (X.subgroupOf (X ⊔ (T : Subgroup G))) ∧
      (componentLayer (restrictedSubgroup ρ W (X.subgroupOf (X ⊔ (T : Subgroup G)))) = ⊤ ∨
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p
          (restrictedSubgroup ρ W (X.subgroupOf (X ⊔ (T : Subgroup G))))) := by
  have hi := source_reduced_seed_local_internal T X M hXM hTM hG hM hX hc I hI
  apply hi.faithfulOrbit_fitting_structure
  change X.subgroupOf (X ⊔ (T : Subgroup G)) ⊔
    (T : Subgroup G).subgroupOf (X ⊔ (T : Subgroup G)) = ⊤
  rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]

end CFSG.Quasithin.Chapter3.Section02
