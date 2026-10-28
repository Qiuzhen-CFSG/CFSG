module
public import CFSG.Quasithin.Chapter3.Section02.SourceLocalInput
public import CFSG.Quasithin.ChapterD.Section03.SeedFitting

/-!
# The original FSU seed-stabilizer action

For either original internal actor alternative, the subgroup X T and
its actual reduced seed satisfy D.3.2. The seed-stabilizer theorem
identifies F* of its original faithful image with the actual X image,
including the semisimple or odd-prime structure. No seed-action Fitting
identity remains an additional input to the later source application.

Source: Aschbacher–Smith, D.3.4(5) and the FSU3.2.2 setup,
combined manuscript of 1 March 2004, pp.194 and 579.
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

theorem source_reduced_seed_local_seed_fitting :
    let ρ := ReducedNormal.representation (X ⊔ (T : Subgroup G))
    generalizedFitting (subspaceActionImage ρ I) =
        restrictedSubgroup ρ I (X.subgroupOf (X ⊔ (T : Subgroup G))) ∧
      (componentLayer (restrictedSubgroup ρ I (X.subgroupOf (X ⊔ (T : Subgroup G)))) = ⊤ ∨
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p
          (restrictedSubgroup ρ I (X.subgroupOf (X ⊔ (T : Subgroup G))))) := by
  have hi := source_reduced_seed_local_internal T X M hXM hTM hG hM hX hc I hI
  apply hi.seed_fitting_structure
  change X.subgroupOf (X ⊔ (T : Subgroup G)) ⊔
    (T : Subgroup G).subgroupOf (X ⊔ (T : Subgroup G)) = ⊤
  rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]

end CFSG.Quasithin.Chapter3.Section02
