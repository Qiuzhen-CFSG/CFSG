module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.Sylow
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.Survivors

/-!
# Source-case transport in the actual group LR

The source Sylow is constructed from the given Sylow subgroup of I. Its image
is S ∩ LR, and its radical is the intrinsic copy of R. The complete five-case
classification can then be applied with a genuine local quotient marking.
The conditional assembly retains every surviving clause and transports all
layers to the original component quotient through that same marking.

The final 15.3.23 application is still pending: S-normalization of L and
pointwise fixation of C_Q(L) in case (4) must be established from the earlier
source facts. The assembly below explicitly takes these two obligations;
it does not assert that the Sylow comparison alone proves either of them.

Source: Aschbacher–Smith, 15.3.23, printed p.1128, and C.1.34,
printed pp.136–137.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.SourceCases
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Specialize the full earlier classification using the actual two-core
quotient of the component. The natural/dual marking is chosen by that theorem. -/
theorem all_five_of_classification (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (κ : GroupClass.{u})
    (ms : MSPair κ (c.L ⊔ d.R : Subgroup G)
      (c.L.subgroupOf (c.L ⊔ d.R)) (d.R.subgroupOf (c.L ⊔ d.R)))
    (classification : UniversalClassification.{u})
    (e₀ : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (P : Sylow 2 (c.L ⊔ d.R : Subgroup G))
    (hRP : d.R.subgroupOf (c.L ⊔ d.R) ≤ (P : Subgroup (c.L ⊔ d.R : Subgroup G))) :
    ∃ e : ((c.L.subgroupOf (c.L ⊔ d.R)) ⧸ pCore 2 (c.L.subgroupOf (c.L ⊔ d.R))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Alternatives (ZMod 2) 1 (c.L.subgroupOf (c.L ⊔ d.R))
        (d.R.subgroupOf (c.L ⊔ d.R)) P e := by
  exact classification κ (c.L ⊔ d.R : Subgroup G) _ _ ms (ZMod 2) 1 (by decide)
    (by simp) ⟨(quotientComparison (show c.L ≤ c.L ⊔ d.R from le_sup_left)).trans e₀⟩ P hRP

/-- Conditional assembly on LR. The two ambient action premises are the remaining
source obligations, rather than a local rank bound or a Sylow equality. -/
theorem source_cases_of_ambient_control (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hI : I ∈ d.Hplus)
    (T : Sylow 2 I) (hT : (T : Subgroup I).map I.subtype = d.S)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hRL : d.R ≤ normalizer (c.L : Set G))
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4)
    (hSL : d.S ≤ normalizer (c.L : Set G))
    (hSC : ∀ (P : Sylow 2 (c.L ⊔ d.R : Subgroup G))
      (e : ((c.L.subgroupOf (c.L ⊔ d.R)) ⧸ pCore 2 (c.L.subgroupOf (c.L ⊔ d.R))) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)),
      FourthCase (c.L.subgroupOf (c.L ⊔ d.R)) (d.R.subgroupOf (c.L ⊔ d.R)) P e →
        d.S ≤ centralizer (coreFixed c.L : Set G))
    (hcases : ∀ (P : Sylow 2 (c.L ⊔ d.R : Subgroup G)),
      d.R.subgroupOf (c.L ⊔ d.R) ≤ (P : Subgroup (c.L ⊔ d.R : Subgroup G)) →
      ∃ e : ((c.L.subgroupOf (c.L ⊔ d.R)) ⧸ pCore 2 (c.L.subgroupOf (c.L ⊔ d.R))) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        Alternatives (ZMod 2) 1 (c.L.subgroupOf (c.L ⊔ d.R))
          (d.R.subgroupOf (c.L ⊔ d.R)) P e) :
    ∃ (P : Sylow 2 (c.L ⊔ d.R : Subgroup G)),
      (P : Subgroup (c.L ⊔ d.R : Subgroup G)).map (c.L ⊔ d.R : Subgroup G).subtype =
        d.S ⊓ (c.L ⊔ d.R) ∧
      d.R.subgroupOf (c.L ⊔ d.R) ≤ (P : Subgroup (c.L ⊔ d.R : Subgroup G)) ∧
      ∃ e : ((c.L.subgroupOf (c.L ⊔ d.R)) ⧸ pCore 2 (c.L.subgroupOf (c.L ⊔ d.R))) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        (FirstThreeCases (c.L.subgroupOf (c.L ⊔ d.R)) (d.R.subgroupOf (c.L ⊔ d.R)) P e ∨
          FifthCase (c.L.subgroupOf (c.L ⊔ d.R)) (d.R.subgroupOf (c.L ⊔ d.R)) P e) ∧
        AmbientCases (show c.L ≤ c.L ⊔ d.R from le_sup_left) (d.R.subgroupOf (c.L ⊔ d.R)) P e := by
  obtain ⟨P, _, hRP, hPS⟩ := local_sylow d c T hT hR hRL
  obtain ⟨e, he⟩ := hcases P hRP
  refine ⟨P, hPS, hRP, e, ?_⟩
  exact survivors_of_ambient_control d le_sup_left (component_in_source d c hI)
    (d.R.subgroupOf (c.L ⊔ d.R)) P e hcore hR hindex hZ hZS hSL (hSC P e) he

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.SourceCases
end
