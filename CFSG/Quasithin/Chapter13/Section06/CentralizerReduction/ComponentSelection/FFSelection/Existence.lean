module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.Setup
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.Lifting
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.ComponentProduct
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter

/-!
# Nonemptiness of the literal family Y_z

The complete universal B.5.6 classification, applied to the actual Thompson
image, and the solvable exclusion 13.6.13 give F(J(G_v)*) = Z(J(G_v)*).
Generalized-Fitting self-centralization then selects an ambient component
moved by the nontrivial two-group J(T_v)*. C.1.16(1) normalizes this component,
so its Thompson commutator is the whole component. This direct selection
retains the outer FF alternatives and does not need a component-product
equality. The older conditional component-product route is preserved below.

The lifting theorem constructs a C-component inside G_v, with exactly the
selected component as its star image. The universal A.3.8(3) implication,
via 1.2.1(3), makes its T_v-star orbit normal; perfectness and Thompson
commutator generation put that orbit in the literal X-family. Then 13.6.12
puts it in X_z. Membership in the actual local family L(G_v,T_v) and
quasisimplicity of K*/O₂(K*) give every remaining Y_z clause.

The final theorems take only the earlier local setup, the complete universal
A.3.8(3), A.3.9(1), B.5.6 and C.1.16(1) implications, and the explicit
solvable exclusion. The parent FF-selection task discharges that exclusion
using its independent 13.6.13 branch and retains the earlier-source inputs.
No Fitting equality, component decomposition, selected component or moving
orbit remains as an extra premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the paragraph following 13.6.13, printed p.929.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Construct an actual Y_z witness from the explicit component-product
premise. The classification proof of that premise remains a separate obligation;
A.3.8(3), A.3.9(1), and C.1.16(1) are complete universal earlier-source inputs. -/
theorem exists_mem_Yz_of_component_product {𝒦 : GroupClass.{u}}
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → cComponentLayer X = solvableResidual X)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set X)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel B)
    (hC116 : SourceC116One.{u})
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hlocal : IsSQTK 𝒦 (Gv v))
    (hcore : Gv v ∈ Chapter1.H G)
    (hF : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hstarCore : pCore 2 (Gstar z v) = ⊥)
    (hJne : JGstar z v ≠ ⊥)
    (hproduct : JGstar z v = sSup {E : Subgroup (Gstar z v) |
      IsComponent (Gstar z v) E ∧ E ≤ JGstar z v}) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn (Gv v) ∧
      IsComponent (Gstar z v) (starImage z v K) ∧
      ⁅starImage z v K, starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        starImage z v K ∧ K ∈ Yz L T z v := by
  have hperfect : Group.IsPerfect (JGstar z v) := by
    rw [Subgroup.isPerfect_iff]
    apply le_antisymm (JGstar z v).commutator_le_self
    apply hproduct.le.trans
    apply sSup_le
    rintro E ⟨hE, hEJ⟩
    let : IsQuasisimple E := hE.2
    exact (commutator_eq_self (H := E)).symm.le.trans (commutator_mono hEJ hEJ)
  have hle : JGstar z v ≤ componentLayer (Gstar z v) := by
    apply hproduct.le.trans
    exact sSup_le fun E hE => le_sSup hE.1
  rw [JGstar_eq_conjugateSpan T z v hSyl] at hperfect hle hJne
  let := hperfect
  obtain ⟨E, hE, hEA⟩ := exists_component_commutator_eq_self_of_perfect_span _
    (thompsonStar_normalizes_components hC116 T z v hz hF hSyl hstarCore) hle hJne
  obtain ⟨K, hK, hKE, hKY⟩ := exists_mem_Yz_of_moved_component hA39 hA38
    L T z v hlocal hcore hSyl hstarCore E hE hEA
  refine ⟨K, hK, ?_, ?_, hKY⟩
  · exact hKE.symm ▸ hE
  · rw [hKE]
    exact hEA

/-- The component selected after 13.6.13, from the earlier local setup and
the exact solvable exclusion. The Fitting-center equality is derived from
the complete universal B.5.6 input, and the direct selection discharges the
component and movement premises of the lifting argument. -/
theorem exists_mem_Yz_of_solvable_exclusion {𝒦 : GroupClass.{u}}
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → cComponentLayer X = solvableResidual X)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set X)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel B)
    (hB56 : FFAlternatives.ProjectiveLine.GeneralClassificationInput.{u,u} 𝒦)
    (hC116 : SourceC116One.{u})
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hlocal : IsSQTK 𝒦 (Gv v))
    (hcore : Gv v ∈ Chapter1.H G)
    (hF : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hstarCore : pCore 2 (Gstar z v) = ⊥)
    (hJne : JGstar z v ≠ ⊥)
    (hexclude : ∀ X ∈ XFamily L T z v, ¬ Group.IsSolvable X) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn (Gv v) ∧
      IsComponent (Gstar z v) (starImage z v K) ∧
      ⁅starImage z v K, starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        starImage z v K ∧ K ∈ Yz L T z v := by
  have hfit := FittingCenter.fitting_eq_center hB56 L T z v hz hlocal hSyl
    hstarCore hexclude
  exact exists_mem_Yz_of_JGstar_fitting_eq_center hA39 hA38 hC116 L T z v hz
    hlocal hcore hF hSyl hstarCore hJne hfit

/-- Nonemptiness asserted in the paragraph after 13.6.13. The earlier-source
implications and the independent solvable exclusion retain their full contracts. -/
theorem Yz_nonempty_of_solvable_exclusion {𝒦 : GroupClass.{u}}
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → cComponentLayer X = solvableResidual X)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set X)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel B)
    (hB56 : FFAlternatives.ProjectiveLine.GeneralClassificationInput.{u,u} 𝒦)
    (hC116 : SourceC116One.{u})
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hlocal : IsSQTK 𝒦 (Gv v))
    (hcore : Gv v ∈ Chapter1.H G)
    (hF : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hstarCore : pCore 2 (Gstar z v) = ⊥)
    (hJne : JGstar z v ≠ ⊥)
    (hexclude : ∀ X ∈ XFamily L T z v, ¬ Group.IsSolvable X) :
    (Yz L T z v).Nonempty := by
  obtain ⟨K, _, _, _, hK⟩ := exists_mem_Yz_of_solvable_exclusion
    hA39 hA38 hB56 hC116 L T z v hz hlocal hcore hF hSyl hstarCore hJne hexclude
  exact ⟨K, hK⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
