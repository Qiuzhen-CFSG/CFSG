module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.Parameters

/-!
# The actual degree-three cover and parameter step in the F.6 consumer

The source component's central-quotient model and Sylow bound construct the
literal special/projective model used by rows (10) and (11). When that
component is the whole group, the original local extension maps assemble
row (10). All multiplier and prime-congruence premises are discharged.
The distinct catalogue, Sylow-sign and marked-local recognition steps
remain explicit for the F.6 source assembly owner.

Source: Aschbacher--Smith F.6.18(10)--(11), printed pp.309--310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H F : Type u} [Group G] [Finite G] [Group H] [Finite H]
    [Field F] [Finite F] {K : Subgroup G}

/-- Transport retains the actual special/projective carrier and field. -/
theorem DegreeThree.of_mulEquiv {p : ℕ} {D E : Type u} [Group D] [Group E]
    (h : DegreeThree p D) (e : E ≃* D) : DegreeThree p E := by
  cases h with
  | linear F hc hs j => exact .linear F hc hs (e.trans j)
  | projectiveLinear F hc hs j => exact .projectiveLinear F hc hs (e.trans j)
  | unitary F J hc hj hs j => exact .unitary F J hc hj hs (e.trans j)
  | projectiveUnitary F J hc hj hs j => exact .projectiveUnitary F J hc hj hs (e.trans j)

/-- The source linear component supplies the literal consumer model. -/
theorem degreeThree_linear_of_source_component
    (hK : IsComponent G K) (T : Sylow 2 G) (hT : Nat.card T ≤ 64)
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card F = p) (hsign : p % 4 = 1)
    (eK : K ⧸ center K ≃* PSL(3,F)) :
    p % 8 = 5 ∧ DegreeThree p K := by
  obtain ⟨hm, hj⟩ := component_linear_three_small_sylow_models hK T hT hp hcard hsign eK
  refine ⟨hm, ?_⟩
  rcases hj with hj | hj
  · exact .linear F hcard hsign (Classical.choice hj)
  · exact .projectiveLinear F hcard hsign (Classical.choice hj)

/-- The source unitary component supplies the literal consumer model,
including the original form and Frobenius involution. -/
theorem degreeThree_unitary_of_source_component
    (eG : G ≃* (H ⧸ pPrimeCore 3 H)) (hK : IsComponent G K)
    (T : Sylow 2 G) (hT : Nat.card T ≤ 64)
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (hsign : p % 4 = 3)
    (eK : K ⧸ center K ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    p % 8 = 3 ∧ DegreeThree p K := by
  obtain ⟨hm, hj⟩ := component_unitary_three_small_sylow_models
    eG hK T hT J hp hcard hconj hsign eK
  refine ⟨hm, ?_⟩
  rcases hj with hj | hj
  · exact .unitary F J hcard hconj hsign (Classical.choice hj)
  · exact .projectiveUnitary F J hcard hconj hsign (Classical.choice hj)

variable {G₁ G₂ : Subgroup G}

/-- The exact row-(10) application in the linear branch. The local groups
are the supplied original generators; the model is constructed from their
ambient component's literal central quotient. -/
theorem ten_linear_of_source_component
    (hK : IsComponent G (generalizedFitting G)) (htop : generalizedFitting G = ⊤)
    (S : Sylow 2 G) (hsylow : Nonempty (S ≃* W32))
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card F = p) (hsign : p % 4 = 1)
    (eK : generalizedFitting G ⧸ center (generalizedFitting G) ≃* PSL(3,F))
    (hleft : CyclicQuaternionExtension G₁ (Equiv.Perm (Fin 3)))
    (hright : Extension G₂ C4Square (Equiv.Perm (Fin 3))) : Alternative G₁ G₂ S := by
  obtain ⟨jS⟩ := hsylow
  have hS : Nat.card S ≤ 64 := by
    rw [Nat.card_congr jS.toEquiv, RegularWreathProduct.card]
    norm_num [C]
  obtain ⟨hm, hmodel⟩ := degreeThree_linear_of_source_component hK S hS hp hcard hsign eK
  let j : generalizedFitting G ≃* G := (MulEquiv.subgroupCongr htop).trans topEquiv
  exact .ten p hp (.inr hm) (hmodel.of_mulEquiv j.symm) htop hK.2 ⟨jS⟩ hleft hright

/-- The exact row-(10) application in the unitary branch, with the original
prime-to-three quotient supplying the scalar-cover hypothesis. -/
theorem ten_unitary_of_source_component
    (eG : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G (generalizedFitting G)) (htop : generalizedFitting G = ⊤)
    (S : Sylow 2 G) (hsylow : Nonempty (S ≃* W32))
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p) (hsign : p % 4 = 3)
    (eK : generalizedFitting G ⧸ center (generalizedFitting G) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J)
    (hleft : CyclicQuaternionExtension G₁ (Equiv.Perm (Fin 3)))
    (hright : Extension G₂ C4Square (Equiv.Perm (Fin 3))) : Alternative G₁ G₂ S := by
  obtain ⟨jS⟩ := hsylow
  have hS : Nat.card S ≤ 64 := by
    rw [Nat.card_congr jS.toEquiv, RegularWreathProduct.card]
    norm_num [C]
  obtain ⟨hm, hmodel⟩ := degreeThree_unitary_of_source_component
    eG hK S hS J hp hcard hconj hsign eK
  let j : generalizedFitting G ≃* G := (MulEquiv.subgroupCongr htop).trans topEquiv
  exact .ten p hp (.inl hm) (hmodel.of_mulEquiv j.symm) htop hK.2 ⟨jS⟩ hleft hright

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
