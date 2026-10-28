module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.Actors
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.ComponentCriterion
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.FixedModel
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.Reduction

/-!
# External E-members for the symplectic swapping branch: conditional assembly

Choose a swapping involution t in the original elementary actor A and put
D = C_G(t). The actor and ambient tau lie in D. If D has two-core contained
in ⟨t⟩ and a genuine Suzuki core quotient, the large-rank hypothesis makes
A act nontrivially on that quotient. The component criterion proves every
E2 clause and bounds the actual radical-quotient image by the field degree.
A Sylow intersection calculation then gives the required E-member.

The final theorem constructs the exact external witness used by
`Swapping.isEGenerated_of_diagramKernel_calculations`, conditional on three
remaining mathematical inputs: graph-cocycle descent; the ambient involution
supplement and intrinsic centralizer core/quotient; and the centralizer's
Sylow intersection and generation with the original T. The marked relative
Suzuki model is provided in FixedModel. No arbitrary involution centralizer
intersection is asserted to be Sylow, and this is not the completed source
E.1.14(1) branch.

Source: Aschbacher--Smith, E.1.1--2, E.1.5 and E.1.14(1), printed
pp.209--210,214; the exceptional fixed-group realization is 16.1.4(7), p.1171.
-/

public section

open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers
open DiagramAutomorphisms BenderSuzuki.MatrixGroups
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- Apply the Suzuki quotient criterion to the original involution centralizer.
All E0/E2 and quotient-rank clauses are discharged from the displayed model
and Sylow data. The ambient group and Sylow subgroup are unchanged. -/
theorem centralizer_isEMemberAt [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hq : 2 < Nat.card F)
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {f : ℕ} (hf : 1 < f) (hodd : Odd f) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) (hr : f < Group.rank A)
    (t : G) (htA : t ∈ A) (htorder : orderOf t = 2)
    (hcore : pCore 2 (centralizer ({t} : Set G)) ≤
      (zpowers t).subgroupOf (centralizer ({t} : Set G)))
    (emodel : (centralizer ({t} : Set G) ⧸ pCore 2 (centralizer ({t} : Set G))) ≃*
      SuzukiMatrixGroup (f / 2))
    (hSyl : ∃ S : Sylow 2 (centralizer ({t} : Set G)),
      (S : Subgroup (centralizer ({t} : Set G))) =
        (T : Subgroup G).subgroupOf (centralizer ({t} : Set G))) :
    IsEMemberAt f (T : Subgroup G) A (centralizer ({t} : Set G)) := by
  have hdeg : 2 * (f / 2) + 1 = f := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have hpos : 0 < f / 2 := by omega
  have hAK := actor_le_centralizer A htA
  have hAcore := actor_not_le_core_of_core_le_involution A _ hAK htorder
    (lt_trans hf hr) hcore
  simpa only [hdeg] using isEMemberAt_of_suzuki_core_quotient (f / 2) hpos T A _
    hAT hAK (tau_le_centralizer e hq T hLT A htA) hSyl emodel hAcore

/-- Conditional construction matching the external-member consumer exactly.
The outstanding inputs are genuine graph-cocycle descent, the intrinsic
centralizer core/quotient, and its intersection and generation with the given
Sylow. This theorem does not assert that those inputs have been proved. -/
theorem exists_external_member_of_normalized_calculations
    [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (T : Sylow 2 G)
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f) (hodd : Odd f)
    (hq : 2 < Nat.card F) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) (hAH : ¬ A ≤ diagramKernel (generalizedFitting G) e hq)
    (hr : f < Group.rank A)
    (hdescent : ∀ g : Sp F, g * (ExceptionalGraph.graphAut ^ f) g = 1 →
      ∃ h : Sp F, g = h * ((ExceptionalGraph.graphAut ^ f) h)⁻¹)
    (hquotient : ∀ t ∈ A, t ∉ diagramKernel (generalizedFitting G) e hq → orderOf t = 2 →
      ∀ h : Sp F, extensionAction (generalizedFitting G) e t =
        MulAut.conj h * ExceptionalGraph.graphAut ^ f * (MulAut.conj h)⁻¹ →
      let D := centralizer ({t} : Set G)
      generalizedFitting G ⊔ zpowers t = ⊤ ∧
        pCore 2 D ≤ (zpowers t).subgroupOf D ∧
        Nonempty ((D ⧸ pCore 2 D) ≃* SuzukiMatrixGroup (f / 2)))
    (hgeometry : ∀ t ∈ A, t ∉ diagramKernel (generalizedFitting G) e hq → orderOf t = 2 →
      ∀ h : Sp F, extensionAction (generalizedFitting G) e t =
        MulAut.conj h * ExceptionalGraph.graphAut ^ f * (MulAut.conj h)⁻¹ →
      generalizedFitting G ⊔ zpowers t = ⊤ →
      let D := centralizer ({t} : Set G)
      (∃ S : Sylow 2 D, (S : Subgroup D) = (T : Subgroup G).subgroupOf D) ∧
        D ⊔ (T : Subgroup G) = ⊤) :
    ∃ D : Subgroup G, IsEMemberAt f (T : Subgroup G) A D ∧ D ⊔ (T : Subgroup G) = ⊤ := by
  obtain ⟨t, htA, htH, htorder, h, hnorm⟩ :=
    exists_normalized_swapping_involution (generalizedFitting G) e hF hf hq A hAH hdescent
  obtain ⟨hsplit, hcore, ⟨emodel⟩⟩ := hquotient t htA htH htorder h hnorm
  obtain ⟨hSyl, hgen⟩ := hgeometry t htA htH htorder h hnorm hsplit
  exact ⟨centralizer ({t} : Set G),
    centralizer_isEMemberAt e hq T hLT hf hodd A hAT hr t htA htorder hcore emodel hSyl, hgen⟩

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers
