module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation.LinearSeparation
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation.FromStructure
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting

/-!
# A.3.7: distinct C-components commute

The proved noncentral branch of A.3.6 supplies the only structural input to
the commutation argument. That argument restricts to the join of the two
components, separates their actual Frattini actions, and uses generalized
Fitting self-centralization. This gives the literal universal A.3.7 input
and discharges it in the original two-core quotient application of 1.2.1(2).
The internal central-product corollary states generation and pairwise
commutation for the original components inside their generated subgroup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.7, printed p.45.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.CComponentCommutation
universe u

/-- Supply the universal noncentral A.3.6 input from its completed proof. -/
theorem noncentralStructureInput (𝒦 : GroupClass.{u}) : NoncentralStructureInput 𝒦 := by
  intro X _ _ hX hO B hB hn
  exact NoncentralFitting.structure_of_noncentral hX hO hB hn

/-- The literal universal conclusion of A.3.7, with every structural and
cover-rigidity premise discharged. -/
theorem universal_A_3_7 {𝒦 : GroupClass.{u}} :
    ∀ (X : Type u) [Group X] [Finite X], IsSQTK 𝒦 X → pCore 2 X = ⊥ →
      ∀ B C : Subgroup X, B.IsCComponent → C.IsCComponent → B ≠ C → ⁅B,C⁆ = ⊥ :=
  universal_A_3_7_of_noncentral_structure (noncentralStructureInput 𝒦)

variable {G : Type u} [Group G] [Finite G]

/-- Distinct C-components of an SQTK group with trivial two-core commute. -/
theorem commutator_eq_bot
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    {B C : Subgroup G} (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C) :
    ⁅B,C⁆ = ⊥ :=
  universal_A_3_7 G hG hO B C hB hC hne

/-- The final assertion of A.3.7: the C-component layer is the internal
central product of its C-components, with their original embeddings. -/
theorem cComponentLayer_central_product
    {𝒦 : GroupClass.{u}} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥) :
    (⨆ B : {B : Subgroup G // B.IsCComponent},
      B.val.subgroupOf (cComponentLayer G)) = ⊤ ∧
    Pairwise (fun B C : {B : Subgroup G // B.IsCComponent} =>
      ⁅B.val.subgroupOf (cComponentLayer G), C.val.subgroupOf (cComponentLayer G)⁆ = ⊥) := by
  constructor
  · apply Subgroup.map_subtype_inj.mp
    simp only [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.subtype_range]
    calc
      (⨆ B : {B : Subgroup G // B.IsCComponent},
        (B.val.subgroupOf (cComponentLayer G)).map (cComponentLayer G).subtype) =
          ⨆ B : {B : Subgroup G // B.IsCComponent}, B.val :=
        iSup_congr fun B => map_subgroupOf_eq_of_le (le_cComponentLayer B.property)
      _ = cComponentLayer G := (sSup_eq_iSup' _).symm
  · intro B C hne
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_commutator,
      map_subgroupOf_eq_of_le (le_cComponentLayer B.property),
      map_subgroupOf_eq_of_le (le_cComponentLayer C.property), Subgroup.map_bot]
    exact commutator_eq_bot hG hO B.property C.property (fun h => hne (Subtype.ext h))

/-- Both inclusions of 1.2.1(2) for the actual quotient by O₂(G), with its
original SQTK hypothesis and the universal A.3.7 input now proved. -/
theorem proposition_1_2_1_two
    {𝒦 : GroupClass.{u}} (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    {B C : Subgroup G} (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C) :
    ⁅B,C⁆ ≤ B.pCoreIn 2 ⊓ C.pCoreIn 2 ∧ B.pCoreIn 2 ⊓ C.pCoreIn 2 ≤ pCore 2 G :=
  Chapter1.Section02.proposition_1_2_1_two_of_A_3_7 universal_A_3_7 hQ hB hC hne

end CFSG.Quasithin.ChapterA.Section03.CComponentCommutation
