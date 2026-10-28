module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.InitialStructure
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Geometry

/-!
# The kernel of the distinguished action in the exceptional branch

The point centralizer C_M(A) is normal in M. Its index over C_G(L) divides
q³, so the source order |C_G(L)|=2 makes it a two-group. Conversely O₂(M)
centralizes A because the distinguished involutions are two-central.
Thus C_M(A)=O₂(M), on the original internal subgroup A=M°.

Source: GLS IV, Chapter 2, (15B) and the equality branch of Lemma 15.7.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

/-- The exact kernel of conjugation on the distinguished elementary group.
It needs only the source order-two centralizer, not the exceptional action. -/
public theorem Context.distinguished_centralizer_eq_twoCore
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2) :
    centralizer ((closure (Z ∩ (M : Set G))).subgroupOf M : Set M) = pCore 2 M := by
  let A := closure (Z ∩ (M : Set G))
  let C := M ⊓ centralizer (A : Set G)
  have heq : C.subgroupOf M = centralizer (A.subgroupOf M : Set M) := by
    ext x
    constructor
    · intro hx a ha
      exact Subtype.ext (mem_centralizer_iff.mp hx.2 a ha)
    · intro hx
      refine ⟨x.property, ?_⟩
      intro a ha
      exact congrArg Subtype.val (mem_centralizer_iff.mp hx
        ⟨a, distinguishedClosure_le ha⟩ ha)
  have hP : IsPGroup 2 (centralizer (residualGenerated M z t : Set G)) :=
    IsPGroup.of_card (n := 1) (by simpa using hJ)
  have hC : IsPGroup 2 (C.subgroupOf M) :=
    (d.centralizer_isPGroup_of_isPGroup hP).of_equiv
      (subgroupOfEquivOfLe (show C ≤ M from inf_le_left)).symm
  have hN : (C.subgroupOf M).Normal := d.centralizer_normal
  apply le_antisymm
  · rw [← heq]
    exact le_sSup ⟨hN, hC⟩
  · exact linear_twoCore_le_distinguished_centralizer d.minimal.disconnected d.reduction

end BenderSuzuki.ZD.LinearExclusion
