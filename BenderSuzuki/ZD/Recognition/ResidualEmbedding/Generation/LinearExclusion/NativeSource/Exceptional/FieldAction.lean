module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Exceptional.FieldTransport
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Exceptional.RootCoordinates
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.NormalClosure

/-!
# Constructing the exceptional field action

The source square coordinates transport the literal M/O₂(M)-action onto the
binary field. The original torus realizes every field scalar. Any element
fixing zero can be corrected by an element of the homocyclic subgroup to
normalize the original L, with the same action on M°. The root marker therefore
makes the zero stabilizer semilinear. Transitivity and all scalars give double
transitivity, completing the input to the independent action classification.

Source: GLS IV, Chapter 2, Lemma 15.7, exceptional equality branch.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII Exceptional
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (s : ExceptionalLocalStructure Z M z t n)
  (d : Context Z M z t n)
  (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
  (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
  (hRV : linearCentralizerClosure M z t = pCore 2 M)
local notation "A" => Subgroup.subgroupOf (closure (Z ∩ (M : Set G))) M
local notation "V" => pCore 2 M
local notation "𝔽" => BinaryGaloisField n

include d in
private theorem point_smul_of_translation_one (m : M)
    (hm : translation s hR hRV m = 1) (a : A) :
    let := pointAction s d hR hRV
    m • a = d.distinguishedConjugation m a := by
  apply Subtype.ext
  change m*(a:M)*m⁻¹*(translation s hR hRV m:M)=m*(a:M)*m⁻¹
  rw [hm, OneMemClass.coe_one, mul_one]

include s d hJ hR hRV in
/-- The field action used in source Lemma 15.7 is constructed from the original
local group, centralizer order, normal closure order and equality branch. -/
public theorem Context.exceptionalFieldAction : Nonempty (ExceptionalFieldAction M n) := by
  obtain ⟨eA, hsemi, hscalar⟩ := d.distinguishedRootCoordinates
  let := pointAction s d hR hRV
  let := fieldAction s d hJ hR hRV eA
  let : FaithfulSMul (M ⧸ V) 𝔽 := fieldAction_faithful s d hJ hR hRV eA
  let : MulAction.IsPretransitive (M ⧸ V) 𝔽 := fieldAction_pretransitive s d hJ hR hRV eA
  have hc : MulAction.SemilinearPointStabilizer.Coordinates (M ⧸ V) 𝔽 := by
    constructor
    · intro c
      obtain ⟨k, hk⟩ := hscalar c
      refine ⟨QuotientGroup.mk' V (k:M), ?_⟩
      intro x
      let a : A := eA.symm (Multiplicative.ofAdd x)
      have ha : (eA a).toAdd=x := by simp [a]
      rw [← ha, fieldAction_smul_mk s d hJ hR hRV eA,
        point_smul_of_translation_one s d hR hRV (k:M)
          (torus_translation_eq_one s hR hRV k), hk]
      rfl
    · intro g hg
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective V g
      have hm : translation s hR hRV m = 1 := by
        have h1 : (eA (1:A)).toAdd=0 := by simp
        rw [← h1, fieldAction_smul_mk s d hJ hR hRV eA] at hg
        have hp : m • (1:A)=1 := eA.injective (Multiplicative.toAdd.injective hg)
        apply Subtype.ext
        have he := congrArg Subtype.val hp
        change m*1*m⁻¹*(translation s hR hRV m:M)=1 at he
        simpa using he
      obtain ⟨c,hcN,hcA⟩ := stabilizer_correction s d hJ hR hRV m hm
      obtain ⟨v,σ,hv⟩ := hsemi c hcN
      refine ⟨v,σ,?_⟩
      intro x
      let a : A := eA.symm (Multiplicative.ofAdd x)
      have ha : (eA a).toAdd=x := by simp [a]
      have hact : m • a = d.distinguishedConjugation c a := by
        rw [point_smul_of_translation_one s d hR hRV m hm]
        apply Subtype.ext
        exact hcA a
      rw [← ha,fieldAction_smul_mk s d hJ hR hRV eA,hact,hv]
      rfl
  exact ⟨{ action := fieldAction s d hJ hR hRV eA
           faithful := fieldAction_faithful s d hJ hR hRV eA
           two_transitive := hc.two_pretransitive_of_pretransitive
           coordinates := hc }⟩

end BenderSuzuki.ZD.LinearExclusion
