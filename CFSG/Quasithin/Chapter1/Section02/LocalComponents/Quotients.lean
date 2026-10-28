module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.CComponent.QuotientLifting
public import CFSG.Quasithin.Defs

/-!
# Local components in the quotient by the two-core

This module proves the quotient deductions in Proposition 1.2.1(1)–(2)
and the unique-containment part of Lemma 1.2.4. The earlier SQTK results
A.3.7, A.3.9(1), and the containment assertion of A.3.12 are explicit,
universally quantified hypotheses. Their full finite, strongly quasithin,
K-group and trivial-two-core assumptions are retained. The quotient's
SQTK property is a separate input to be discharged by the Chapter 1 owner.
These deductions do not assert the unproved earlier classification results.

Local-family membership survives the solvable quotient by restricting the
quotient map to the join. C-component correspondence, perfectness, and
solvable residuals then lift generation, commutation and containment.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript, 1 March 2004, pp. 503–505.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.Section02
universe u v
variable {G : Type u} {G' : Type v} [Group G] [Group G'] [Finite G]

/-- The A.3 local-component condition survives every homomorphism with solvable kernel. -/
theorem localCComponents_map_of_solvable_ker {B S : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (f : G →* G') [Group.IsSolvable f.ker] :
    B.map f ∈ ChapterA.Section03.localCComponents (S.map f) := by
  let M := B ⊔ S
  let g := f.subgroupMap M
  let : Group.IsSolvable g.ker := by
    change Group.IsSolvable (f.subgroupMap M).ker
    rw [Subgroup.ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := M.subtype.subgroupComap f.ker) (fun a b he => Subtype.ext (Subtype.ext
        (congrArg (fun x : f.ker => (x : G)) he)))
  have h := cComponent_map_of_solvable_ker hB g (f.subgroupMap_surjective M)
  have he : (B.subgroupOf M).map g = (B.map f).subgroupOf (M.map f) := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact mem_map.mpr ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, hbx⟩
      exact ⟨⟨b, (show B ≤ M from le_sup_left) hb⟩, hb, Subtype.ext hbx⟩
  rw [he] at h
  change ((B.map f).subgroupOf (B.map f ⊔ S.map f)).IsCComponent
  rw [← Subgroup.map_sup]
  exact h

/-- The generation assertion of 1.2.1(1), conditional on the universal earlier result A.3.9(1). -/
theorem proposition_1_2_1_one_of_A_3_9 {𝒦 : GroupClass.{u}}
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → cComponentLayer X = solvableResidual X)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G)) :
    cComponentLayer G = solvableResidual G := by
  let := pCore_isNilpotent (p := 2) (G := G)
  exact cComponentLayer_eq_residual_of_quotient (pCore 2 G)
    (hA39 _ hQ (pCore_quotient_pCore_eq_bot 2))

/-- Both inclusions in 1.2.1(2), conditional on the universal earlier result A.3.7. -/
theorem proposition_1_2_1_two_of_A_3_7 {𝒦 : GroupClass.{u}}
    (hA37 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ →
      ∀ B K : Subgroup X, B.IsCComponent → K.IsCComponent → B ≠ K → ⁅B, K⁆ = ⊥)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    {B K : Subgroup G} (hB : B.IsCComponent) (hK : K.IsCComponent) (hne : B ≠ K) :
    ⁅B, K⁆ ≤ B.pCoreIn 2 ⊓ K.pCoreIn 2 ∧
      B.pCoreIn 2 ⊓ K.pCoreIn 2 ≤ pCore 2 G := by
  let := pCore_isNilpotent (p := 2) (G := G)
  apply cComponent_commutator_le_twoCores_of_quotient_commutes hB hK
  exact hA37 _ hQ (pCore_quotient_pCore_eq_bot 2) _ _
    (hB.map_quotient _) (hK.map_quotient _)
    (fun he => hne (hB.eq_of_map_quotient_eq hK _ he))

/-- Chapter 1 local components map to A.3 local components modulo the two-core. -/
theorem mem_L_map_twoCore_mem_localCComponents {B S : Subgroup G} (hB : B ∈ L G S) :
    B.map (QuotientGroup.mk' (pCore 2 G)) ∈ ChapterA.Section03.localCComponents
      (S.map (QuotientGroup.mk' (pCore 2 G))) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  let : Group.IsSolvable (QuotientGroup.mk' (pCore 2 G)).ker := by
    rw [QuotientGroup.ker_mk']; infer_instance
  exact localCComponents_map_of_solvable_ker hB.1 _

/-- The unique-containment assertion of 1.2.4, conditional on the earlier A.3.12 assertion in the quotient. -/
theorem lemma_1_2_4_containment_of_A_3_12 {𝒦 : GroupClass.{u}}
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents T →
      ∃! K : Subgroup X, K.IsCComponent ∧ B ≤ K)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ L G S) :
    ∃! K : Subgroup G, K.IsCComponent ∧ B ≤ K := by
  let := pCore_isNilpotent (p := 2) (G := G)
  let := mem_L_isPerfect hB
  apply existsUnique_cComponent_lift_containing (pCore 2 G)
  apply hA312 _ hQ (pCore_quotient_pCore_eq_bot 2)
    (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G)))
  simpa only [Sylow.coe_mapSurjective] using mem_L_map_twoCore_mem_localCComponents hB

end CFSG.Quasithin.Chapter1.Section02
