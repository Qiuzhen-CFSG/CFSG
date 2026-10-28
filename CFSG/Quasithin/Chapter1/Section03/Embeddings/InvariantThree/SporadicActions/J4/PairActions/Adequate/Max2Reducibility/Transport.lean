module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.MatrixConditions

/-!
# Transport through an actual maximal max2 embedding

An equivalence from the supplied overgroup to the ATLAS max2 word subgroup,
followed by its certified matrix quotient, has kernel exactly the overgroup's
two-core. Every three-subgroup therefore embeds in the quotient. The supplied
ambient Sylow subgroup maps to a Sylow subgroup, and setwise permutability
survives restriction and projection.

Every automorphism of the overgroup descends through its characteristic
two-core. Consequently all compatible actors on the original complement act
compatibly on its matrix image. This does not require innerness or equality
between the word subgroup and the full ambient involution centralizer.

Source application: Aschbacher–Smith, proof of Proposition 1.3.4, printed
p.511/PDF p.528 of `refs/quasithin.pdf`; the actual quotient and conjugacy
comparisons are certified in `QuotientIncidence.MatrixQuotient`.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Janko4.modelGroup sourceSubgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2

/-- The certified matrix projection after the supplied actual equivalence. -/
noncomputable def projection {G : Type*} [Group G] {M : Subgroup G}
    (e : M ≃* sourceSubgroup) : M →* MatrixGroup :=
  involutionSourceMatrixMap.comp e.toMonoidHom

/-- The projection covers the actual matrix group. -/
theorem projection_surjective {G : Type*} [Group G] {M : Subgroup G}
    (e : M ≃* sourceSubgroup) : Function.Surjective (projection e) :=
  involutionSourceMatrixMap_surjective.comp e.surjective

/-- The kernel is the two-core of the supplied overgroup. -/
theorem projection_ker {G : Type*} [Group G] {M : Subgroup G}
    (e : M ≃* sourceSubgroup) : (projection e).ker = pCore 2 M := by
  rw [projection, ← MonoidHom.comap_ker, involutionSourceMatrixMap_ker]
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_comap_eq_self_of_surjective e.surjective, pCore_map_iso]

/-- Every three-subgroup injects across the binary kernel. -/
theorem complement_injective {G : Type*} [Group G] {M R : Subgroup G}
    (e : M ≃* sourceSubgroup) (hRM : R ≤ M) (h3 : IsPGroup 3 R) :
    Function.Injective ((projection e).comp (inclusion hRM)) := by
  have hd : Disjoint (R.subgroupOf M) (pCore 2 M) :=
    IsPGroup.disjoint_of_coprime
      (h3.of_equiv (subgroupOfEquivOfLe hRM).symm)
      pCore_isPGroup (by decide : Nat.Coprime 3 2)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro r hr
  have hi : inclusion hRM r ∈ pCore 2 M := by
    rw [← projection_ker e]
    exact hr
  have hr1 := disjoint_def.mp hd r.property hi
  exact mem_bot.mpr ((inclusion_injective hRM)
    (by simpa only [map_one] using hr1))

/-- Every local automorphism descends to the certified quotient. -/
theorem exists_quotientActor {G : Type*} [Group G] {M : Subgroup G}
    (e : M ≃* sourceSubgroup) (c : MulAut M) :
    ∃ d : MulAut MatrixGroup, ∀ x : M, projection e (c x) = d (projection e x) := by
  let b := MulAut.congr e c
  let q := involutionSourceMatrixQuotientEquiv
  refine ⟨(q.symm.trans (quotientAut (pCore 2 sourceSubgroup) b)).trans q, fun x => ?_⟩
  change q (QuotientGroup.mk' (pCore 2 sourceSubgroup) (e (c x))) =
    q (quotientAut (pCore 2 sourceSubgroup) b
      (q.symm (q (QuotientGroup.mk' (pCore 2 sourceSubgroup) (e x)))))
  rw [q.symm_apply_apply, quotientAut_apply_mk]
  congr 2
  simp only [b, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

/-- The quotient image retains the full order of the complement. -/
theorem complement_card {G : Type*} [Group G] {M R : Subgroup G}
    (e : M ≃* sourceSubgroup) (hRM : R ≤ M) (h3 : IsPGroup 3 R) :
    Nat.card ((projection e).comp (inclusion hRM)).range = Nat.card R :=
  (Nat.card_congr (MonoidHom.ofInjective (complement_injective e hRM h3)).toEquiv).symm

/-- The elementary source alternative remains elementary in the image. -/
theorem complement_elementary {G : Type*} [Group G] {M R : Subgroup G}
    (e : M ≃* sourceSubgroup) (hRM : R ≤ M) (hE : IsElementaryAbelian 3 R) :
    IsElementaryAbelian 3 ((projection e).comp (inclusion hRM)).range := by
  let _ := hE
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ := IsElementaryAbelian.subgroupOf (p := 3) hRM
  rw [MonoidHom.range_comp, inclusion_range]
  exact IsElementaryAbelian.map (projection e)

/-- The actual Sylow image in the matrix quotient. -/
noncomputable def quotientSylow {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (S : Sylow 2 G) (hSM : S.toSubgroup ≤ M) (e : M ≃* sourceSubgroup) :
    Sylow 2 MatrixGroup :=
  (S.subtype hSM).mapSurjective (f := projection e) (projection_surjective e)

/-- Restriction and projection preserve setwise permutability. -/
theorem pair_permutes {G : Type*} [Group G] [Finite G] {M R : Subgroup G}
    (S : Sylow 2 G) (hSM : S.toSubgroup ≤ M) (hRM : R ≤ M)
    (e : M ≃* sourceSubgroup)
    (h : (R : Set G) * (S : Set G) = (S : Set G) * (R : Set G)) :
    (((projection e).comp (inclusion hRM)).range : Set MatrixGroup) *
        (quotientSylow S hSM e : Set MatrixGroup) =
      (quotientSylow S hSM e : Set MatrixGroup) *
        (((projection e).comp (inclusion hRM)).range : Set MatrixGroup) := by
  have hp : (R.subgroupOf M : Set M) * (S.toSubgroup.subgroupOf M : Set M) =
      (S.toSubgroup.subgroupOf M : Set M) * (R.subgroupOf M : Set M) := by
    apply Set.image_injective.mpr M.subtype_injective
    simpa only [Set.image_mul, ← coe_map, map_subgroupOf_eq_of_le hRM,
      map_subgroupOf_eq_of_le hSM, Sylow.coe_coe] using h
  simpa only [quotientSylow, ← Sylow.coe_coe, Sylow.coe_mapSurjective,
    Sylow.coe_subtype, MonoidHom.range_comp, inclusion_range, coe_map, Set.image_mul]
    using congrArg (Set.image (projection e)) hp

/-- Every specified actor has a compatible quotient automorphism. -/
theorem compatible_quotientActors {G : Type*} [Group G] {S M R : Subgroup G}
    (e : M ≃* sourceSubgroup) (hRM : R ≤ M) (D : Subgroup (MulAut R))
    (hact : CompatibleSylowActions S R M hRM D) :
    ∀ a ∈ D, ∃ c : MulAut MatrixGroup, ∀ r : R,
      ((projection e).comp (inclusion hRM)) (a r) =
        c (((projection e).comp (inclusion hRM)) r) := by
  intro a ha
  obtain ⟨c, _, hcR⟩ := hact a ha
  obtain ⟨d, hd⟩ := exists_quotientActor e c
  refine ⟨d, fun r => ?_⟩
  change projection e (inclusion hRM (a r)) = d (projection e (inclusion hRM r))
  rw [hcR, hd]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2
