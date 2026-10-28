module

public import Theory.GroupTheory.CentricRadicalCharacterFusion
public import Theory.GroupTheory.FusionInvariantTransfer
public import Mathlib.GroupTheory.IndexNormal

/-!+# Binary kernels and intrinsic-radical fusion

To contradict simplicity, it suffices that the normalizers of the centric
intrinsic-radical candidates preserve membership in an index-two Sylow subgroup.
The quotient by that subgroup supplies the binary character, Alperin reduction
makes it invariant under fusion, and ordinary transfer contradicts its
nontriviality. This is the transfer step in the second Held candidate argument
(Huppert--Blackburn III, XII.1.18(b), p.314).
-/

open Subgroup BenderSuzuki.External
namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer

/-- The concrete intrinsic-radical condition, stated for two subgroups of the
same group. Normality and automorphisms here are intrinsic to `U`. -/
@[expose] public def IntrinsicRadicalIn {H : Type*} [Group H]
    (S U : Subgroup H) : Prop :=
  ((S.subgroupOf (normalizer (U : Set H))).map U.normalizerMonoidHom ⊓
    pCore 2 (MulAut U)) ≤ (MulAut.conj : U →* MulAut U).range

/-- Membership invariance on precisely the normalizers needed by the
intrinsic-radical fusion theorem. -/
@[expose] public def PreservesKernel {G : Type*} [Group G]
    (S : Sylow 2 G) (M : Subgroup S) : Prop :=
  ∀ U : Subgroup G, U ≤ (S : Subgroup G) →
    (Nat.card ↥((S : Subgroup G) ⊓ normalizer (U : Set G))).factorization 2 =
      (Nat.card (normalizer (U : Set G))).factorization 2 →
    ((S : Subgroup G) ⊓ centralizer (U : Set G)) ≤ U →
    IntrinsicRadicalIn (S : Subgroup G) U →
    ∀ g ∈ normalizer (U : Set G), ∀ x y : S, (x : G) ∈ U →
      g⁻¹ * (x : G) * g = (y : G) → (x ∈ M ↔ y ∈ M)

/-- The genuine character-fusion and transfer implication; no character or
nontriviality witness is added to the hypotheses. -/
public theorem false_of_preservesKernel
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G) (M : Subgroup S)
    (hindex : M.index = 2) (hpreserve : PreservesKernel S M) : False := by
  classical
  let : M.Normal := M.normal_of_index_eq_two hindex
  have hcard : Nat.card (S ⧸ M) = 2 := hindex
  let : IsCyclic (S ⧸ M) := isCyclic_of_prime_card hcard
  let : CommGroup (S ⧸ M) := IsCyclic.commGroup
  let chi : S →* S ⧸ M := QuotientGroup.mk' M
  have hchi (x : S) : chi x = 1 ↔ x ∈ M := QuotientGroup.eq_one_iff x
  have heq (x y : S) (hmem : x ∈ M ↔ y ∈ M) : chi x = chi y := by
    by_cases hx : x ∈ M
    · rw [(hchi x).mpr hx, (hchi y).mpr (hmem.mp hx)]
    · obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (1 : S ⧸ M)).mp hcard
      exact (ha _ (fun hh => hx ((hchi x).mp hh))).trans
        (ha _ (fun hh => hx (hmem.mpr ((hchi y).mp hh)))).symm
  have hfusion (x y : S) (hxy : IsConj (x : G) (y : G)) : chi x = chi y := by
    apply S.intrinsic_radical_character_fusion chi (fun U hUS hext hcent hrad g hg a b ha hab =>
      heq a b (hpreserve U hUS hext hcent hrad g hg a b ha hab)) hxy
  have htop : M = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact (hchi x).mp (S.fusion_invariant_eq_one_of_simple hns chi hcard hfusion x)
  simp [htop] at hindex

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer
