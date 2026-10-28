module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.Setup

/-!
# Lifting the linear-case complement from the two-core

GLS, Volume 4, Chapter 2, Lemma 15.7 first constructs a normal subgroup
`M₁` complementing `U = V ∩ D` inside `V = O₂(M)`. When `M = DV`, this
is a complement to `D` in `M`. The theorem below proves that passage with
all subgroups and normality interpreted relative to `M`.

The construction of `M₁` in the proper-closure case and the exclusion of
the equality case remain prerequisites. In particular this conditional
lifting lemma does not assert the source Lemma 15.7.
-/

noncomputable section

namespace BenderSuzuki.ZD

/-- A complement to the pair stabilizer's intersection with `O₂(M)`
lifts to a complement in `M` when the pair stabilizer supplements `O₂(M)`.
Normality of the constructed subgroup can be carried separately in `M`. -/
public theorem linear_pair_complement_of_twoCore_complement
    {G : Type*} [Group G] {M : Subgroup G} {t : G}
    (N : Subgroup M) (hNV : N ≤ pCore 2 M)
    (hDV : (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤)
    (hsplit : (((residualPairStabilizer M t).subgroupOf M).subgroupOf (pCore 2 M)).IsComplement'
      (N.subgroupOf (pCore 2 M))) :
    ((residualPairStabilizer M t).subgroupOf M).IsComplement' N := by
  let D := (residualPairStabilizer M t).subgroupOf M
  let V := pCore 2 M
  have hdis : Disjoint D N := by
    apply Subgroup.disjoint_def.mpr
    intro x hxD hxN
    have hx : (⟨x, hNV hxN⟩ : V) = 1 :=
      Subgroup.disjoint_def.mp hsplit.disjoint hxD hxN
    exact congrArg Subtype.val hx
  refine ⟨Subgroup.mul_injective_of_disjoint hdis, ?_⟩
  intro g
  have hg : g ∈ D ⊔ V := by rw [hDV]; exact Subgroup.mem_top g
  obtain ⟨d, hd, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  obtain ⟨⟨j, k⟩, hjk⟩ := hsplit.2 ⟨v, hv⟩
  have heq : ((j : V) : M) * ((k : V) : M) = v := congrArg Subtype.val hjk
  refine ⟨(⟨d * ((j : V) : M), D.mul_mem hd j.property⟩,
    ⟨((k : V) : M), k.property⟩), ?_⟩
  change (d * ((j : V) : M)) * ((k : V) : M) = d * v
  rw [mul_assoc, heq]

end BenderSuzuki.ZD
