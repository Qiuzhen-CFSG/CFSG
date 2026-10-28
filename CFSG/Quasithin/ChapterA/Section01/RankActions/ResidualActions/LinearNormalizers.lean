module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.ResidualActions.LinearInputs
public import Theory.SpecificGroups.GL2.TwoSubgroupNormalizerAction

/-!
# The GL₂ normalizer calculations for A.1.26

Conjugation on an elementary abelian two-subgroup has two-group image, and
conjugation on an arbitrary two-subgroup has {2,3}-group image. The kernel is
therefore one of the normal subgroups defining the corresponding residual.
This proves both literal source formulations and both universal contracts
used by the odd-core and solvable-quotient reductions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.1.26,
printed pp.25–26. The underlying matrix calculation uses the determinant-one
subgroup, its scalar involution, and the proved cyclic/quaternion alternatives.
No classification or action premise is left to the consumer.
-/

open Subgroup

namespace CFSG.Quasithin.ChapterA.RankActions
open Matrix.GeneralLinearGroup

private theorem two_ne_zero {p : ℕ} [Fact p.Prime] (hp : Odd p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have he : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
    (Fact.out : p.Prime).ne_one
  subst p
  obtain ⟨k, hk⟩ := hp
  omega

private theorem centralizes_of_rangeAction_trivial {G : Type*} [Group G]
    (X V : Subgroup G) (hn : X ≤ normalizer (V : Set G))
    (h : V.normalizerMonoidHom.rangeRestrict.comp (Subgroup.inclusion hn) = 1) :
    ⁅V, X⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro v hv
  apply mem_centralizer_iff.mpr
  intro x hx
  have he := congrArg (fun f : X →* V.normalizerMonoidHom.range =>
    (((f ⟨x, hx⟩).val ⟨v, hv⟩) : G)) h
  change x * v * x⁻¹ = v at he
  exact (mul_inv_eq_iff_eq_mul).mp he

/-- The unconditional elementary abelian GL₂ normalizer contract in A.1.26(1). -/
public theorem elementaryTwoLinearNormalizer : ElementaryTwoLinearNormalizer := by
  intro p _ hp X V hX hV hn
  let := hV
  have hR := normalizerAction_isPGroup_of_elementaryAbelian_two (two_ne_zero hp) V
  let f := V.normalizerMonoidHom.rangeRestrict.comp (Subgroup.inclusion hn)
  have hq : IsPGroup 2 (X ⧸ f.ker) :=
    (hR.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hk := hX f.ker inferInstance hq
  apply centralizes_of_rangeAction_trivial X V hn
  change f = 1
  apply MonoidHom.ext
  intro x
  exact MonoidHom.mem_ker.mp (hk.symm ▸ mem_top x)

/-- The unconditional GL₂ normalizer contract in A.1.26(2), using the genuine
{2,3}-residual convention. -/
public theorem twoLinearNormalizer : TwoLinearNormalizer := by
  intro p _ hp X V hX hV hn
  have hR := normalizerAction_isPiGroup_of_isPGroup_two (two_ne_zero hp) V hV
  let f := V.normalizerMonoidHom.rangeRestrict.comp (Subgroup.inclusion hn)
  have hq : IsPiGroup twoThreePrimes (X ⧸ f.ker) :=
    hR.of_injective (QuotientGroup.kerLift f) (QuotientGroup.kerLift_injective f)
  have hk := hX f.ker inferInstance hq
  apply centralizes_of_rangeAction_trivial X V hn
  change f = 1
  apply MonoidHom.ext
  intro x
  exact MonoidHom.mem_ker.mp (hk.symm ▸ mem_top x)

private theorem centralizes_embedded_of_le_actionKernel {G : Type*} [Group G]
    (V : Subgroup G) (R : Subgroup (normalizer (V : Set G)))
    (hR : R ≤ V.normalizerMonoidHom.ker) :
    ⁅V, R.map (normalizer (V : Set G)).subtype⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro v hv
  apply mem_centralizer_iff.mpr
  rintro x ⟨n, hn, rfl⟩
  have he := congrArg (fun a : MulAut V => (a ⟨v, hv⟩ : G)) (hR hn)
  change n.val * v * n.val⁻¹ = v at he
  exact (mul_inv_eq_iff_eq_mul).mp he

/-- Source formulation: O²(N_GL₂(p)(A)) centralizes every elementary abelian
two-subgroup A. The residual is embedded from the actual normalizer. -/
public theorem pResidual_normalizer_centralizes_elementaryTwo
    (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (A : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)))
    [IsElementaryAbelian 2 A] :
    ⁅A, (pResidual 2 (normalizer (A : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))))).map
      (normalizer (A : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)))).subtype⁆ = ⊥ := by
  apply centralizes_embedded_of_le_actionKernel
  have hR := normalizerAction_isPGroup_of_elementaryAbelian_two (two_ne_zero hp) A
  exact sInf_le ⟨inferInstance,
    (hR.of_equiv (QuotientGroup.quotientKerEquivRange A.normalizerMonoidHom).symm)⟩

/-- Source formulation: O^{2,3}(N_GL₂(p)(S)) centralizes every two-subgroup S.
The residual is the intersection of normal subgroups with {2,3}-group quotient. -/
public theorem piResidual_normalizer_centralizes_two
    (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) (hS : IsPGroup 2 S) :
    ⁅S, (piResidual twoThreePrimes (normalizer (S : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))))).map
      (normalizer (S : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)))).subtype⁆ = ⊥ := by
  apply centralizes_embedded_of_le_actionKernel
  have hR := normalizerAction_isPiGroup_of_isPGroup_two (two_ne_zero hp) S hS
  exact sInf_le ⟨inferInstance,
    (hR.of_equiv (QuotientGroup.quotientKerEquivRange S.normalizerMonoidHom))⟩
end CFSG.Quasithin.ChapterA.RankActions
