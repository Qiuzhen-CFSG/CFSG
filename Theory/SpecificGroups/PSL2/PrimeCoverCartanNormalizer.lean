module
public import Theory.SpecificGroups.PSL2.PrimeCartanNormalizer
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.SpecificGroups.SL2.PrimeFieldOddSubgroups
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.Quasithin.CoprimeRank

/-!
# Cubic normalization through an actual prime-SL₂ cover

A surjection onto SL₂(p) with two-group kernel identifies the intrinsic
two-core quotient with PSL₂(p). The equivalence retains the projection
on representatives. Odd Sylow subgroups of prime-field SL₂ are cyclic,
so the three-rank hypothesis in the existing Cartan normalizer theorem
is automatic. This proves normalization of a perfect subgroup containing
the marked cubic, once the covering group's two-core normalizes it.

Source: Aschbacher--Smith, Proposition 9.3.1, printed p.732, reduction
from the noncentral odd-core container to the prime-linear row.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2

/-- Every odd-prime rank of prime-field PSL₂ is at most one. -/
theorem primeField_odd_rank {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (ho : Odd r) : primeRank r PSL(2, ZMod p) ≤ 1 := by
  let P : Sylow r SL(2, ZMod p) := Classical.choice inferInstance
  have hc : IsCyclic P :=
    Matrix.SpecialLinearGroup.isCyclic_of_odd_pGroup_injective_primeField
      P.isPGroup' (by intro h; subst r; norm_num at ho)
      (P : Subgroup SL(2, ZMod p)).subtype Subtype.val_injective
  exact P.primeRank_le_one_of_surjective hc
    (GorensteinWalter.sl2ProjectiveProjection (ZMod p))
    (GorensteinWalter.sl2ProjectiveProjection_surjective (ZMod p))

/-- A two-group extension of SL₂ has the canonical PSL₂ two-core quotient. -/
noncomputable def primeSL2CoverCoreEquiv
    {X : Type*} [_root_.Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp : 3 < p) (f : X →* SL(2,ZMod p)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : (X ⧸ pCore 2 X) ≃* PSL(2,ZMod p) := by
  let : IsQuasisimple SL(2,ZMod p) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by simpa using hp) (MulEquiv.refl _)
  have ho : Odd (Nat.card (ZMod p)) := by
    simpa using (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hz : IsPGroup 2 (center SL(2,ZMod p)) := by
    exact (GorensteinWalter.sl2ProjectiveProjection_ker_isPGroup (ZMod p) ho).of_equiv
      (MulEquiv.subgroupCongr (GorensteinWalter.sl2ProjectiveProjection_ker (ZMod p)))
  have he : pCore 2 SL(2,ZMod p) = center SL(2,ZMod p) :=
    le_antisymm (IsQuasisimple.pCore_le_center 2) (le_sSup ⟨inferInstance,hz⟩)
  exact (MonoidHom.quotientPCoreEquivOfSurjective f hf hk).trans
    (QuotientGroup.quotientMulEquivOfEq he)

/-- The core-quotient equivalence retains the original projective map. -/
theorem primeSL2CoverCoreEquiv_mk
    {X : Type*} [_root_.Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp : 3 < p) (f : X →* SL(2,ZMod p)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (x : X) :
    primeSL2CoverCoreEquiv hp f hf hk (QuotientGroup.mk' (pCore 2 X) x) =
      GorensteinWalter.sl2ProjectiveProjection (ZMod p) (f x) := by
  simp only [primeSL2CoverCoreEquiv, MulEquiv.trans_apply,
    MonoidHom.quotientPCoreEquivOfSurjective_mk]
  rfl

/-- The actual SL₂ cover discharges all rank-one model inputs to Cartan normalization. -/
theorem cartan_normalizes_of_primeSL2_cover
    {G : Type*} [_root_.Group G] [Finite G]
    (K J A B : Subgroup G) [Group.IsPerfect K] [IsElementaryAbelian 3 A]
    (hKJ : K ≤ J) (hAJ : A ≤ normalizer (J : Set G))
    (hBA : B ≤ A) (hBK : B ≤ K)
    (hQK : J.pCoreIn 2 ≤ normalizer (K : Set G)) (hB : Nat.card B = 3)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (f : J →* SL(2,ZMod p)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : A ≤ normalizer (K : Set G) := by
  let a := primeSL2CoverCoreEquiv hp f hf hk
  have hr : primeRank 3 J ≤ 1 := by
    rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 J) pCore_isPGroup,
      primeRank_congr 3 a]
    exact primeField_odd_rank (by decide)
  exact primeField_cartan_normalizes_perfect_subgroup K J A B hKJ hAJ hBA hBK
    hQK hB hr (Fact.out : p.Prime) ((Fact.out : p.Prime).odd_of_ne_two (by omega))
    (by simp) a

end Theory.PSL2

