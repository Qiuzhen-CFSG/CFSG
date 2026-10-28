module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock.SylowTransfer
public import Mathlib.Data.Finsupp.Fintype

/-!
# Sylow Brauer correspondence for the principal block

Over a finite field, extract the primitive augmentation-one factor of the
Sylow Brauer image. Uniqueness makes that factor normalizer invariant. The
complement has augmentation zero; transfer from the normalizer recovers it
under the Brauer map. In the ambient principal corner this transfer is
nilpotent, forcing its idempotent Brauer image to vanish.

This proves primitivity for the literal coefficient restriction. Source:
Feit III.9 and V.6.2, printed pp.209--210.
-/

public section
noncomputable section
namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
open ModularBlock ModularBlock.NormalizerBrauerAction
open ModularBlock.RelativeTransferBrauer ModularBlock.SubgroupBrauerMap
attribute [local instance] Fintype.ofFinite
variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- The Sylow Brauer image of a principal block is the local principal block. -/
theorem sylow_brauer_isCentrallyPrimitive
    {K : Type*} [Field K] [Finite K] [CharP K p]
    (e : MonoidAlgebra K G) (he : IsCentrallyPrimitive e)
    (heaug : groupAlgebraAugmentation K G e = 1) (P : Sylow p G) :
    IsCentrallyPrimitive (DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G) e) := by
  classical
  let C := Subgroup.centralizer (P : Set G)
  let N := (Subgroup.normalizer (P : Set G))
  let E : MonoidAlgebra K C := DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G) e
  let eps := groupAlgebraAugmentation K C
  let : Finite (MonoidAlgebra K C) :=
    Finite.of_injective MonoidAlgebra.coeff MonoidAlgebra.coeff_injective
  let : Finite (MonoidAlgebra K G) :=
    Finite.of_injective MonoidAlgebra.coeff MonoidAlgebra.coeff_injective
  have hEc : E ∈ Set.center (MonoidAlgebra K C) :=
    subgroupCentralizerRestriction_mem_center (R := K) (P : Subgroup G) e he.1
  have hEi : IsIdempotentElem E :=
    subgroupCentralizerRestriction_isIdempotent_of_mem_center (R := K) (P : Subgroup G) P.isPGroup' e he.1 he.2.1
  have hEa : eps E = 1 :=
    (augmentation_subgroupCentralizerRestriction (R := K) (P : Subgroup G) P.isPGroup' e he.1).trans heaug
  let epsZ : Subring.center (MonoidAlgebra K C) →+* K :=
    eps.toRingHom.comp (Subring.center (MonoidAlgebra K C)).subtype
  obtain ⟨bCI, hb, hbE, hbne⟩ :=
    CentralPrimitiveExistence.exists_isCentrallyPrimitive_factor_map_ne_zero
      epsZ E hEc hEi (by change eps E ≠ 0; rw [hEa]; exact one_ne_zero)
  let b := bCI.val
  have hba : eps b = 1 := by
    have hid : IsIdempotentElem (eps b) := hb.2.1.map eps
    exact (IsIdempotentElem.iff_eq_zero_or_one.mp hid).resolve_left hbne
  have hbfix : ∀ n : N, normalizerConjugate K (P : Subgroup G) n b = b := by
    intro n
    rcases mul_conjugate_eq_zero_or_conjugate_eq (R := K) (P : Subgroup G) n b hb with hz | heq
    · have h := congrArg eps hz
      have hconja : eps (MonoidAlgebra.mapDomainRingEquiv K
          (centralizerConjEquiv (P : Subgroup G) n) b) = eps b :=
        augmentation_mapDomain_centralizerConjEquiv (R := K) (P : Subgroup G) n b
      rw [map_mul, hconja, hba, one_mul, map_zero] at h
      exact (one_ne_zero h).elim
    · exact heq
  have hEfix : ∀ n : N, normalizerConjugate K (P : Subgroup G) n E = E := by
    intro n
    exact subgroupRestriction_mapDomain_centralizerConjEquiv_eq_self (R := K) (P : Subgroup G) n e he.1
  have hEb : E * b = b := (Semigroup.mem_center_iff.mp hEc b).symm.trans hbE
  let B := E - b
  have hBid : IsIdempotentElem B := hb.2.1.sub hEi hbE hEb
  have hBaug : eps B = 0 := by rw [map_sub, hEa, hba, sub_self]
  have hBE : B * E = B := by
    change (E - b) * E = E - b
    rw [sub_mul, hEi.eq, hbE]
  have hBfix : ∀ n : N, normalizerConjugate K (P : Subgroup G) n B = B := by
    intro n
    rw [map_sub, hEfix n, hbfix n]
  let BN := normalizerAlgebraEmbedding K (P : Subgroup G) B
  let T := relativeTransfer K N BN
  have hBNc : BN ∈ Set.center (MonoidAlgebra K N) :=
    normalizerAlgebraEmbedding_mem_center_of_fixed (R := K) (P : Subgroup G) B hBfix
  have hTc : T ∈ Set.center (MonoidAlgebra K G) := relativeTransfer_mem_center N BN hBNc
  have hBNa : groupAlgebraAugmentation K N BN = 0 :=
    (augmentation_normalizerAlgebraEmbedding (R := K) (P : Subgroup G) B).trans hBaug
  have hTa : groupAlgebraAugmentation K G T = 0 := by
    rw [augmentation_relativeTransfer, hBNa, mul_zero]
  have hrecover : DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G) T = B :=
    sylow_transfer_recovery P B hBfix
  let a := T * e
  have hac : a ∈ Set.center (MonoidAlgebra K G) := Set.mul_mem_center hTc he.1
  have hae : a * e = a := by
    change (T * e) * e = T * e
    rw [mul_assoc, he.2.1.eq]
  have haa : groupAlgebraAugmentation K G a = 0 := by
    rw [map_mul, hTa, zero_mul]
  have haB : DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G) a = B := by
    rw [subgroupCentralizerRestriction_mul_of_mem_center (R := K) (P : Subgroup G) P.isPGroup' T e hTc he.1,
      hrecover]
    exact hBE
  have hnil : IsNilpotent a :=
    PrimitiveCorner.isNilpotent_of_centrallyPrimitive_of_map_eq_zero
      (groupAlgebraAugmentation K G).toRingHom e a he hac hae heaug haa
  let aZ : Subring.center (MonoidAlgebra K G) := ⟨a, hac⟩
  have hnilZ : IsNilpotent aZ := by
    obtain ⟨n, hn⟩ := hnil
    exact ⟨n, Subtype.ext hn⟩
  have hnilB := hnilZ.map (subgroupCentralizerRestrictionOnCenter p K (P : Subgroup G) P.isPGroup')
  change IsNilpotent (DefectSupport.subgroupCentralizerRestriction K (P : Subgroup G) a) at hnilB
  rw [haB] at hnilB
  have hBzero : B = 0 := by
    obtain ⟨n, hn⟩ := hnilB
    rcases n with _ | n
    · simp at hn
    · exact (hBid.pow_eq (Nat.succ_ne_zero n)).symm.trans hn
  have hEq : E = b := sub_eq_zero.mp hBzero
  change IsCentrallyPrimitive E
  rw [hEq]
  exact hb

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
