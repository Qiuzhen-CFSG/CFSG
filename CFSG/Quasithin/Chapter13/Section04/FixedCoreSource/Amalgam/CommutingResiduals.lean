module
public import Theory.GroupTheory.PResidual.PrimeToNormalizerImage
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual
public import Theory.GroupTheory.SymmetricThreeTwoCoreResidual
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The product branch of the original amalgam

When the two residual images commute, a coprime action kernel normalizing
both residuals lets their mutual normalization lift. The common Sylow
supplement then makes both residuals normal in the whole join. The local
kernel bounds place their commutator in both residual two-cores, and
residual generation gives the literal product of the original vertices.

This is the group-theoretic part of case (i) in Aschbacher–Smith 13.4.7,
printed p.900. It retains the possibly odd action kernel; its hypotheses
are discharged for the original pairs in CommutingAction. No structural
alternative or model-recognition conclusion is assumed.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

private theorem local_residual_primeTo_top
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) :
    primeToResidual 3 ((pResidual 2 A).map A.subtype) = ⊤ := by
  rw [←twoResidual_eq_primeToResidual_three
    ((SymmetricThreeTwoCore.twoThree_of_quotient e).of_injective
      (inclusion (map_subtype_le (pResidual 2 A))) (inclusion_injective _))]
  exact (pResidual_eq_top_iff 2 _).mpr (isPPerfect_embedded_pResidual 2 A)

/-- The commuting branch retains the full, possibly odd, action kernel. -/
theorem commuting_residuals
    (hg : ChapterF.IsGoldschmidtTriple A B) (N : Subgroup G) [N.Normal]
    (hcop : Nat.Coprime 3 (Nat.card N))
    (hnA : N ≤ normalizer ((pResidual 2 A).map A.subtype : Set G))
    (hnB : N ≤ normalizer ((pResidual 2 B).map B.subtype : Set G))
    (hAN : A ⊓ N ≤ A.pCoreIn 2) (hBN : B ⊓ N ≤ B.pCoreIn 2)
    (hc : ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤ N) :
    let K₁ := (pResidual 2 A).map A.subtype
    let K₂ := (pResidual 2 B).map B.subtype
    K₁.Normal ∧ K₂.Normal ∧ ⁅K₁,K₂⁆ ≤ K₁.pCoreIn 2 ⊓ K₂.pCoreIn 2 ∧
      (Set.univ : Set G) = (A : Set G) * (B : Set G) := by
  let K₁ := (pResidual 2 A).map A.subtype
  let K₂ := (pResidual 2 B).map B.subtype
  let f := QuotientGroup.mk' N
  have hcop' : Nat.Coprime 3 (Nat.card f.ker) := by
    simpa only [f,QuotientGroup.ker_mk'] using hcop
  have hc' : ⁅K₁.map f,K₂.map f⁆ = ⊥ := by
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hc
  have hnorm (P Q : Subgroup G) (hp : primeToResidual 3 P = ⊤)
      (hn : N ≤ normalizer (P : Set G)) (hcomm : ⁅P.map f,Q.map f⁆ = ⊥) :
      Q ≤ normalizer (P : Set G) := by
    apply (map_le_normalizer_map_iff_of_primeToResidual 3 f P Q hp hcop'
      (by simpa only [f,QuotientGroup.ker_mk'] using hn)).mp
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      (centralizer_le_normalizer _)
  have hn₂₁ := hnorm K₁ K₂ (local_residual_primeTo_top hg.quotient_left.some) hnA hc'
  have hn₁₂ := hnorm K₂ K₁ (local_residual_primeTo_top hg.quotient_right.some) hnB
    (by simpa only [commutator_comm] using hc')
  have hnB₁ : B ≤ normalizer (K₁ : Set G) := by
    rw [←hg.right_residual_sup_intersection]
    exact sup_le hn₂₁ hg.intersection_normalizes_left_residual
  have hnA₂ : A ≤ normalizer (K₂ : Set G) := by
    rw [←hg.left_residual_sup_intersection]
    exact sup_le hn₁₂ hg.intersection_normalizes_right_residual
  have hn₁ : K₁.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←hg.left_residual_sup_right]
    exact sup_le K₁.le_normalizer hnB₁
  have hn₂ : K₂.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←hg.symm.left_residual_sup_right]
    exact sup_le K₂.le_normalizer hnA₂
  have hbound (P Q Y : Subgroup G) (hPY : P ≤ Y)
      (hn : Q ≤ normalizer (P : Set G))
      (hc : ⁅P,Q⁆ ≤ N) (hl : Y ⊓ N ≤ Y.pCoreIn 2) : ⁅P,Q⁆ ≤ P.pCoreIn 2 := by
    have hPN : (N.subgroupOf P).map P.subtype ≤ Y.pCoreIn 2 := by
      rintro x ⟨y,hy,rfl⟩
      exact hl ⟨hPY y.property,hy⟩
    have hp : IsPGroup 2 (N.subgroupOf P) :=
      ((isPGroup_pCoreIn 2 Y).of_injective (inclusion hPN) (inclusion_injective _)).of_injective
        ((N.subgroupOf P).equivMapOfInjective P.subtype P.subtype_injective).toMonoidHom
        ((N.subgroupOf P).equivMapOfInjective P.subtype P.subtype_injective).injective
    have hcore : N.subgroupOf P ≤ pCore 2 P := le_sSup ⟨inferInstance,hp⟩
    intro x hx
    exact mem_map_of_mem P.subtype (hcore
      (show (⟨x,le_normalizer_iff_commutator_le_left.mp hn hx⟩ : P) ∈ N.subgroupOf P from hc hx))
  refine ⟨hn₁,hn₂,le_inf (hbound K₁ K₂ A (map_subtype_le _) hn₂₁ hc hAN)
    (by
      rw [commutator_comm]
      exact hbound K₂ K₁ B (map_subtype_le _) hn₁₂
        (by simpa only [commutator_comm] using hc) hBN),?_⟩
  let := hn₁
  apply Set.Subset.antisymm ?_ (Set.subset_univ _)
  have he : (Set.univ : Set G) = (K₁ : Set G) * (B : Set G) := by
    rw [←normal_mul,hg.left_residual_sup_right]
    rfl
  rw [he]
  exact Set.mul_subset_mul (map_subtype_le _) (Set.Subset.refl _)
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
