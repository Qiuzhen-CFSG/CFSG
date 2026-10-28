module

public import CFSG.Quasithin.ChapterF.Section06.Elementary
public import CFSG.Quasithin.ClassicalModels
public import BenderSuzuki.MatrixGroups.PSL28Facts
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Theory.SpecificGroups.PSL2.RankOneRoots
public import Theory.SpecificGroups.PSL2.EightCentralCovers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
/-!
# The PSL₂(8) exception in the cyclic component branch

The centralizer of each cubic element in the concrete PSL₂(8) has order
nine. Its cyclic subgroup therefore has normalizer with two-part at most
two, whereas a Sylow two-subgroup has order divisible by four. This rules
out the original cubic local residual inside a component of that model.
The constructed trivial universal cover passes the exclusion to the
component's actual central quotient. Field transport also handles the
source's field-independent model predicate at parameter eight.

Source: Aschbacher–Smith, F.6.17, printed p.309; I.1.3, printed p.407.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.SourceAssembly

private theorem four_not_dvd_cubic_normalizer_of_odd_centralizer
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) (hA : Nat.card A = 3)
    (hodd : Odd (Nat.card (centralizer (A : Set G)))) :
    ¬ 4 ∣ Nat.card (normalizer (A : Set G)) := by
  let : IsCyclic A := isCyclic_of_prime_card hA
  have hAut : Nat.card (MulAut A) = 2 := by
    rw [IsCyclic.card_mulAut, hA]
    decide
  let f := A.normalizerMonoidHom
  have hrange : Nat.card f.range ∣ 2 := hAut ▸ f.range.card_subgroup_dvd_card
  have hker : Odd (Nat.card f.ker) := by
    have heq : Nat.card f.ker = Nat.card (centralizer (A : Set G)) := by
      rw [normalizerMonoidHom_ker,
        Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (A : Set G))).toEquiv]
    rwa [heq]
  have hprod := f.ker.card_mul_index
  rw [index_ker] at hprod
  intro hfour
  have hdiv : 4 ∣ Nat.card f.range := by
    apply (hker.coprime_two_left.pow_left 2).dvd_of_dvd_mul_left
    simpa only [hprod] using hfour
  have := dvd_trans hdiv hrange
  norm_num at this

private theorem psl28_card : Nat.card (PSL2BinaryMatrixGroup 3) = 504 := by
  have hgroup := BenderSuzuki.External.huppert614_card_psl_mul_center (K := BinaryGaloisField 3)
  simp only [BenderSuzuki.Converse.center_SL2_eq_bot, Nat.card_eq_fintype_card,
    Fintype.card_unique, mul_one] at hgroup
  have hF : Nat.card (BinaryGaloisField 3) = 8 := by
    exact GaloisField.card 2 3 (by decide)
  rw [hF] at hgroup
  norm_num at hgroup
  exact hgroup

/-- The order-nine cubic centralizer excludes a Sylow two-subgroup from its normalizer. -/
theorem psl28_sylow_not_normalizes_cubic
    (S : Sylow 2 (PSL2BinaryMatrixGroup 3)) (A : Subgroup (PSL2BinaryMatrixGroup 3))
    (hA : Nat.card A = 3) : ¬ (S : Subgroup (PSL2BinaryMatrixGroup 3)) ≤ normalizer (A : Set (PSL2BinaryMatrixGroup 3)) := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 (by rw [hA])
  have haG : orderOf (a : PSL2BinaryMatrixGroup 3) = 3 := (orderOf_coe a).trans ha
  have hc : Nat.card (centralizer (A : Set (PSL2BinaryMatrixGroup 3))) ∣ 9 := by
    rw [← (psl28_orderThree_centralizer_cyclic_order_nine a haG).1]
    exact card_dvd_of_le (centralizer_le (Set.singleton_subset_iff.mpr a.property))
  have ho : Odd (Nat.card (centralizer (A : Set (PSL2BinaryMatrixGroup 3)))) := (by decide : Odd 9).of_dvd_nat hc
  intro hSA
  apply four_not_dvd_cubic_normalizer_of_odd_centralizer A hA ho
  exact (S.pow_dvd_card_of_pow_dvd_card (n := 2) (by rw [psl28_card]; decide)).trans
    (card_dvd_of_le hSA)


variable {G : Type*} [Group G] [Finite G] {G₁ G₂ K : Subgroup G}

/-- Transport the cubic normalizer exclusion through the original model isomorphism. -/
theorem not_psl_two_eight_of_sylow_normalizes_cubic
    (S : Sylow 2 G) (A : Subgroup G) (hA : Nat.card A = 3)
    (hSA : (S : Subgroup G) ≤ normalizer (A : Set G)) :
    ¬ Nonempty (G ≃* PSL2BinaryMatrixGroup 3) := by
  rintro ⟨e⟩
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  apply psl28_sylow_not_normalizes_cubic T (A.map e.toMonoidHom)
    ((card_map_of_injective e.injective).trans hA)
  change (S : Subgroup G).map e.toMonoidHom ≤ _
  rw [← map_equiv_normalizer_eq A e]
  exact map_mono hSA

/-- The original local cubic residual rules out PSL₂(8) for its component. -/
theorem component_not_psl_two_eight_of_left_residual_cubic
    (h : IsGoldschmidtTriple G₁ G₂) (hK : IsComponent G K)
    (hL : (pResidual 2 G₁).map G₁.subtype ≤ K)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    ¬ Nonempty (K ≃* PSL2BinaryMatrixGroup 3) := by
  let A := (pResidual 2 G₁).map G₁.subtype
  obtain ⟨S, hS⟩ := h.subnormal_intersection_sylow K hK.1
  apply not_psl_two_eight_of_sylow_normalizes_cubic S (A.subgroupOf K)
    ((Nat.card_congr (subgroupOfEquivOfLe hL).toEquiv).trans hc)
  apply le_normalizer_iff.mpr
  intro s hs a ha
  change (s : G) * (a : G) * (s : G)⁻¹ ∈ A
  rw [hS] at hs
  exact (mem_normalizer_iff.mp (h.intersection_normalizes_left_residual hs) (a : G)).mp ha

/-- The constructed universal cover of PSL₂(8) is trivial, so the same
exclusion holds for the actual component's central quotient. -/
theorem central_quotient_not_psl_two_eight_of_left_residual_cubic
    (h : IsGoldschmidtTriple G₁ G₂) (hK : IsComponent G K)
    (hL : (pResidual 2 G₁).map G₁.subtype ≤ K)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    ¬ Nonempty ((K ⧸ center K) ≃* PSL2BinaryMatrixGroup 3) := by
  rintro ⟨j⟩
  let : IsQuasisimple K := hK.2
  exact component_not_psl_two_eight_of_left_residual_cubic h hK hL hc
    ⟨Theory.SpecificGroups.PSL2Eight.coverEquiv (PerfectCentralCovering.centralQuotientCover j)⟩

/-- The field-independent source model at q=8 is excluded as well. -/
theorem central_quotient_not_psl_eight_model_of_left_residual_cubic
    (h : IsGoldschmidtTriple G₁ G₂) (hK : IsComponent G K)
    (hL : (pResidual 2 G₁).map G₁.subtype ≤ K)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 8 := by
  rintro ⟨F, _, _, hF, ⟨j⟩⟩
  let := Fintype.ofFinite F
  let := Fintype.ofFinite (BinaryGaloisField 3)
  let eF : F ≃+* BinaryGaloisField 3 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF]
    exact (GaloisField.card 2 3 (by decide)).symm)
  exact central_quotient_not_psl_two_eight_of_left_residual_cubic h hK hL hc
    ⟨j.trans (Atlas.fieldEquivPSL 2 eF)⟩
end CFSG.Quasithin.ChapterF.SourceAssembly
