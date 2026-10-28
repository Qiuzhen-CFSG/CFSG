module
public import Theory.GroupAction.CoprimeFixedCardinality
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Coprime two-perfect actions preserving a quintic line

A two-perfect actor on an abelian group of order 25 that preserves a
subgroup of order five fixes both that line and its quotient, since
Aut(C5) is a two-group. Coprime fixed-point lifting then fixes the whole
plane. The subgroup form retains both literal ambient normalizers.

Source: the terminal quintic-plane exclusion in Aschbacher–Smith
14.5.11, printed pp.1015–1016, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
private theorem automorphisms_five_two {R : Type*} [Group R] [Finite R]
    (hc : Nat.card R = 5) : IsPGroup 2 (MulAut R) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic R := isCyclic_of_prime_card hc
  apply IsPGroup.of_card (n := 2)
  rw [IsCyclic.card_mulAut,hc]
  decide

/-- Coprime fixed-point lifting eliminates the action on the full quintic plane. -/
theorem twoPerfect_coprime_quintic_line_fixed
    {X R : Type*} [Group X] [Finite X] [Group R] [Finite R]
    [MulDistribMulAction X R] [IsMulCommutative R]
    (hX : IsPPerfect 2 X) (hcop : Nat.Coprime (Nat.card X) (Nat.card R))
    (hR : Nat.card R = 25) (C : Subgroup R) [IsInvariant X R C]
    (hC : Nat.card C = 5) : ∀ x : X, ∀ r : R, x • r = r := by
  let : MulDistribMulAction X (R ⧸ C) := quotientMulDistribMulAction C inferInstance
  have hq : Nat.card (R ⧸ C) = 5 := by
    have hh := C.card_mul_index
    rw [C.index_eq_card,hC,hR] at hh
    omega
  have hcfix := hX.hom_eq_one_of_isPGroup (automorphisms_five_two hC)
    (MulDistribMulAction.toMulAut X C)
  have hqfix := hX.hom_eq_one_of_isPGroup (automorphisms_five_two hq)
    (MulDistribMulAction.toMulAut X (R ⧸ C))
  have hCF : C ≤ FixedPoints.subgroup X R := by
    intro c hc x
    have he := congrArg (fun f : X →* MulAut C => f x ⟨c,hc⟩) hcfix
    exact congrArg Subtype.val he
  have hqF : FixedPoints.subgroup X (R ⧸ C) = ⊤ := by
    apply top_unique
    intro r _ x
    exact congrArg (fun f : X →* MulAut (R ⧸ C) => f x r) hqfix
  have hcard := FixedPoints.card_eq_quotient_mul_kernel_of_coprime
    (inferInstance : Group.IsSolvable R) hcop C (inferInstance : IsInvariant X R C)
  rw [hqF,inf_eq_left.mpr hCF,card_top,hq,hC] at hcard
  have htop : FixedPoints.subgroup X R = ⊤ := eq_top_of_card_eq _ (hcard.trans hR.symm)
  intro x r
  exact (show r ∈ FixedPoints.subgroup X R from htop ▸ mem_top r) x

/-- The same assertion on actual normalized subgroups. -/
theorem twoPerfect_coprime_quintic_line_centralizes
    {G : Type*} [Group G] [Finite G]
    (X R C : Subgroup G) [IsMulCommutative R]
    (hX : IsPPerfect 2 X) (hcop : Nat.Coprime (Nat.card X) (Nat.card R))
    (hR : Nat.card R = 25) (hC : Nat.card C = 5) (hCR : C ≤ R)
    (hnR : X ≤ normalizer (R : Set G)) (hnC : X ≤ normalizer (C : Set G)) :
    X ≤ centralizer (R : Set G) := by
  let : MulDistribMulAction X R := conjMulDistribMulActionOfLeNormalizer X R hnR
  let : IsInvariant X R (C.subgroupOf R) := ⟨by
    intro x r
    exact (mem_normalizer_iff.mp (hnC x.property) r)⟩
  have hc : Nat.card (C.subgroupOf R) = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCR).toEquiv).trans hC
  have hh := twoPerfect_coprime_quintic_line_fixed hX hcop hR (C.subgroupOf R) hc
  intro x hx r hr
  have he := congrArg Subtype.val (hh ⟨x,hx⟩ ⟨r,hr⟩)
  change x * r * x⁻¹ = r at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
end Theory.GroupTheory
