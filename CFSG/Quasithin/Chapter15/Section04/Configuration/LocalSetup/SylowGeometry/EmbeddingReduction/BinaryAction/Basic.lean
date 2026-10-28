module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Basic
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ModelCases
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.InnerPairCalculation
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# Binary automorphism quotients in the invariant branch of 15.4.20

The actual PSL₄(2) and PSL₅(2) models have outer quotient of order at most two,
hence prime to three. An action containing all inner automorphisms and one
outer automorphism is therefore surjective. The core quotient action of LU
has kernel exactly O₂(LU), using the proved centerlessness of the models.

For PSL₄(2), the permuting Sylow pair and the local irreducibility hypothesis
force an outer action by the existing intrinsic pair calculation. This closes
the full automorphism quotient in dimension four. The corresponding forced
outer action in dimension five remains to be proved; the conditional binary
assembly below does not claim to discharge it.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
1.3.4, printed pp.509–511, and the proof of 15.4.20, printed p.1164.
The arbitrary-field comparison uses the attributed ATLAS port
`Theory.AtlasPort.ExceptionalIsomorphisms.Support`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.BinaryAction
open Chapter1 Chapter1.XiEmbedding.InvariantThree

/-- Identify the arbitrary binary field model with the established linear carrier. -/
theorem binary_linear_equiv {Q : Type*} [Group Q] {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL Q n 2) :
    Nonempty (Q ≃* BinaryLinear.OuterCyclic.LinearGroup n) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let _ := Fintype.ofFinite F
  let f : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact ⟨e.trans ((Atlas.fieldEquivPSL n f.symm).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear hn))⟩

/-- Transport the proved inner/graph coverage through the actual model isomorphism. -/
theorem binary_inner_graph {Q : Type*} [Group Q] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL Q n 2) :
    ∃ τ : MulAut Q, ∀ a : MulAut Q,
      ∃ g : Q, a = MulAut.conj g ∨ a = τ * MulAut.conj g := by
  obtain ⟨e⟩ := binary_linear_equiv (by omega) hm
  let c := MulAut.congr e
  refine ⟨c.symm (BinaryLinear.OuterCyclic.graphLinear n), fun a => ?_⟩
  obtain ⟨g, hg⟩ := BinaryLinear.OuterCyclic.inner_graph hn (c a)
  refine ⟨e.symm g, ?_⟩
  rcases hg with hg | hg
  · left
    apply c.injective
    simpa only [c, MulAut.congr_conj, e.apply_symm_apply] using hg
  · right
    apply c.injective
    simpa only [map_mul, c.apply_symm_apply, c, MulAut.congr_conj,
      e.apply_symm_apply] using hg

/-- The actual Aut/Inn quotient has at most two elements. -/
theorem binary_outer_card_le_two {Q : Type*} [Group Q] {n : ℕ}
    (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL Q n 2) :
    Nat.card (MulAut.Outer Q) ≤ 2 := by
  obtain ⟨τ, hτ⟩ := binary_inner_graph hn hm
  let q := QuotientGroup.mk' (MulAut.innerSubgroup Q)
  let f : Bool → MulAut.Outer Q := fun b => if b then q τ else 1
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup Q) x
    obtain ⟨g, hg⟩ := hτ a
    have hi : q (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    rcases hg with rfl | rfl
    · exact ⟨false, hi.symm⟩
    · refine ⟨true, ?_⟩
      change q τ = q (τ * MulAut.conj g)
      rw [map_mul, hi, mul_one]
  simpa using Nat.card_le_card_of_surjective f hf

/-- The outer-order fact required by the prime-to-three residual argument. -/
theorem binary_outer_prime_to_three {Q : Type*} [Group Q] [Finite Q] {n : ℕ}
    (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL Q n 2) :
    Nat.Coprime 3 (Nat.card (MulAut.Outer Q)) := by
  have hb := binary_outer_card_le_two hn hm
  have hp : 0 < Nat.card (MulAut.Outer Q) := Nat.card_pos
  have hc : Nat.card (MulAut.Outer Q) = 1 ∨ Nat.card (MulAut.Outer Q) = 2 := by omega
  rcases hc with hc | hc <;> rw [hc] <;> decide

/-- All inner automorphisms together with any outer element fill the automorphism group. -/
theorem binary_surjective_of_outer {Q A : Type*} [Group Q] [Group A] {n : ℕ}
    (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL Q n 2)
    (f : A →* MulAut Q) (hi : MulAut.innerSubgroup Q ≤ f.range)
    (ho : ¬ f.range ≤ MulAut.innerSubgroup Q) : Function.Surjective f := by
  obtain ⟨τ, hτ⟩ := binary_inner_graph hn hm
  have ht : τ ∈ f.range := by
    obtain ⟨a, ha, han⟩ := Set.not_subset.mp ho
    obtain ⟨g, hg⟩ := hτ a
    rcases hg with rfl | rfl
    · exact (han ⟨g, rfl⟩).elim
    · simpa only [mul_inv_cancel_right] using
        f.range.mul_mem ha (f.range.inv_mem (hi ⟨g, rfl⟩))
  intro a
  obtain ⟨g, hg⟩ := hτ a
  rcases hg with rfl | rfl
  · exact hi ⟨g, rfl⟩
  · exact f.range.mul_mem ht (hi ⟨g, rfl⟩)

variable {G : Type*} [Group G] {L U : Subgroup G}

/-- Conditional binary assembly: the outer-action premise still needs a source proof. -/
theorem binary_quotient_aut_of_outer {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (XiQuotient L) n 2)
    (hUL : U ≤ normalizer L) (hU : IsPGroup 2 U)
    (ho : ¬ (pCoreJoinAction 2 hUL).range ≤ MulAut.innerSubgroup (XiQuotient L)) :
    Nonempty (XiQuotient (L ⊔ U) ≃* MulAut (XiQuotient L)) := by
  have hc := binary_linear_center_eq_bot (by omega : 0 < n) hm
  have hs := binary_surjective_of_outer hn hm (pCoreJoinAction 2 hUL)
    (inner_le_pCoreJoinAction_range 2 hUL) ho
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (pCoreJoinAction_kernel 2 hUL hU hc).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (pCoreJoinAction 2 hUL) hs)⟩

/-- The source inner-normalizer convention detects a genuine outer element in the image. -/
theorem outer_range_of_not_innerNormalizer (hUL : U ≤ normalizer L)
    (ho : ¬ U ≤ Terminal.innerTwoQuotientNormalizer L) :
    ¬ (pCoreJoinAction 2 hUL).range ≤ MulAut.innerSubgroup (XiQuotient L) := by
  intro hr
  apply ho
  intro u hu
  apply (Terminal.LinearFourActions.mem_innerNormalizer_iff_quotient_action
    (⟨u, hUL hu⟩ : normalizer (L : Set G))).mpr
  obtain ⟨q, hq⟩ := hr (show pCoreJoinAction 2 hUL ⟨u, (show U ≤ L ⊔ U from le_sup_right) hu⟩ ∈
    (pCoreJoinAction 2 hUL).range from ⟨_, rfl⟩)
  exact ⟨q, hq.symm⟩

/-- The permuting Sylow pair forces an outer action in dimension four. -/
theorem four_outer [Finite G] {X P H : Subgroup G}
    (h : XiEmbedding.LocalInput 3 U X P H) (hS : IsSylowIn 2 U H)
    (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) (hXL : X ≤ L)
    (hm : ClassicalGroup.IsPSL (XiQuotient L) 4 2) :
    ¬ (pCoreJoinAction 2 ((le_sup_right.trans h.overgroup).trans
      ((normal_subgroupOf_iff_le_normalizer hLH).mp hLn))).range ≤
        MulAut.innerSubgroup (XiQuotient L) := by
  have hUL : U ≤ normalizer L := (le_sup_right.trans h.overgroup).trans
    ((normal_subgroupOf_iff_le_normalizer hLH).mp hLn)
  have hPL : P ≤ L := (le_sup_right.trans h.complement.le).trans hXL
  apply outer_range_of_not_innerNormalizer hUL
  apply Terminal.LinearFourActions.not_le_innerNormalizer_of_innerPairInvariant h hPL hUL
  obtain ⟨S, hSe⟩ := component_quotient_sylow hS hLH hLn
  rw [← hSe]
  apply Terminal.LinearFourActions.InnerPairCalculation.linearFourInnerPairTheorem
    (XiQuotient L) hm S (XiEmbedding.quotientImage L P)
  · exact h.odd_complement.of_mulEquiv (complementEquiv h hPL)
  · simpa only [← hSe, Sylow.coe_coe] using component_quotient_permute h hPL

/-- The complete dimension-four quotient identification under the local source hypotheses. -/
theorem four_quotient_aut [Finite G] {X P H : Subgroup G}
    (h : XiEmbedding.LocalInput 3 U X P H) (hS : IsSylowIn 2 U H)
    (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) (hXL : X ≤ L)
    (hm : ClassicalGroup.IsPSL (XiQuotient L) 4 2) :
    Nonempty (XiQuotient (L ⊔ U) ≃* MulAut (XiQuotient L)) :=
  binary_quotient_aut_of_outer (Or.inl rfl) hm _ h.two_group
    (four_outer h hS hLH hLn hXL hm)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.BinaryAction
