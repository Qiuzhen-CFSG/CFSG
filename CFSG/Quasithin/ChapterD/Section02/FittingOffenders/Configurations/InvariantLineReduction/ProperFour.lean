module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.InvariantLineReduction.Supports
public import Theory.GroupAction.HyperplaneCommutatorGeneration
public import Theory.Representation.BinaryOffender.UniformFixedSpace

/-!
# Excluding a proper four-dimensional invariant-line support

The support calculations spend three of the four available fixed
codimensions. A nonzero complement therefore has fixed codimension one.
Its action kernel in the four-group is nontrivial.

To prove this, we exclude a faithful action directly. Faithfulness makes all three involutions
have the same fixed hyperplane. Each involution centralizer in the odd
core preserves that hyperplane, so coprime hyperplane generation makes it
core-invariant. Since the actor fixes it and [P,A]=P, the core fixes it too.
Full movement by the core makes the hyperplane zero; the resulting module
of dimension at most one cannot admit a faithful involution. A nonidentity
kernel element then gives an order-two actor fixing the complement and
moving at most two dimensions on the four-dimensional support. Its ratio
contradicts starred minimality.

This proves the proper-four exclusion of Aschbacher--Smith, D.2.14,
printed p.187. It replaces the printed remainder-plane calculation by a
common-fixed-hyperplane obstruction. No dimension or action kernel for the
remainder is assumed. The final application uses the literal faithful
image on the original complement, with both subgroup images and the core
commutator transported explicitly.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
open Representation.BinaryOffender Subgroup
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

private theorem no_faithful_four_coatom (hf : Function.Injective ρ)
    (P A : Subgroup G) (hP : IsPGroup 3 P) (hA : IsElementaryTwo A)
    (hcA : Nat.card A = 4) (hPA : ⁅P, A⁆ = P)
    (hm : subspaceCommutator ρ ⊤ P = ⊤) (hd : fixedCodim ρ A ≤ 1) : False := by
  let : IsElementaryAbelian 2 A := hA.2
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let F := fixedSpace ρ A
  let S := subspaceStabilizer ρ F
  have hAS : A ≤ S := fixedSpace_subactor_stabilized ρ hA le_rfl
  have hgen := iSup_hyperplane_centralizer_commutator (by decide : 3 ≠ 2) P A hP
    (le_normalizer_iff_commutator_le_left.mpr hPA.le)
  have hPS : P ≤ S := by
    rw [← hPA, ← hgen]
    apply iSup₂_le
    intro B hB
    let B₀ := B.map A.subtype
    have hBA : B₀ ≤ A := map_subtype_le B
    have hcard : Nat.card B₀ = 2 := by
      have hh := B.card_mul_index
      rw [hB, hcA] at hh
      have hmap : Nat.card B₀ = Nat.card B := card_map_of_injective A.subtype_injective
      omega
    have hBn : B₀ ≠ ⊥ := by intro he; rw [he, card_bot] at hcard; omega
    have hpos := fixedCodim_pos_of_faithful ρ hf hBn
    have hle := Submodule.finrank_mono (fixedSpace_antitone ρ hBA)
    have ha := fixedCodim_add_finrank ρ A
    have hb := fixedCodim_add_finrank ρ B₀
    have he : fixedSpace ρ B₀ = F :=
      (fixedSpace_eq_of_fixedCodim_eq ρ hBA (by omega)).symm
    have hCS : P ⊓ centralizer (B₀ : Set G) ≤ S := by
      dsimp only [S]
      rw [← he]
      exact fixedSpace_invariant_normalizer ρ
        (inf_le_right.trans (centralizer_le_normalizer _))
    apply commutator_le.mpr
    intro p hp a ha
    exact S.mul_mem (S.mul_mem (S.mul_mem (hCS hp) (hAS ha)) (S.inv_mem (hCS hp)))
      (S.inv_mem (hAS ha))
  have hFP : F ≤ fixedSpace ρ P := by
    rw [← hPA]
    exact le_fixedSpace_commutator_of_invariant ρ hPS le_rfl
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hc := odd_fixed_moved_complement ρ (hn ▸ (by decide : Odd 3).pow)
  have hF : F = ⊥ := le_bot_iff.mp (by
    intro v hv
    have hu : v ∈ subspaceCommutator ρ ⊤ P := by rw [hm]; trivial
    exact hc.disjoint.le_bot ⟨hu, hFP hv⟩)
  have hvdim : Module.finrank (ZMod 2) V ≤ 1 := by
    have hh := fixedCodim_add_finrank ρ A
    change fixedCodim ρ A + Module.finrank (ZMod 2) F = _ at hh
    rw [hF, finrank_bot, add_zero] at hh
    omega
  obtain ⟨a, ha, han⟩ := (Subgroup.nontrivial_iff_exists_ne_one A).mp
    ((Subgroup.nontrivial_iff_ne_bot A).mpr hA.1)
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) han
  have hne : zpowers a ≠ ⊥ := by
    intro he
    exact han (he.le (mem_zpowers a))
  have hpos := fixedCodim_pos_of_faithful ρ hf hne
  have hhalf := (involution_actor_rank_and_fixedCodim ρ a ho).2.2.2
  omega

/-- Coprime hyperplane generation forces a nontrivial kernel on the complement
of a proper four-dimensional support. No remainder dimension is assumed. -/
theorem Reduced.proper_four_remainder_kernel_ne_bot {P A Z : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hZ : IsInvariantLine P A Z)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 4)
    (hp : subspaceCommutator ρ ⊤ Z ≠ ⊤) :
    subspaceKernel ρ (fixedSpace ρ Z) A ≠ ⊥ := by
  intro hker
  let W := fixedSpace ρ Z
  let σ := subspaceImageRepresentation ρ W
  let P' := restrictedSubgroup ρ W P
  let A' := restrictedSubgroup ρ W A
  have hst := (h.invariant_line_stable ρ hZ).2
  have hPst : P ≤ subspaceStabilizer ρ W := le_top.trans hst
  have hAst : A ≤ subspaceStabilizer ρ W := le_top.trans hst
  have hcA : Nat.card A' = 4 := by
    have hc := card_subspaceKernel_mul_image ρ W A hAst
    rw [hker, card_bot, one_mul, h.card_actor] at hc
    exact hc
  have hnon : ¬ W ≤ fixedSpace ρ A := h.invariant_line_remainder_noncentral ρ hZ hp
  have hA' : IsElementaryTwo A' := h.starred.1.2.1.restrictedSubgroup ρ W hAst hnon
  let : IsElementaryAbelian 3 P := h.elementary
  have hP' : IsPGroup 3 P' := by
    change IsPGroup 3 ((P.subgroupOf (subspaceStabilizer ρ W)).map (subspaceActionHom ρ W))
    exact ((IsElementaryAbelian.isPGroup 3 P).comap_subtype).map _
  have hm : subspaceCommutator σ ⊤ P' = ⊤ := restricted_commutator_eq_top ρ W P hPst
    (h.invariant_line_remainder_moved ρ hZ)
  have hcomm : ⁅P', A'⁆ = P' := restrictedSubgroup_commutator ρ W hPst hAst h.core_commutator
  exact no_faithful_four_coatom σ (subspaceImageRepresentation_injective ρ W) P' A' hP' hA'
    hcA hcomm hm (h.invariant_line_remainder_budget ρ hZ hd).2

/-- The actual small order-two subactor in the proper-four branch is constructed
from the complement kernel, with its bound on the original representation. -/
theorem Reduced.proper_four_small_subactor {P A Z : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hZ : IsInvariantLine P A Z)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 4)
    (hp : subspaceCommutator ρ ⊤ Z ≠ ⊤) :
    ∃ C : Subgroup G, C ≤ A ∧ Nat.card C = 2 ∧
      fixedSpace ρ Z ≤ fixedSpace ρ C ∧ fixedCodim ρ C ≤ 2 := by
  obtain ⟨c, hc, hcn⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).mp
    ((Subgroup.nontrivial_iff_ne_bot _).mpr (h.proper_four_remainder_kernel_ne_bot ρ hZ hd hp))
  let : IsElementaryAbelian 2 A := h.starred.1.2.1.2
  have ho : orderOf c = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian c hc.1) hcn
  have hC : Nat.card (zpowers c) = 2 := (Nat.card_zpowers c).trans ho
  have hf : fixedSpace ρ Z ≤ fixedSpace ρ (zpowers c) := by
    intro v hv
    exact (mem_fixedSpace_zpowers_iff ρ c v).mpr (hc.2 v hv)
  exact ⟨zpowers c, zpowers_le.mpr hc.1, hC, hf, h.four_support_subactor_bound ρ hZ hd hC hf⟩

/-- A proper four-dimensional invariant-line support is impossible: its
constructed order-two subactor violates the strict minimality inequality. -/
theorem Reduced.no_proper_four_support {P A Z : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hZ : IsInvariantLine P A Z)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 4) :
    subspaceCommutator ρ ⊤ Z = ⊤ := by
  by_contra hp
  obtain ⟨C, hCA, hC, _, hb⟩ := h.proper_four_small_subactor ρ hZ hd hp
  exact h.no_codim_four_with_small_subactor ρ hCA hC hb (h.proper_four_codimension ρ hZ hd hp)

end CFSG.Quasithin.ChapterD.FittingConfigurations
