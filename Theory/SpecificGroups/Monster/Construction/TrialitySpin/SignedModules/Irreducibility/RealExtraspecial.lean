module

public import Mathlib.Data.Real.Basic
public import Theory.ElementaryAbelian.Extraspecial
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Real extraspecial irreducibility by trace duality

An extraspecial group of order `2^25` acting on a real space of dimension
4096 is irreducible if its nonidentity central element acts as minus identity.
Faithfulness need not be assumed for this implication.

For a noncentral element, conjugation multiplies its operator by minus one,
so its trace vanishes. Representatives of the central quotient then give
`2^24` linearly independent operators, as detected by trace against their
inverses. Dimension counting makes them span all endomorphisms. An invariant
subspace is therefore stable under every rank-one operator and is zero or full.
This proof uses neither algebraic closure nor prior irreducibility.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.6, printed pp. 62–63,
and its application to the spin space in Section 27, printed pp. 146–147.
The trace-duality calculation adapts the one in
`Theory.Representation.ExtraspecialFixedPoints`, with its irreducibility
premise replaced by the explicit action of the central involution.
-/

public section

open scoped commutatorElement
open Module
namespace Representation

variable {K V : Type*} [Group K] [Finite K] [IsExtraspecial 2 K]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

omit [Finite K] [FiniteDimensional ℝ V] in
/-- The supplied central sign action forces trace zero off the center. -/
theorem trace_eq_zero_of_extraspecial_two_neg_one (ρ : Representation ℝ K V)
    {z : K} (hz : z ∈ Subgroup.center K) (hz1 : z ≠ 1)
    (hρz : ρ z = -(1 : Module.End ℝ V))
    {x : K} (hx : x ∉ Subgroup.center K) : LinearMap.trace ℝ V (ρ x) = 0 := by
  classical
  rw [Subgroup.mem_center_iff] at hx
  push Not at hx
  obtain ⟨y, hy⟩ := hx
  have hc1 : ⁅y, x⁆ ≠ 1 := fun h => hy (commutatorElement_eq_one_iff_mul_comm.mp h)
  let : IsMulCommutative (K ⧸ Subgroup.center K) :=
    (IsExtraspecial.quotient_elementary_abelian 2 K).toIsMulCommutative
  have hcomm : commutator K ≤ Subgroup.center K :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := Subgroup.center K)).mp inferInstance
  have hc : ⁅y, x⁆ ∈ Subgroup.center K := hcomm
    (Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) (by trivial) (by trivial))
  have hcz : ⁅y, x⁆ = z := by
    obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center K)).mp
      (IsExtraspecial.center_order_p 2 K)
    have h₁ : (⟨⁅y, x⁆, hc⟩ : Subgroup.center K) ≠ 1 := by
      simpa only [ne_eq, Subtype.ext_iff, Subgroup.coe_one] using hc1
    have h₂ : (⟨z, hz⟩ : Subgroup.center K) ≠ 1 := by
      simpa only [ne_eq, Subtype.ext_iff, Subgroup.coe_one] using hz1
    exact congrArg Subtype.val ((hw _ h₁).trans (hw _ h₂).symm)
  have hconj : y * x * y⁻¹ = z * x := by
    rw [← hcz]
    simp [commutatorElement_def, mul_assoc]
  have ht : LinearMap.trace ℝ V (ρ (y * x * y⁻¹)) = LinearMap.trace ℝ V (ρ x) := by
    rw [ρ.map_mul, ρ.map_mul, mul_assoc, LinearMap.trace_mul_comm]
    rw [mul_assoc, ← ρ.map_mul, inv_mul_cancel, ρ.map_one, mul_one]
  rw [hconj, ρ.map_mul, hρz, neg_mul, one_mul, map_neg] at ht
  linarith

/-- The central-coset operators span the entire real endomorphism space. -/
theorem span_range_eq_top_of_extraspecial_two_finrank_4096 (ρ : Representation ℝ K V)
    {z : K} (hz : z ∈ Subgroup.center K) (hz1 : z ≠ 1)
    (hρz : ρ z = -(1 : Module.End ℝ V))
    (hcard : Nat.card K = 2 ^ 25) (hdim : Module.finrank ℝ V = 4096) :
    Submodule.span ℝ (Set.range (ρ : K → Module.End ℝ V)) = ⊤ := by
  classical
  let Q := K ⧸ Subgroup.center K
  let : Fintype Q := Fintype.ofFinite Q
  let b : Q → Module.End ℝ V := fun q => ρ q.out
  have hb : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc s
    let t : Module.End ℝ V →ₗ[ℝ] ℝ :=
      (LinearMap.trace ℝ V).comp (LinearMap.mulRight ℝ (ρ s.out⁻¹))
    have htb (r : Q) : t (b r) = if r = s then (4096 : ℝ) else 0 := by
      change LinearMap.trace ℝ V (ρ r.out * ρ s.out⁻¹) = _
      rw [← ρ.map_mul]
      split_ifs with hrs
      · subst r
        simp [hdim]
      · apply trace_eq_zero_of_extraspecial_two_neg_one ρ hz hz1 hρz
        intro hcenter
        have heq : ((r.out : K) : Q) = ((s.out : K) : Q) :=
          QuotientGroup.eq_iff_div_mem.mpr (by simpa only [div_eq_mul_inv] using hcenter)
        exact hrs (by simpa only [Quotient.out_eq] using heq)
    have ht := congrArg t hc
    simp only [map_sum, map_smul, htb, smul_eq_mul, mul_ite, mul_zero, map_zero] at ht
    rw [Finset.sum_eq_single s] at ht
    · simpa using ht
    · intro r _ hrs
      simp [hrs]
    · simp
  have hcardQ : Fintype.card Q = 16777216 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
    rw [IsExtraspecial.center_order_p 2 K, hcard] at h
    change 2 ^ 25 = Nat.card Q * 2 at h
    rw [Nat.card_eq_fintype_card] at h
    omega
  have hspan : Submodule.span ℝ (Set.range b) = ⊤ := by
    apply hb.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_linearMap, hdim, hcardQ]
  apply top_unique
  rw [← hspan]
  exact Submodule.span_mono (by rintro _ ⟨q, rfl⟩; exact ⟨q.out, rfl⟩)

omit [FiniteDimensional ℝ V] in
/-- Spanning all endomorphisms forces every invariant subspace to be zero or full. -/
theorem isIrreducible_of_span_range_eq_top {G : Type*} [Group G]
    (ρ : Representation ℝ G V) [Nontrivial V]
    (hspan : Submodule.span ℝ (Set.range (ρ : G → Module.End ℝ V)) = ⊤) :
    IsIrreducible ρ := by
  have : Nontrivial (Subrepresentation ρ) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have heq := congrArg Subrepresentation.toSubmodule h
    exact (bot_ne_top : (⊥ : Submodule ℝ V) ≠ ⊤) heq
  constructor
  intro W
  by_cases hW : W.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hW)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    obtain ⟨w, hw, hw0⟩ := W.toSubmodule.ne_bot_iff.mp hW
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℝ hw0
    have hmem : (f.smulRight v) ∈ Submodule.span ℝ (Set.range (ρ : G → Module.End ℝ V)) := by
      rw [hspan]; trivial
    have hstable : ∀ a ∈ Submodule.span ℝ (Set.range (ρ : G → Module.End ℝ V)),
        a w ∈ W.toSubmodule := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem a ha => obtain ⟨g, rfl⟩ := ha; exact W.apply_mem_toSubmodule g hw
      | zero => simp
      | add a b ha hb h₁ h₂ => exact W.toSubmodule.add_mem h₁ h₂
      | smul a b hb h => exact W.toSubmodule.smul_mem a h
    simpa [hf] using hstable _ hmem

/-- The real extraspecial irreducibility implication used for the Parker spin space. -/
theorem isIrreducible_of_extraspecial_two_finrank_4096 (ρ : Representation ℝ K V)
    {z : K} (hz : z ∈ Subgroup.center K) (hz1 : z ≠ 1)
    (hρz : ρ z = -(1 : Module.End ℝ V))
    (hcard : Nat.card K = 2 ^ 25) (hdim : Module.finrank ℝ V = 4096) :
    IsIrreducible ρ := by
  have : Nontrivial V := (Module.finrank_pos_iff (R := ℝ)).mp (by omega)
  exact isIrreducible_of_span_range_eq_top ρ
    (span_range_eq_top_of_extraspecial_two_finrank_4096 ρ hz hz1 hρz hcard hdim)

omit [FiniteDimensional ℝ V] in
/-- Pullback along a surjection preserves irreducibility. -/
theorem isIrreducible_comp_of_surjective {G H : Type*} [Group G] [Group H]
    (ρ : Representation ℝ H V) [IsIrreducible ρ]
    (π : G →* H) (hπ : Function.Surjective π) : IsIrreducible (ρ.comp π) := by
  have : Nontrivial (Subrepresentation (ρ.comp π)) := by
    have : Nontrivial (Submodule ℝ V) :=
      Function.Injective.nontrivial (Subrepresentation.toSubmodule_injective (ρ := ρ))
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    exact (bot_ne_top : (⊥ : Submodule ℝ V) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule h)
  constructor
  intro W
  let W' : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro h v hv
        obtain ⟨g, rfl⟩ := hπ h
        exact W.apply_mem_toSubmodule g hv }
  rcases eq_bot_or_eq_top W' with h | h
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation ρ => U.toSubmodule) h)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation ρ => U.toSubmodule) h)

end Representation
