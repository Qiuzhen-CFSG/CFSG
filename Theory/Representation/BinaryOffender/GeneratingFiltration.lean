module
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOffender.FlagCodimension
public import Theory.ElementaryAbelian.BinaryRankDifference
import Mathlib.Tactic.Linarith

/-!
# Fixed codimension for a filtration by generators

For invariant binary subspaces W_i, let Z_i be their successive sums and
B_i the actual pointwise kernel on Z_i. A fixed vector in Z + W lies in
Z + C_W(C_B(Z)); the dimension formula for sums yields the key inequality
codim C_(Z+W)(B) >= codim C_Z(B) + codim C_W(C_B(Z)).
Iterating it proves the local-to-global ratio inequality and propagates
equality to every local contribution, including a selected first generator.

The quotient formulation uses log_2 of the literal relative indices, proved
equal to the ranks of the elementary abelian quotients. It allows arbitrary
real q and makes no faithfulness or semisimplicity assumption.

Source: Aschbacher--Smith, D.1.3(a)--(j), printed pp.173--174.
-/

@[expose] public section
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

theorem fixedCodim_sup_ge (Z W : Subrepresentation ρ) (B : Subgroup G) :
    fixedCodim Z.toRepresentation B +
      fixedCodim W.toRepresentation (subspaceKernel ρ Z.toSubmodule B) ≤
        fixedCodim (Z ⊔ W).toRepresentation B := by
  let C := fixedSpace ρ B
  let D := fixedSpace ρ (subspaceKernel ρ Z.toSubmodule B)
  have hZD : Z.toSubmodule ≤ D := le_fixedSpace_subspaceKernel ρ Z.toSubmodule B
  have hcontain : (Z.toSubmodule ⊔ W.toSubmodule) ⊓ C ≤
      Z.toSubmodule ⊔ (W.toSubmodule ⊓ D) := by
    rintro v ⟨hv, hc⟩
    obtain ⟨z, hz, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    apply Submodule.mem_sup.mpr
    refine ⟨z, hz, w, ⟨hw, ?_⟩, rfl⟩
    intro a
    have hh := hc (⟨a, a.property.1⟩ : B)
    change ρ a (z + w) = z + w at hh
    rw [map_add, a.property.2 z hz] at hh
    exact add_left_cancel hh
  have hinf : Z.toSubmodule ⊓ (W.toSubmodule ⊓ D) = Z.toSubmodule ⊓ W.toSubmodule := by
    apply le_antisymm
    · exact inf_le_inf_left _ inf_le_left
    · exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hZD))
  have hdimZW := Z.toSubmodule.finrank_sup_add_finrank_inf_eq W.toSubmodule
  have hdimZD := Z.toSubmodule.finrank_sup_add_finrank_inf_eq (W.toSubmodule ⊓ D)
  rw [hinf] at hdimZD
  have hcap : Z.toSubmodule ⊓ ((Z.toSubmodule ⊔ W.toSubmodule) ⊓ C) =
      Z.toSubmodule ⊓ C := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
  have hsumC := Z.toSubmodule.finrank_sup_add_finrank_inf_eq
    ((Z.toSubmodule ⊔ W.toSubmodule) ⊓ C)
  rw [hcap] at hsumC
  have hle := Submodule.finrank_mono (sup_le (le_sup_left : Z.toSubmodule ≤
    Z.toSubmodule ⊔ (W.toSubmodule ⊓ D)) hcontain)
  have hz := fixedCodim_add_finrank Z.toRepresentation B
  have hw := fixedCodim_add_finrank W.toRepresentation (subspaceKernel ρ Z.toSubmodule B)
  have hzw := fixedCodim_add_finrank (Z ⊔ W).toRepresentation B
  have hez := (subrepresentationFixedEquiv ρ Z B).finrank_eq
  have hew := (subrepresentationFixedEquiv ρ W (subspaceKernel ρ Z.toSubmodule B)).finrank_eq
  have hezw := (subrepresentationFixedEquiv ρ (Z ⊔ W) B).finrank_eq
  change fixedCodim (Z ⊔ W).toRepresentation B + _ =
    Module.finrank (ZMod 2) (Z.toSubmodule ⊔ W.toSubmodule : Submodule (ZMod 2) V) at hzw
  change _ = Module.finrank (ZMod 2) ((Z.toSubmodule ⊔ W.toSubmodule) ⊓ C : Submodule (ZMod 2) V) at hezw
  change _ = Module.finrank (ZMod 2) (W.toSubmodule ⊓ D : Submodule (ZMod 2) V) at hew
  change _ = Module.finrank (ZMod 2) (Z.toSubmodule ⊓ C : Submodule (ZMod 2) V) at hez
  have hzi := Submodule.finrank_mono (inf_le_left : Z.toSubmodule ⊓ C ≤ Z.toSubmodule)
  omega
end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

def generatingSpan (W : ℕ → Subrepresentation ρ) : ℕ → Subrepresentation ρ
  | 0 => ⊥
  | n + 1 => generatingSpan W n ⊔ W n

def generatingKernel (W : ℕ → Subrepresentation ρ) (B : Subgroup G) (n : ℕ) : Subgroup G :=
  subspaceKernel ρ (generatingSpan ρ W n).toSubmodule B

@[simp] theorem generatingKernel_zero (W : ℕ → Subrepresentation ρ) (B : Subgroup G) :
    generatingKernel ρ W B 0 = B := by
  ext b
  change (b ∈ B ∧ ∀ w ∈ (⊥ : Submodule (ZMod 2) V), ρ b w = w) ↔ b ∈ B
  simp

theorem generatingKernel_succ (W : ℕ → Subrepresentation ρ) (B : Subgroup G) (n : ℕ) :
    generatingKernel ρ W B (n + 1) =
      subspaceKernel ρ (W n).toSubmodule (generatingKernel ρ W B n) := by
  ext b
  constructor
  · rintro ⟨hb, hf⟩
    exact ⟨⟨hb, fun z hz => hf z (Submodule.mem_sup_left hz)⟩,
      fun w hw => hf w (Submodule.mem_sup_right hw)⟩
  · rintro ⟨⟨hb, hz⟩, hw⟩
    refine ⟨hb, ?_⟩
    intro x hx
    obtain ⟨z, hz', w, hw', rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hz z hz', hw w hw']

variable [FiniteDimensional (ZMod 2) V]

/-- The full prefix bound and equality propagation, including zero increments. -/
theorem generating_filtration_bound (W : ℕ → Subrepresentation ρ) (B : Subgroup G)
    (q : ℝ) (n : ℕ)
    (hlocal : ∀ i < n, q * ((rank (generatingKernel ρ W B i) : ℝ) -
      rank (generatingKernel ρ W B (i + 1))) ≤
      fixedCodim (W i).toRepresentation (generatingKernel ρ W B i)) :
    q * ((rank B : ℝ) - rank (generatingKernel ρ W B n)) ≤
      fixedCodim (generatingSpan ρ W n).toRepresentation B ∧
    ((fixedCodim (generatingSpan ρ W n).toRepresentation B : ℝ) =
      q * ((rank B : ℝ) - rank (generatingKernel ρ W B n)) →
      ∀ i < n, (fixedCodim (W i).toRepresentation (generatingKernel ρ W B i) : ℝ) =
        q * ((rank (generatingKernel ρ W B i) : ℝ) -
          rank (generatingKernel ρ W B (i + 1)))) := by
  induction n with
  | zero =>
    simp only [generatingKernel_zero, sub_self, mul_zero]
    exact ⟨Nat.cast_nonneg _, fun _ i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ n ih =>
    obtain ⟨hprev, heqprev⟩ := ih (fun i hi => hlocal i (Nat.lt_succ_of_lt hi))
    have hn := hlocal n (Nat.lt_succ_self n)
    have hstep : (fixedCodim (generatingSpan ρ W n).toRepresentation B : ℝ) +
        fixedCodim (W n).toRepresentation (generatingKernel ρ W B n) ≤
          fixedCodim (generatingSpan ρ W (n + 1)).toRepresentation B := by
      exact_mod_cast fixedCodim_sup_ge ρ (generatingSpan ρ W n) (W n) B
    refine ⟨by nlinarith, ?_⟩
    intro he i hi
    have hp : (fixedCodim (generatingSpan ρ W n).toRepresentation B : ℝ) =
        q * ((rank B : ℝ) - rank (generatingKernel ρ W B n)) := by nlinarith
    have hl : (fixedCodim (W n).toRepresentation (generatingKernel ρ W B n) : ℝ) =
        q * ((rank (generatingKernel ρ W B n) : ℝ) -
          rank (generatingKernel ρ W B (n + 1))) := by nlinarith
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact heqprev hp i hi
    · exact hl

/-- An exhaustive generating filtration gives the bound on the original space. -/
theorem generating_filtration_total (W : ℕ → Subrepresentation ρ) (B : Subgroup G)
    (q : ℝ) (n : ℕ) (hgen : generatingSpan ρ W n = ⊤)
    (hlocal : ∀ i < n, q * ((rank (generatingKernel ρ W B i) : ℝ) -
      rank (generatingKernel ρ W B (i + 1))) ≤
      fixedCodim (W i).toRepresentation (generatingKernel ρ W B i)) :
    q * ((rank B : ℝ) - rank (subspaceKernel ρ ⊤ B)) ≤ fixedCodim ρ B ∧
    ((fixedCodim ρ B : ℝ) = q * ((rank B : ℝ) - rank (subspaceKernel ρ ⊤ B)) →
      ∀ i < n, (fixedCodim (W i).toRepresentation (generatingKernel ρ W B i) : ℝ) =
        q * ((rank (generatingKernel ρ W B i) : ℝ) -
          rank (generatingKernel ρ W B (i + 1)))) := by
  have he : fixedCodim (generatingSpan ρ W n).toRepresentation B = fixedCodim ρ B :=
    (fixedCodim_subrepresentation_eq_iff ρ _ B).mpr (by rw [hgen]; exact top_unique le_sup_left)
  have hk : generatingKernel ρ W B n = subspaceKernel ρ ⊤ B := by
    unfold generatingKernel
    rw [hgen]
    rfl
  simpa only [he, hk] using generating_filtration_bound ρ W B q n hlocal

omit [FiniteDimensional (ZMod 2) V] in
/-- Real rank differences agree with the ranks of the literal relative quotients. -/
theorem rank_sub_rank_eq_log_relIndex [Finite G] (B C : Subgroup G)
    [IsElementaryAbelian 2 B] (hCB : C ≤ B) :
    (rank B : ℝ) - rank C = (Nat.log 2 (C.relIndex B) : ℝ) := by
  have hle : rank C ≤ rank B := Nat.log_mono_right (Subgroup.card_le_of_le hCB)
  rw [← Nat.cast_sub hle]
  exact congrArg (Nat.cast : ℕ → ℝ) (Subgroup.log_card_sub_log_card_eq_log_relIndex B C hCB)

/-- First-factor equality applies after any enumeration placing the desired generator first. -/
theorem generating_filtration_first_equality (W : ℕ → Subrepresentation ρ)
    (B : Subgroup G) (q : ℝ) (n : ℕ) (hn : 0 < n)
    (hgen : generatingSpan ρ W n = ⊤)
    (hlocal : ∀ i < n, q * ((rank (generatingKernel ρ W B i) : ℝ) -
      rank (generatingKernel ρ W B (i + 1))) ≤
      fixedCodim (W i).toRepresentation (generatingKernel ρ W B i))
    (heq : (fixedCodim ρ B : ℝ) = q * ((rank B : ℝ) - rank (subspaceKernel ρ ⊤ B))) :
    (fixedCodim (W 0).toRepresentation B : ℝ) =
      q * ((rank B : ℝ) - rank (subspaceKernel ρ (W 0).toSubmodule B)) := by
  have he := (generating_filtration_total ρ W B q n hgen hlocal).2 heq 0 hn
  simpa only [generatingKernel_succ, generatingKernel_zero] using he

/-- Quotient-rank formulation of the generating filtration, for an elementary actor. -/
theorem generating_quotient_bound [Finite G] (W : ℕ → Subrepresentation ρ)
    (B : Subgroup G) [IsElementaryAbelian 2 B] (q : ℝ) (n : ℕ)
    (hgen : generatingSpan ρ W n = ⊤)
    (hlocal : ∀ i < n, q * (Nat.log 2
      ((generatingKernel ρ W B (i + 1)).relIndex (generatingKernel ρ W B i)) : ℝ) ≤
      fixedCodim (W i).toRepresentation (generatingKernel ρ W B i)) :
    q * (Nat.log 2 ((subspaceKernel ρ ⊤ B).relIndex B) : ℝ) ≤ fixedCodim ρ B ∧
    ((fixedCodim ρ B : ℝ) = q * (Nat.log 2 ((subspaceKernel ρ ⊤ B).relIndex B) : ℝ) →
      ∀ i < n, (fixedCodim (W i).toRepresentation (generatingKernel ρ W B i) : ℝ) =
        q * (Nat.log 2
          ((generatingKernel ρ W B (i + 1)).relIndex (generatingKernel ρ W B i)) : ℝ)) := by
  have hstep (i : ℕ) : generatingKernel ρ W B (i + 1) ≤ generatingKernel ρ W B i := by
    rw [generatingKernel_succ]
    exact subspaceKernel_le _ _ _
  have hr (i : ℕ) : (rank (generatingKernel ρ W B i) : ℝ) -
      rank (generatingKernel ρ W B (i + 1)) =
        (Nat.log 2 ((generatingKernel ρ W B (i + 1)).relIndex
          (generatingKernel ρ W B i)) : ℝ) := by
    let _ : IsElementaryAbelian 2 (generatingKernel ρ W B i) :=
      IsElementaryAbelian.of_le (subspaceKernel_le ρ _ B)
    exact rank_sub_rank_eq_log_relIndex _ _ (hstep i)
  have ht := rank_sub_rank_eq_log_relIndex B (subspaceKernel ρ ⊤ B)
    (subspaceKernel_le ρ ⊤ B)
  simpa only [hr, ht] using generating_filtration_total ρ W B q n hgen
    (fun i hi => (hr i) ▸ hlocal i hi)

/-- If the desired generator is first, equality is measured on that generator
and its original B-action. No faithful action on the ambient space is assumed. -/
theorem generating_quotient_first_equality [Finite G] (W : ℕ → Subrepresentation ρ)
    (B : Subgroup G) [IsElementaryAbelian 2 B] (q : ℝ) (n : ℕ) (hn : 0 < n)
    (hgen : generatingSpan ρ W n = ⊤)
    (hlocal : ∀ i < n, q * (Nat.log 2
      ((generatingKernel ρ W B (i + 1)).relIndex (generatingKernel ρ W B i)) : ℝ) ≤
      fixedCodim (W i).toRepresentation (generatingKernel ρ W B i))
    (heq : (fixedCodim ρ B : ℝ) =
      q * (Nat.log 2 ((subspaceKernel ρ ⊤ B).relIndex B) : ℝ)) :
    (fixedCodim (W 0).toRepresentation B : ℝ) =
      q * (Nat.log 2 ((subspaceKernel ρ (W 0).toSubmodule B).relIndex B) : ℝ) := by
  have h := (generating_quotient_bound ρ W B q n hgen hlocal).2 heq 0 hn
  simpa only [generatingKernel_succ, generatingKernel_zero] using h

end Representation.BinaryOffender
