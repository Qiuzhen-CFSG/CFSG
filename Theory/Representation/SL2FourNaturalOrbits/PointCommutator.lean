module
public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The field point moved by a natural SL₂(4) Borel

The diagonal cubic moves the binary point fixed by the upper root group and
Frobenius onto the complete F₄-line. A nontrivial upper root has this same
line as its displacement image. The proofs use two explicit displacements;
they do not enumerate subgroups of SL₂(4).

Source application: Aschbacher–Smith, combined 1 March 2004 manuscript,
Lemma 14.4.10, printed pp.1010–1011. The source must mark its actual Borel
and root subgroup before using these model calculations.
-/

@[expose] public section
namespace Representation.SL2FourNatural.PointCommutator
open Representation.SL2FourNatural Representation.BinaryOffender

abbrev Bit := ZMod 2

def representation : Representation Bit SL V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp action

/-- The binary point fixed by the upper root group and field automorphism. -/
def point : Submodule Bit V := upperFixed ⊓ fieldFixed

/-- The diagonal element of order three in the upper triangular Borel. -/
def cubic : SL :=
  ⟨!![QuadraticAlgebra.omega, 0; 0, QuadraticAlgebra.omega ^ 2], by decide +kernel⟩

theorem cubic_pow_three : cubic ^ 3 = 1 := by decide +kernel

theorem point_card : Nat.card point = 2 := card_upperFixed_inf_fieldFixed

theorem fieldPoint_card : Nat.card upperFixed = 4 := card_upperFixed

/-- The calculated binary plane is the restriction of a one-dimensional
F₄-subspace. -/
theorem fieldPoint_isFieldLine : IsFieldLine upperFixed := by
  let W := Submodule.span F {(![1, 0] : V)}
  have hn : (![1, 0] : V) ≠ 0 := by
    intro he
    have := congrFun he 0
    simp at this
  refine ⟨W, ?_, ?_⟩
  · exact finrank_span_singleton hn
  · ext v
    change v ∈ W ↔ v ∈ upperFixed
    rw [mem_upperFixed]
    constructor
    · intro hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      simp
    · intro hv
      apply Submodule.mem_span_singleton.mpr
      refine ⟨v 0, ?_⟩
      funext i
      fin_cases i <;> simp [hv]

private theorem basis_mem_point : (![1, 0] : V) ∈ point := by
  constructor
  · exact (mem_upperFixed _).mpr rfl
  · apply (mem_fieldFixed _).mpr
    intro i
    fin_cases i <;> simp

private theorem fieldPoint_generated : ∀ v : V, v 1 = 0 →
    v = 0 ∨ v = representation cubic ![1, 0] - ![1, 0] ∨
    v = representation (cubic ^ 2) ![1, 0] - ![1, 0] ∨
    v = (representation cubic ![1, 0] - ![1, 0]) +
      (representation (cubic ^ 2) ![1, 0] - ![1, 0]) := by
  decide +kernel

/-- Every Borel actor containing the diagonal cubic moves the binary point
onto the full F₄-point. -/
theorem point_commutator (A : Subgroup SL)
    (hA : A ≤ subspaceStabilizer representation upperFixed) (hc : cubic ∈ A) :
    subspaceCommutator representation point A = upperFixed := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨a, ha, w, hw, rfl⟩
    exact upperFixed.sub_mem ((hA ha w).2 hw.1) hw.1
  · intro v hv
    have h₁ : representation cubic ![1, 0] - ![1, 0] ∈
        subspaceCommutator representation point A :=
      Submodule.subset_span ⟨cubic, hc, ![1, 0], basis_mem_point, rfl⟩
    have h₂ : representation (cubic ^ 2) ![1, 0] - ![1, 0] ∈
        subspaceCommutator representation point A :=
      Submodule.subset_span ⟨cubic ^ 2, A.pow_mem hc 2, ![1, 0], basis_mem_point, rfl⟩
    rcases fieldPoint_generated v ((mem_upperFixed _).mp hv) with rfl | rfl | rfl | rfl
    · exact Submodule.zero_mem _
    · exact h₁
    · exact h₂
    · exact Submodule.add_mem _ h₁ h₂

/-- A chosen preimage for every displacement in the F₄-point. -/
theorem fieldPoint_displacement (v : V) (hv : v ∈ upperFixed) :
    representation (upper 1) (![0, v 0] : V) - ![0, v 0] = v := by
  have hv1 := (mem_upperFixed v).mp hv
  change action (upper 1) _ - _ = _
  rw [upper_action]
  funext i
  fin_cases i <;> simp [hv1]

/-- A nontrivial upper root moves the natural module onto the same F₄-point. -/
theorem fieldPoint_le_root_commutator (R : Subgroup SL) (hR : upper 1 ∈ R) :
    upperFixed ≤ subspaceCommutator representation ⊤ R := by
  intro v hv
  rw [← fieldPoint_displacement v hv]
  exact Submodule.subset_span ⟨upper 1, hR, ![0, v 0], Submodule.mem_top, rfl⟩

end Representation.SL2FourNatural.PointCommutator
