module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.HomogeneousCoordinates

/-!
# Exact natural multiplicities and the binary source bound

Rank-nullity along the literal natural chief flag gives dimension i*n at its
ith term and length*n for the full action. Thus an independently constructed
repeated-natural chart has multiplicity exactly i. The original offender's
ratio budget, together with the proved lower bound 1/(n-1) on each factor,
bounds the full length by n-1 in both binary source families.

Source: Aschbacher--Smith, B.5.1, pp.100--102, inequalities (*) and (++),
and the bound on r in the final binary branch.
-/

public section
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped MatrixGroups BigOperators ENNReal
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- Every binary-natural factor contributes its actual natural dimension.
The dimension identity holds at each term, not just at the full module. -/
theorem binary_natural_flag_dimensions (C : Subgroup G) (f : ReducibleChiefFlag ρ C)
    {d : ℕ} (hn : ∀ i < f.length, IsLinearNatural
      ((sectionRepresentation ρ (f.chain i) (f.chain (i+1))).comp C.subtype) BinaryField.two d) :
    (∀ i ≤ f.length, Module.finrank (ZMod 2) (f.chain i).toSubmodule = i*d) ∧
      Module.finrank (ZMod 2) V = f.length*d := by
  have hs (i : ℕ) (hi : i < f.length) : sectionDimension ρ (f.chain i) (f.chain (i+1)) = d := by
    obtain ⟨a⟩ := hn i hi
    have he := a.linearEquiv.finrank_eq
    change sectionDimension ρ (f.chain i) (f.chain (i+1)) =
      Module.finrank (ZMod 2) (Fin d → ZMod 2) at he
    simpa using he
  have hall (i : ℕ) (hi : i ≤ f.length) :
      Module.finrank (ZMod 2) (f.chain i).toSubmodule = i*d := by
    induction i with
    | zero =>
      rw [f.bottom]
      change Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) V) = 0*d
      simp
    | succ i ih =>
      have hb := sectionDimension_add ρ (f.chain i) (f.chain (i+1)) (f.monotone (by omega))
      rw [hs i (by omega),ih (by omega)] at hb
      simpa [Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.add_comm] using hb.symm
  refine ⟨hall,?_⟩
  have ht := hall f.length le_rfl
  rw [f.top] at ht
  change Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) = f.length*d at ht
  simpa using ht

/-- The source ratio budget bounds the full number of natural factors by
n-1; all central factors have already been eliminated. -/
theorem binary_source_flag_length [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : generalizedFitting G ≃* SL(d,ZMod 2))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hindices : f.noncentral = Finset.range f.length) : f.length ≤ d-1 := by
  classical
  let q := fun i => quadraticRatio (imageRepresentation (sectionRepresentation ρ (f.chain i) (f.chain (i+1))))
  have hb := f.estimates ρ hf inferInstance hcore A hA
  have hl (i : ℕ) (hi : i ∈ f.noncentral) : 1 / (d-1 : ℕ) ≤ q i :=
    binary_flag_ratio_lower ρ hK earlier hsq hcore hd mark f hi ((hb.2.2.1 i hi).2.le)
  have hsum : (f.noncentral.card : ℝ≥0∞) * (1 / (d-1 : ℕ)) ≤ 1 := by
    calc
      _ = ∑ i ∈ f.noncentral, (1 / (d-1 : ℕ) : ℝ≥0∞) := by simp
      _ ≤ ∑ i ∈ f.noncentral, q i := Finset.sum_le_sum hl
      _ ≤ 1 := hb.2.1
  have hr := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hsum
  rw [hindices,Finset.card_range] at hr
  rcases hd with rfl | rfl
  · norm_num [ENNReal.toReal_mul,ENNReal.toReal_div] at hr ⊢
    exact_mod_cast (by linarith : (f.length : ℝ) ≤ 3)
  · norm_num [ENNReal.toReal_mul,ENNReal.toReal_div] at hr ⊢
    exact_mod_cast (by linarith : (f.length : ℝ) ≤ 4)

/-- The explicit repeated-natural coordinate multiplicity of a flag term
is exactly its chief length, rather than a new unbounded parameter. -/
theorem binary_repeated_flag_multiplicity (C : Subgroup G) (f : ReducibleChiefFlag ρ C)
    {d : ℕ} (hd : 0 < d)
    (hn : ∀ i < f.length, IsLinearNatural
      ((sectionRepresentation ρ (f.chain i) (f.chain (i+1))).comp C.subtype) BinaryField.two d)
    {i r : ℕ} (hi : i ≤ f.length)
    (hr : IsRepeatedLinearNatural (f.chain i).toRepresentation BinaryField.two d r) : r = i := by
  obtain ⟨a⟩ := hr
  have he := a.linearEquiv.finrank_eq
  change Module.finrank (ZMod 2) (f.chain i).toSubmodule =
    Module.finrank (ZMod 2) (Fin r → Fin d → ZMod 2) at he
  simp [Module.finrank_pi_fintype] at he
  rw [(binary_natural_flag_dimensions ρ C f hn).1 i hi] at he
  exact (Nat.eq_of_mul_eq_mul_right hd he).symm

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
