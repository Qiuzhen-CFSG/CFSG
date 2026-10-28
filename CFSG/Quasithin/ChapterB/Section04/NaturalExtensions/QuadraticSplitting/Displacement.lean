module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Propagation
public import Mathlib.Algebra.Module.ZMod

/-!
# The displacement space of a Levi-fixed lift

Quadraticity makes x ↦ ρ(x)v − v additive on the axis group. Its image is
therefore already a binary subspace, without taking a larger linear span.
It is fixed by the axis group and invariant under any normalizing subgroup
fixing v. The quotient orbit then proves that this subspace together with
v is a complement to the original submodule in the binary-field case.

Source: Aschbacher–Smith B.4.9(1), printed p.93, combined manuscript of
1 March 2004. The fixed lift and the quotient orbit calculation are separate
inputs, not a presumed invariant complement.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (Q : Subgroup G)
  (hq : IsQuadratic ρ Q) (v : V)

/-- The source map α, with the original action and original lifted vector. -/
def displacementHom : Additive Q →+ V where
  toFun x := ρ x.toMul v - v
  map_zero' := by simp
  map_add' x y := by
    change ρ ((x.toMul : G) * y.toMul) v - v =
      (ρ x.toMul v - v) + (ρ y.toMul v - v)
    have hh := hq x.toMul x.toMul.property y.toMul y.toMul.property v
    rw [map_sub] at hh
    rw [map_mul, Module.End.mul_apply]
    rw [sub_eq_iff_eq_add.mp hh]
    abel

/-- `[v,Q]` is exactly the additive image of α, regarded as a binary subspace. -/
def displacementSpace : Submodule (ZMod 2) V :=
  AddSubgroup.toZModSubmodule 2 (displacementHom ρ Q hq v).range

/-- Every vector in the displacement space is one displacement. -/
theorem mem_displacementSpace (w : V) :
    w ∈ displacementSpace ρ Q hq v ↔ ∃ x : Q, ρ x v - v = w := by
  rfl

/-- The full axis group fixes the displacement space. -/
theorem displacementSpace_le_fixed : displacementSpace ρ Q hq v ≤ fixedSpace ρ Q := by
  rintro w ⟨x, rfl⟩ a
  exact hq a a.property x.toMul x.toMul.property v

/-- A normalizing subgroup fixing the lift preserves its displacement space. -/
theorem displacementSpace_invariant (K : Subgroup G)
    (hnorm : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q)
    (hfix : ∀ k ∈ K, ρ k v = v) :
    ∀ k ∈ K, ∀ w ∈ displacementSpace ρ Q hq v,
      ρ k w ∈ displacementSpace ρ Q hq v := by
  rintro k hk w ⟨x, rfl⟩
  refine ⟨Additive.ofMul ⟨k * x.toMul * k⁻¹, hnorm k hk x.toMul x.toMul.property⟩, ?_⟩
  change ρ (k * x.toMul * k⁻¹) v - v = ρ k (ρ x.toMul v - v)
  have hi : ρ k⁻¹ v = v := by
    have hh := congrArg (ρ k⁻¹) (hfix k hk)
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at hh
    exact hh.symm
  simp only [map_mul, Module.End.mul_apply, hi, map_sub, hfix k hk]

/-- The local candidate W + ⟨v⟩. -/
def localSpace : Submodule (ZMod 2) V :=
  displacementSpace ρ Q hq v ⊔ Submodule.span (ZMod 2) {v}

/-- KQ preserves W + ⟨v⟩ when K normalizes Q and fixes v. -/
theorem localSpace_invariant (K : Subgroup G)
    (hnorm : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q)
    (hfix : ∀ k ∈ K, ρ k v = v) :
    K ⊔ Q ≤ subspaceStabilizer ρ (localSpace ρ Q hq v) := by
  have hgen (g : G)
      (hW : ∀ w ∈ displacementSpace ρ Q hq v,
        ρ g w ∈ displacementSpace ρ Q hq v)
      (hv : ρ g v ∈ localSpace ρ Q hq v) :
      ∀ w ∈ localSpace ρ Q hq v, ρ g w ∈ localSpace ρ Q hq v := by
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_add, map_smul]
    exact (localSpace ρ Q hq v).add_mem (Submodule.mem_sup_left (hW a ha))
      ((localSpace ρ Q hq v).smul_mem c hv)
  apply sup_le
  · apply le_subspaceStabilizer
    intro k hk
    apply hgen k (displacementSpace_invariant ρ Q hq v K hnorm hfix k hk)
    rw [hfix k hk]
    exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton v))
  · apply le_subspaceStabilizer
    intro x hx
    apply hgen x
    · intro w hw
      have hh : ρ x w = w := displacementSpace_le_fixed ρ Q hq v hw ⟨x,hx⟩
      rw [hh]
      exact hw
    · have hw : ρ x v - v ∈ displacementSpace ρ Q hq v :=
        (mem_displacementSpace ρ Q hq v _).mpr ⟨⟨x,hx⟩, rfl⟩
      have hh := (localSpace ρ Q hq v).add_mem (Submodule.mem_sup_left hw)
        (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton v)))
      simpa only [sub_add_cancel] using hh

/-- The binary local complement construction. The hypotheses about the lift
are tested on the literal quotient: its orbit is free, lies off the fixed
hyperplane, and its displacement orbit together with its line covers the
quotient. No upstairs disjointness or splitting is assumed. -/
theorem localSpace_isCompl (N : Subrepresentation ρ)
    (hfree : ∀ x : Q, N.quotientRepresentation x (N.toSubmodule.mkQ v) =
      N.toSubmodule.mkQ v → (x : G) = 1)
    (hout : N.toSubmodule.mkQ v ∉ fixedSpace N.quotientRepresentation Q)
    (hcover : ∀ z : V ⧸ N.toSubmodule, ∃ c : ZMod 2, ∃ x : Q,
      z = c • N.toSubmodule.mkQ v +
        (N.quotientRepresentation x (N.toSubmodule.mkQ v) - N.toSubmodule.mkQ v)) :
    IsCompl N.toSubmodule (localSpace ρ Q hq v) := by
  have hWfixed (w : V) (hw : w ∈ displacementSpace ρ Q hq v) :
      N.toSubmodule.mkQ w ∈ fixedSpace N.quotientRepresentation Q := by
    intro a
    change N.toSubmodule.mkQ (ρ a w) = N.toSubmodule.mkQ w
    exact congrArg N.toSubmodule.mkQ (displacementSpace_le_fixed ρ Q hq v hw a)
  have hWzero (w : V) (hw : w ∈ displacementSpace ρ Q hq v)
      (hz : N.toSubmodule.mkQ w = 0) : w = 0 := by
    obtain ⟨x, rfl⟩ := (mem_displacementSpace ρ Q hq v w).mp hw
    have hx : (x : G) = 1 := hfree x (sub_eq_zero.mp (by
      change N.toSubmodule.mkQ (ρ x v) - N.toSubmodule.mkQ v = 0
      rw [← map_sub]
      exact hz))
    simp [hx]
  constructor
  · apply Submodule.disjoint_def.mpr
    intro w hn hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have hz : N.toSubmodule.mkQ a + c • N.toSubmodule.mkQ v = 0 := by
      have hz' : N.toSubmodule.mkQ (a + c • v) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hn
      simpa only [map_add, map_smul] using hz'
    have hc : c = 0 := by
      by_contra hc
      have hcv : c • N.toSubmodule.mkQ v ∈ fixedSpace N.quotientRepresentation Q := by
        rw [eq_neg_of_add_eq_zero_right hz]
        exact (fixedSpace N.quotientRepresentation Q).neg_mem (hWfixed a ha)
      exact hout ((Submodule.smul_mem_iff _ hc).mp hcv)
    subst c
    simp only [zero_smul, add_zero] at hz ⊢
    exact hWzero a ha hz
  · apply codisjoint_iff.mpr
    apply top_unique
    intro w _
    obtain ⟨c, x, hx⟩ := hcover (N.toSubmodule.mkQ w)
    let b := c • v + (ρ x v - v)
    have hb : b ∈ localSpace ρ Q hq v := by
      apply (localSpace ρ Q hq v).add_mem
      · exact Submodule.mem_sup_right (Submodule.smul_mem _ c
          (Submodule.subset_span (Set.mem_singleton v)))
      · exact Submodule.mem_sup_left ((mem_displacementSpace ρ Q hq v _).mpr ⟨x,rfl⟩)
    have hnb : w - b ∈ N.toSubmodule := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change N.toSubmodule.mkQ (w - (c • v + (ρ x v - v))) = 0
      rw [map_sub, map_add, map_smul, map_sub]
      exact sub_eq_zero.mpr hx
    exact Submodule.mem_sup.mpr ⟨w - b, hnb, b, hb, sub_add_cancel _ _⟩

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
