module

public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.Representation.SubspaceQuotient
public import Theory.LinearAlgebra.BinaryTriangularPGroup

/-!
# Scalar saturation of two-core displacements

For a faithful finite-dimensional representation of a finite group over a field
of characteristic two, an element whose displacement is a linear combination
of displacements from the intrinsic two-core lies in that two-core. In particular,
this applies to any scalar multiple of one two-core displacement. The field need
not be finite, and its universe is independent of the group and vector space.

The span of the displacements of a finite p-group consists of nilpotent operators
in characteristic p: quotient by the nonzero common fixed space and induct on
dimension. This span is closed under multiplication. For a normal subgroup it is
also preserved by ambient conjugation. The elements with displacement in the span
therefore form a normal subgroup, whose faithful image is unipotent, hence a
two-group. Maximality of the intrinsic two-core finishes the argument.

The affine-root application is in
`Theory.Representation.TwoCoreScalarSaturation.AffineRootQuotient`. This supplies
the linear scalar-closure premise used for Aschbacher--Smith E.1.2(E1) and the
G₂ branch of E.1.14(1), printed pp.210 and 214, citing Asc82a, Lemma 4.7.
-/

public section

open scoped BigOperators
open Subgroup

namespace Representation
universe u v w
variable {F : Type u} [Field F] {Q : Type v} [Group Q] [Finite Q]
  {V : Type w} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private theorem displacement_span_nilpotent
    (hc : ringChar F ≠ 0) (hQ : IsPGroup (ringChar F) Q)
    (ρ : Representation F Q V) {f : Module.End F V}
    (hf : f ∈ Submodule.span F (Set.range (fun q : Q => ρ q - 1))) :
    IsNilpotent f := by
  classical
  let : Fintype Q := Fintype.ofFinite Q
  generalize hn : Module.finrank F V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hV : Nontrivial V
    · let : Nontrivial V := hV
      obtain ⟨v, hv, hvQ⟩ := pGroup_fix_nonzero_vector hc hQ ρ
      let U : Subrepresentation ρ := {
        toSubmodule := invariants ρ
        apply_mem_toSubmodule := by
          intro q v hv
          have he : ρ q v = v := hv q
          rw [he]
          exact hv }
      have hlt : Module.finrank F (V ⧸ U.toSubmodule) < n := by
        have hpos : 0 < Module.finrank F U.toSubmodule :=
          Module.finrank_pos_iff_exists_ne_zero.mpr
            ⟨⟨v, hvQ⟩, fun he => hv (congrArg Subtype.val he)⟩
        have hadd := U.toSubmodule.finrank_quotient_add_finrank
        omega
      obtain ⟨c, hcoeff⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hf
      let f' : Module.End F (V ⧸ U.toSubmodule) :=
        ∑ q : Q, c q • (U.quotientRepresentation q - 1)
      have hf' : f' ∈ Submodule.span F
          (Set.range (fun q : Q => U.quotientRepresentation q - 1)) := by
        apply Submodule.sum_mem
        intro q _
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self q))
      obtain ⟨m, hm⟩ := ih _ hlt U.quotientRepresentation hf' rfl
      have hkill (v : V) (hv : v ∈ U.toSubmodule) : f v = 0 := by
        rw [← hcoeff]
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
          Module.End.one_apply]
        have he (q : Q) : ρ q v = v := hv q
        simp only [he, sub_self, smul_zero, Finset.sum_const_zero]
      have hquot (v : V) : U.toSubmodule.mkQ (f v) = f' (U.toSubmodule.mkQ v) := by
        rw [← hcoeff]
        simp only [f', LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
          Module.End.one_apply, map_sum, map_smul, map_sub,
          Subrepresentation.quotientRepresentation_mk]
      have hpow (k : ℕ) (v : V) :
          U.toSubmodule.mkQ ((f ^ k) v) = (f' ^ k) (U.toSubmodule.mkQ v) := by
        induction k with
        | zero => simp
        | succ k hk =>
          simp only [pow_succ', Module.End.mul_apply, hquot, hk]
      refine ⟨m + 1, ?_⟩
      ext v
      rw [pow_succ', Module.End.mul_apply]
      apply hkill
      apply (Submodule.Quotient.mk_eq_zero U.toSubmodule).mp
      change U.toSubmodule.mkQ ((f ^ m) v) = 0
      rw [hpow, hm, LinearMap.zero_apply]
    · have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
      exact ⟨1, Subsingleton.elim _ _⟩

omit [Finite Q] [FiniteDimensional F V] in
private theorem displacement_span_mul_mem (ρ : Representation F Q V)
    {a b : Module.End F V}
    (ha : a ∈ Submodule.span F (Set.range (fun q : Q => ρ q - 1)))
    (hb : b ∈ Submodule.span F (Set.range (fun q : Q => ρ q - 1))) :
    a * b ∈ Submodule.span F (Set.range (fun q : Q => ρ q - 1)) := by
  let I := Submodule.span F (Set.range (fun q : Q => ρ q - 1))
  have hgen (q : Q) : ρ q - 1 ∈ I := Submodule.subset_span (Set.mem_range_self q)
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨q, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨r, rfl⟩ := hb
      have he : (ρ q - 1) * (ρ r - 1) = (ρ (q * r) - 1) - (ρ q - 1) - (ρ r - 1) := by
        rw [map_mul]
        noncomm_ring
      rw [he]
      exact I.sub_mem (I.sub_mem (hgen _) (hgen _)) (hgen _)
    | zero => simpa only [mul_zero] using I.zero_mem
    | add a b _ _ ha hb => simpa only [mul_add] using I.add_mem ha hb
    | smul c a _ ha => simpa only [mul_smul_comm] using I.smul_mem c ha
  | zero => simpa only [zero_mul] using I.zero_mem
  | add a b _ _ ha hb => simpa only [add_mul] using I.add_mem ha hb
  | smul c a _ ha => simpa only [smul_mul_assoc] using I.smul_mem c ha

variable {X : Type v} [Group X] [Finite X]

omit [Finite X] [FiniteDimensional F V] in
private theorem displacement_span_conj_mem (ρ : Representation F X V)
    (N : Subgroup X) [N.Normal] (g : X) {a : Module.End F V}
    (ha : a ∈ Submodule.span F (Set.range (fun q : N => ρ q - 1))) :
    ρ g * a * ρ g⁻¹ ∈ Submodule.span F (Set.range (fun q : N => ρ q - 1)) := by
  let I := Submodule.span F (Set.range (fun q : N => ρ q - 1))
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨q, rfl⟩ := ha
    have he : ρ g * (ρ q - 1) * ρ g⁻¹ = ρ (g * q * g⁻¹) - 1 := by
      simp only [mul_sub, sub_mul, mul_one, ← map_mul, mul_inv_cancel, map_one]
    rw [he]
    exact Submodule.subset_span ⟨⟨g * q * g⁻¹, (inferInstance : N.Normal).conj_mem _ q.property g⟩, rfl⟩
  | zero => simpa only [mul_zero, zero_mul] using I.zero_mem
  | add a b _ _ ha hb => simpa only [mul_add, add_mul] using I.add_mem ha hb
  | smul c a _ ha =>
    simpa only [mul_smul_comm, smul_mul_assoc] using I.smul_mem c ha

/-- Linear combinations of two-core displacements detect the intrinsic two-core
in a faithful finite-dimensional representation in characteristic two. -/
theorem mem_twoCore_of_displacement_mem_span [CharP F 2]
    (ρ : Representation F X V) (hρ : Function.Injective ρ) (x : X)
    (hx : ρ x - 1 ∈ Submodule.span F
      (Set.range (fun q : pCore 2 X => ρ q - 1))) : x ∈ pCore 2 X := by
  classical
  by_cases hV : Nontrivial V
  · let : Nontrivial V := hV
    let I := Submodule.span F (Set.range (fun q : pCore 2 X => ρ q - 1))
    let S : Submonoid X := {
      carrier := {g | ρ g - 1 ∈ I}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change ρ (a * b) - 1 ∈ I
        have he : ρ (a * b) - 1 = (ρ a - 1) * (ρ b - 1) + (ρ a - 1) + (ρ b - 1) := by
          rw [map_mul]
          noncomm_ring
        rw [he]
        exact I.add_mem (I.add_mem
          (displacement_span_mul_mem (ρ.comp (pCore 2 X).subtype) ha hb) ha) hb }
    let H : Subgroup X := {
      S with
      inv_mem' := by
        intro g hg
        have he : g ^ (orderOf g - 1) = g⁻¹ := by
          apply eq_inv_of_mul_eq_one_left
          rw [pow_sub_one_mul (orderOf_pos g).ne', pow_orderOf_eq_one]
        rw [← he]
        exact S.pow_mem hg _ }
    have hH : H.Normal := ⟨by
      intro a ha g
      change ρ (g * a * g⁻¹) - 1 ∈ I
      have he : ρ (g * a * g⁻¹) - 1 = ρ g * (ρ a - 1) * ρ g⁻¹ := by
        simp only [mul_sub, sub_mul, mul_one, ← map_mul, mul_inv_cancel, map_one]
      rw [he]
      exact displacement_span_conj_mem ρ (pCore 2 X) g ha⟩
    let : ExpChar (Module.End F V) 2 :=
      expChar_of_injective_algebraMap
        (FaithfulSMul.algebraMap_injective F (Module.End F V)) 2
    have hP : IsPGroup 2 H := by
      apply IsPGroup.of_injective_unipotent_binary (ρ.comp H.subtype)
        (hρ.comp Subtype.val_injective)
      intro g
      apply displacement_span_nilpotent (F := F)
        (by rw [ringChar.eq F 2]; decide)
        (by rw [ringChar.eq F 2]; exact pCore_isPGroup)
        (ρ.comp (pCore 2 X).subtype)
      exact g.property
    exact (show H ≤ pCore 2 X from le_sSup ⟨hH, hP⟩) hx
  · have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    have hx1 : x = 1 := hρ (Subsingleton.elim _ _)
    exact hx1 ▸ (pCore 2 X).one_mem

/-- Scalar saturation of the displacement operators of the intrinsic two-core. -/
theorem mem_twoCore_of_displacement_eq_smul [CharP F 2]
    (ρ : Representation F X V) (hρ : Function.Injective ρ)
    (x y : X) (c : F) (hy : y ∈ pCore 2 X)
    (hxy : ρ x - 1 = c • (ρ y - 1)) : x ∈ pCore 2 X := by
  apply mem_twoCore_of_displacement_mem_span ρ hρ x
  rw [hxy]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩)

end Representation
