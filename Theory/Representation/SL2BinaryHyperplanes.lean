module
public import Theory.SpecificGroups.SL2.Affine.Action
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Algebra.ZMod
public import Theory.Representation.BinaryOffender.PermutedSupports

/-!
# Binary hyperplanes of the natural SL₂ module

A binary linear functional on the field, composed with the determinant
pairing, identifies the natural plane with its binary dual. The pairing is
nondegenerate and SL₂-invariant, so nonzero-vector transitivity gives actual
transitivity on binary hyperplanes. Separately, a two-group has a nonzero
fixed vector on the dual, and hence an invariant binary hyperplane.

These are the natural-module inputs to Aschbacher--Smith, 6.1.10(1),
printed p.670. The argument works over every finite binary field and uses
no finite enumeration. The Chapter 6 global-rank theorem is the consumer.
-/

open Matrix
noncomputable section
namespace Representation.SL2BinaryHyperplanes
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

private def pairing (ell : F →ₗ[ZMod 2] ZMod 2) :
    (Fin 2 → F) →ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin 2 → F) where
  toFun v := {
    toFun w := ell (v 0 * w 1 - v 1 * w 0)
    map_add' w x := by
      rw [show v 0 * (w + x) 1 - v 1 * (w + x) 0 =
        (v 0 * w 1 - v 1 * w 0) + (v 0 * x 1 - v 1 * x 0) by
          simp only [Pi.add_apply]; ring, map_add]
    map_smul' c w := by
      change ell (v 0 * (c • w 1) - v 1 * (c • w 0)) = c • _
      rw [mul_smul_comm, mul_smul_comm, ← smul_sub, map_smul] }
  map_add' v w := by
    apply LinearMap.ext
    intro x
    change ell ((v + w) 0 * x 1 - (v + w) 1 * x 0) = _
    rw [show (v + w) 0 * x 1 - (v + w) 1 * x 0 =
      (v 0 * x 1 - v 1 * x 0) + (w 0 * x 1 - w 1 * x 0) by
        simp only [Pi.add_apply]; ring, map_add]
    rfl
  map_smul' c v := by
    apply LinearMap.ext
    intro w
    change ell ((c • v 0) * w 1 - (c • v 1) * w 0) = c • _
    rw [smul_mul_assoc, smul_mul_assoc, ← smul_sub, map_smul]
    rfl

omit [Finite F] in
private theorem pairing_injective (ell : F →ₗ[ZMod 2] ZMod 2) (hell : ell 1 = 1) :
    Function.Injective (pairing ell) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro v hv
  change v = 0
  have hz (w : Fin 2 → F) : ell (v 0 * w 1 - v 1 * w 0) = 0 :=
    congrArg (fun f : Module.Dual (ZMod 2) (Fin 2 → F) => f w) hv
  have h0 : v 0 = 0 := by
    by_contra h
    have hh := hz ![0, (v 0)⁻¹]
    simp [h, hell] at hh
  have h1 : v 1 = 0 := by
    by_contra h
    have hh := hz ![-(v 1)⁻¹, 0]
    simp [h, hell] at hh
  ext i
  fin_cases i <;> assumption

private def selfDual (ell : F →ₗ[ZMod 2] ZMod 2) (hell : ell 1 = 1) :
    (Fin 2 → F) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin 2 → F) :=
  LinearEquiv.ofBijective (pairing ell)
    ⟨pairing_injective ell hell,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq (K := ZMod 2) (V := Fin 2 → F)).symm).mp
          (pairing_injective ell hell)⟩

/-- The literal determinant-one action with scalars restricted to the binary field. -/
@[expose] public def action (g : SpecialLinearGroup (Fin 2) F) :
    (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F) :=
  (SpecialLinearGroup.toLin' g).restrictScalars (ZMod 2)

omit [Finite F] in
private theorem pairing_invariant (ell : F →ₗ[ZMod 2] ZMod 2)
    (g : SpecialLinearGroup (Fin 2) F) (v w : Fin 2 → F) :
    pairing ell (action g v) (action g w) = pairing ell v w := by
  change ell ((g.val.mulVec v) 0 * (g.val.mulVec w) 1 -
    (g.val.mulVec v) 1 * (g.val.mulVec w) 0) = _
  have hd := g.property
  rw [det_fin_two] at hd
  rw [show (g.val.mulVec v) 0 * (g.val.mulVec w) 1 -
    (g.val.mulVec v) 1 * (g.val.mulVec w) 0 =
    (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) *
      (v 0 * w 1 - v 1 * w 0) by
        simp only [mulVec, dotProduct, Fin.sum_univ_two]; ring, hd, one_mul]
  rfl

private theorem hyperplane_eq_pairing_ker (ell : F →ₗ[ZMod 2] ZMod 2) (hell : ell 1 = 1)
    (H : Submodule (ZMod 2) (Fin 2 → F))
    (hH : Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) (Fin 2 → F)) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ H = (selfDual ell hell v).ker := by
  have ht : H < ⊤ := by
    apply lt_of_le_of_ne le_top
    intro he
    rw [he, finrank_top] at hH
    omega
  obtain ⟨f, hf, hle⟩ := H.exists_le_ker_of_lt_top ht
  obtain ⟨v, rfl⟩ := (selfDual ell hell).surjective f
  refine ⟨v, ?_, Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  · intro hv; exact hf (by simp [hv])
  · have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    omega

/-- Determinant-one matrices act transitively on the binary hyperplanes. -/
public theorem transitive_hyperplanes (H K : Submodule (ZMod 2) (Fin 2 → F))
    (hH : Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) (Fin 2 → F))
    (hK : Module.finrank (ZMod 2) K + 1 = Module.finrank (ZMod 2) (Fin 2 → F)) :
    ∃ g : SpecialLinearGroup (Fin 2) F, H.map (action g).toLinearMap = K := by
  obtain ⟨ell, hell⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) (one_ne_zero : (1 : F) ≠ 0)
  obtain ⟨v, hv, rfl⟩ := hyperplane_eq_pairing_ker ell hell H hH
  obtain ⟨w, hw, rfl⟩ := hyperplane_eq_pairing_ker ell hell K hK
  obtain ⟨g, hg⟩ := Matrix.SL2.exists_mulVec_eq F v w hv hw
  have he : action g v = w := hg
  refine ⟨g, ?_⟩
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change pairing ell w (action g y) = 0
    rw [← he, pairing_invariant]
    exact hy
  · intro hz
    refine ⟨(action g).symm z, ?_, (action g).apply_symm_apply z⟩
    change pairing ell v ((action g).symm z) = 0
    have hh := pairing_invariant ell g v ((action g).symm z)
    rw [he, (action g).apply_symm_apply] at hh
    exact hh.symm.trans hz

end Representation.SL2BinaryHyperplanes

namespace Representation
open BinaryOffender
variable {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
  [FiniteDimensional (ZMod 2) X] [Nontrivial X]

/-- Every two-group action on a nonzero binary module preserves a hyperplane. -/
public theorem exists_invariant_binary_hyperplane (ρ : Representation (ZMod 2) H X)
    (hH : IsPGroup 2 H) :
    ∃ U : Submodule (ZMod 2) X,
      Module.finrank (ZMod 2) U + 1 = Module.finrank (ZMod 2) X ∧
      ∀ g v, v ∈ U → ρ g v ∈ U := by
  obtain ⟨f, _, hf, hfix⟩ := PermutedSupports.exists_nonzero_fixed ρ.dual ⊤
    (hH.to_subgroup ⊤) ⊤ (top_ne_bot : (⊤ : Submodule (ZMod 2) (Module.Dual (ZMod 2) X)) ≠ ⊥)
    (by intro g hg v; simp)
  refine ⟨f.ker, Module.Dual.finrank_ker_add_one_of_ne_zero hf, ?_⟩
  intro g v hv
  have hh := congrArg (fun k : Module.Dual (ZMod 2) X => k v)
    (hfix ⟨g⁻¹, Subgroup.mem_top _⟩)
  change f (ρ (g⁻¹)⁻¹ v) = f v at hh
  change f (ρ g v) = 0
  have hh' : f (ρ g v) = f v := by simpa only [inv_inv] using hh
  exact hh'.trans hv

end Representation
