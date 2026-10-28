module

public import Theory.Representation.SixLetterRadicalDisplacement.PermutationQuotients.TranspositionRank.Seeds
public import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.Tactic

/-!
# Transposition rank on noncentral syntheme quotients

Every transposition moves at least two dimensions on every noncentral
surjective equivariant quotient of the actual fifteen-syntheme permutation
module. No faithfulness or additional finite-dimensionality premise is needed.

For (01), the displacement range contains rows 72 and 528. Each of these
vectors and their sum 600 generates the augmentation core under A₆, by the
kernel-checked certificates in `Seeds`. Thus a noncentral equivariant quotient
kills none of the three vectors, so their two images are linearly independent
over F₂. Conjugacy gives the result for all transpositions. The final lemmas
transport the result through an actor isomorphism and an equivariant linear
equivalence, and exclude a transvection in the transported quotient.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), Lemma 13.8.34, printed p.968 (PDF p.985),
final line-containment contradiction. The downstream source owner supplies
the marking, quotient map and noncentrality; this module proves the complete
representation-theoretic obstruction for those inputs.
-/

public section
open BinaryPermutation Representation Module
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace Representation.SixLetterRadicalDisplacement.PermutationQuotients.TranspositionRank

variable {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]

/-- A surjective quotient of the fifteen-dimensional module is finite-dimensional. -/
theorem finite_of_surjective (f : P →ₗ[ZMod 2] Q) (hf : Function.Surjective f) :
    Module.Finite (ZMod 2) Q := Module.Finite.of_surjective f hf

private theorem seed_nonzero
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (n : ℕ) (hn : n = 72 ∨ n = 528 ∨ n = 600) :
    f (row n) ≠ 0 := by
  intro hz
  have hker : P0 ≤ f.ker := core_le_of_seed f.ker (by
    intro g v hv
    change f (rho g.val v) = 0
    rw [heq, show f v = 0 from hv, map_zero]) n hn hz
  obtain ⟨g, v, hne⟩ := hnc
  exact hne (quotient_trivial_of_core_le_ker (MonoidHom.id S) σ f hf heq hker g v)

private theorem displacement72 : rho swap01 (row 8) - row 8 = row 72 := by decide +kernel
private theorem displacement528 : rho swap01 (row 16) - row 16 = row 528 := by decide +kernel
private theorem row600 : row 72 + row 528 = row 600 := by decide

/-- The chosen transposition moves at least two dimensions in any noncentral quotient. -/
theorem swap01_rank_ge_two
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) :
    2 ≤ finrank (ZMod 2) (LinearMap.range (σ swap01 - LinearMap.id)) := by
  let := finite_of_surjective f hf
  have h72 := seed_nonzero σ f hf heq hnc 72 (Or.inl rfl)
  have h528 := seed_nonzero σ f hf heq hnc 528 (Or.inr (Or.inl rfl))
  have h600 := seed_nonzero σ f hf heq hnc 600 (Or.inr (Or.inr rfl))
  have hne : f (row 528) ≠ f (row 72) := by
    intro h
    apply h600
    rw [← row600, map_add, h, ZModModule.add_self]
  let W := LinearMap.range (σ swap01 - LinearMap.id)
  have hm72 : f (row 72) ∈ W := by
    refine ⟨f (row 8), ?_⟩
    change σ swap01 (f (row 8)) - f (row 8) = f (row 72)
    rw [← heq, ← map_sub, displacement72]
  have hm528 : f (row 528) ∈ W := by
    refine ⟨f (row 16), ?_⟩
    change σ swap01 (f (row 16)) - f (row 16) = f (row 528)
    rw [← heq, ← map_sub, displacement528]
  let u : W := ⟨f (row 72), hm72⟩
  let v : W := ⟨f (row 528), hm528⟩
  have hli : LinearIndependent (ZMod 2) (![u,v] : Fin 2 → W) := by
    apply linearIndependent_fin2.mpr
    constructor
    · intro h
      exact h528 (congrArg Subtype.val h)
    · intro c
      change c • v ≠ u
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · simpa only [zero_smul, ne_eq, eq_comm] using
          (show u ≠ 0 from fun h => h72 (congrArg Subtype.val h))
      · simpa only [one_smul] using
          (show v ≠ u from fun h => hne (congrArg Subtype.val h))
  simpa using hli.fintype_card_le_finrank

/-- Equivariant linear equivalences preserve the dimension of a displacement range. -/
theorem displacement_finrank_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (e : Q ≃ₗ[ZMod 2] V) (a : Q →ₗ[ZMod 2] Q) (b : V →ₗ[ZMod 2] V)
    (he : ∀ v, e (a v) = b (e v)) :
    finrank (ZMod 2) (LinearMap.range (a - LinearMap.id)) =
      finrank (ZMod 2) (LinearMap.range (b - LinearMap.id)) := by
  have hm : (LinearMap.range (a - LinearMap.id)).map e.toLinearMap =
      LinearMap.range (b - LinearMap.id) := by
    ext v
    constructor
    · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
      refine ⟨e u, ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub, he]
    · rintro ⟨u, rfl⟩
      refine ⟨a (e.symm u) - e.symm u, ⟨e.symm u, rfl⟩, ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub, he,
        e.apply_symm_apply]
  rw [← hm, e.finrank_map_eq]

private theorem conjugate_displacement_finrank (σ : Representation (ZMod 2) S Q) (g a : S) :
    finrank (ZMod 2) (LinearMap.range (σ a - LinearMap.id)) =
      finrank (ZMod 2) (LinearMap.range (σ (g * a * g⁻¹) - LinearMap.id)) := by
  let e : Q ≃ₗ[ZMod 2] Q := {
    toLinearMap := σ g
    invFun := σ g⁻¹
    left_inv := by
      intro v
      change σ g⁻¹ (σ g v) = v
      simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    right_inv := by
      intro v
      change σ g (σ g⁻¹ v) = v
      simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply] }
  apply displacement_finrank_eq e
  intro v
  change σ g (σ a v) = σ (g * a * g⁻¹) (σ g v)
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

/-- Every actual transposition has displacement rank at least two on a noncentral
surjective equivariant quotient of the marked syntheme module. -/
theorem transposition_rank_ge_two
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (t : S) (ht : t.IsSwap) :
    2 ≤ finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) := by
  obtain ⟨i, j, hij, rfl⟩ := ht
  obtain ⟨g, hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap (by decide : (0 : Fin 6) ≠ 1) hij)
  have hc := conjugate_displacement_finrank σ g swap01
  change g * swap01 * g⁻¹ = Equiv.swap i j at hg
  rw [hg] at hc
  rw [← hc]
  exact swap01_rank_ge_two σ f hf heq hnc

/-- The rank obstruction under any marking of the actor as the six-letter symmetric group. -/
theorem actor_rank_ge_two {G : Type*} [Group G]
    (e : G ≃* S) (σ : Representation (ZMod 2) G Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho (e g) v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (t : G) (ht : (e t).IsSwap) :
    2 ≤ finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) := by
  let τ := σ.comp e.symm.toMonoidHom
  have hτeq : ∀ g v, f (rho g v) = τ g (f v) := by
    intro g v
    simpa [τ] using heq (e.symm g) v
  have hτnc : ∃ g v, τ g v ≠ v := by
    obtain ⟨g, v, h⟩ := hnc
    exact ⟨e g, v, by simpa [τ] using h⟩
  have h := transposition_rank_ge_two τ f hf hτeq hτnc (e t) ht
  have he : ∀ v, (LinearEquiv.refl (ZMod 2) Q) (τ (e t) v) =
      σ t ((LinearEquiv.refl (ZMod 2) Q) v) := by
    intro v
    change σ (e.symm (e t)) v = σ t v
    rw [e.symm_apply_apply]
  exact (displacement_finrank_eq (LinearEquiv.refl (ZMod 2) Q)
    (τ (e t)) (σ t) he) ▸ h

/-- Both the actor marking and an equivariant change of the quotient module may
be transported without changing the transposition rank obstruction. -/
theorem transported_rank_ge_two {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : G ≃* S) (σ : Representation (ZMod 2) G Q) (τ : Representation (ZMod 2) G V)
    (f : P →ₗ[ZMod 2] Q) (hf : Function.Surjective f)
    (heq : ∀ g v, f (rho (e g) v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (u : Q ≃ₗ[ZMod 2] V)
    (hu : ∀ g v, u (σ g v) = τ g (u v)) (t : G) (ht : (e t).IsSwap) :
    2 ≤ finrank (ZMod 2) (LinearMap.range (τ t - LinearMap.id)) := by
  rw [← displacement_finrank_eq u (σ t) (τ t) (hu t)]
  exact actor_rank_ge_two e σ f hf heq hnc t ht

/-- In the transported quotient an actual transposition cannot be a transvection.
Finite-dimensionality is obtained from the quotient surjection. -/
theorem transported_not_transvection {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : G ≃* S) (σ : Representation (ZMod 2) G Q) (τ : Representation (ZMod 2) G V)
    (f : P →ₗ[ZMod 2] Q) (hf : Function.Surjective f)
    (heq : ∀ g v, f (rho (e g) v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (u : Q ≃ₗ[ZMod 2] V)
    (hu : ∀ g v, u (σ g v) = τ g (u v)) (t : G) (ht : (e t).IsSwap)
    (a : V ≃ₗ[ZMod 2] V) (ha : a.toLinearMap = τ t) :
    a ∉ LinearEquiv.transvections (ZMod 2) V := by
  let := finite_of_surjective (u.toLinearMap.comp f) (u.surjective.comp hf)
  intro h
  have hle := LinearEquiv.mem_dilatransvections_iff_finrank.mp
    (LinearEquiv.transvections_subset_dilatransvections h)
  rw [ha] at hle
  have hge := transported_rank_ge_two e σ τ f hf heq hnc u hu t ht
  omega

end Representation.SixLetterRadicalDisplacement.PermutationQuotients.TranspositionRank
