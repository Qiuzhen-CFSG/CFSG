module

public import Theory.Representation.OrthogonalFourPlusMatrix.Commutant
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.LinearAlgebra.QuadraticRankOneDisplacement

/-!
# Low-rank actors in the full binary determinant normalizer

Conjugating scalars in the computed additive commutant constructs an actual
field automorphism for every binary normalizer element. A nontrivial scalar
twist moves at least half the eight-dimensional binary module. Thus rank at
most two forces F₄-linearity. Restriction of scalars then shows that a
nonidentity actor has field rank one and binary rank exactly two.

The argument covers the full normalizer, including component interchanges,
field actors, their products and scalar factors; no outer-action list or
involution hypothesis is needed. It does not assert preservation of the
F₄-valued determinant or singularity of a source-marked vector.

Source: Aschbacher--Smith 14.4.6(b), combined manuscript (1 March 2004),
printed p.1008.
-/

public section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Module

/-- Every binary normalizer element is semilinear over the actual coefficient field. -/
theorem normalizer_semilinear (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V))) :
    ∃ σ : F ≃+* F, ∀ (c : F) (M : V), t (c • M) = σ c • t M := by
  let q (c : F) : V →+ V :=
    { toFun := fun M => t (c • t.symm M)
      map_zero' := by simp
      map_add' := by intro M N; simp [smul_add] }
  have hq (c : F) : ∃ d : F, ∀ M, q c M = d • M := by
    apply centralizer_scalar
    intro g M
    have hg : linearAction g ∈ linearAction.range := ⟨g, rfl⟩
    have hmem := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer _).inv_mem ht) (linearAction g)).mp hg
    obtain ⟨h, hh⟩ := hmem
    have hh' : linearAction h = t⁻¹ * linearAction g * t := by simpa using hh
    have hi (N : V) : t.symm (action g N) = action h (t.symm N) := by
      have he := LinearEquiv.congr_fun hh' (t.symm N)
      simpa using he.symm
    have he (N : V) : t (action h N) = action g (t N) := by
      apply t.symm.injective
      rw [LinearEquiv.symm_apply_apply, hi, LinearEquiv.symm_apply_apply]
    change t (c • t.symm (action g M)) = action g (t (c • t.symm M))
    have hsmul (N : V) : action h (c • N) = c • action h N :=
      (matrixAction h).map_smul c N
    rw [hi, ← hsmul, he]
  let φ : F → F := fun c => q c (Matrix.single 0 0 1) 0 0
  have hφ (c : F) (M : V) : q c M = φ c • M := by
    obtain ⟨d, hd⟩ := hq c
    have he : φ c = d := by simp [φ, hd, Matrix.single]
    exact he ▸ hd M
  have hmul (a b : F) (M : V) : q (a * b) M = q a (q b M) := by
    simp [q, mul_smul]
  let φhom : F →+* F :=
    { toFun := φ
      map_one' := by simp [φ, q, Matrix.single]
      map_mul' := by
        intro a b
        change q (a * b) (Matrix.single 0 0 1) 0 0 = φ a * φ b
        rw [hmul, hφ, hφ]
        simp [Matrix.single]
      map_zero' := by simp [φ, q]
      map_add' := by intro a b; simp [φ, q, add_smul] }
  refine ⟨RingEquiv.ofBijective φhom
    ⟨φhom.injective, Finite.surjective_of_injective φhom.injective⟩, fun c M => ?_⟩
  have he := hφ c (t M)
  change t (c • M) = φ c • t M
  simpa only [q, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.symm_apply_apply] using he

/-- Rank at most two excludes every nontrivial field twist. -/
theorem low_rank_field_linear (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (hr : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 2) :
    ∀ (c : F) (M : V), t (c • M) = c • t M := by
  obtain ⟨σ, hσ⟩ := normalizer_semilinear t ht
  have hs (c : F) : σ c = c := by
    by_contra hc
    have hb := Representation.BinaryOffender.NaturalTensor.finrank_le_twice_operatorFixedCodim
      t.toLinearMap σ.toRingHom ⟨c, hc⟩ hσ
    rw [finrank_binary] at hb
    change 8 ≤ 2 * finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) at hb
    omega
  simpa only [hs] using hσ

/-- The same low-rank actor has an F₄-linear lift with identical underlying action. -/
theorem low_rank_field_equiv (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (hr : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 2) :
    ∃ s : V ≃ₗ[F] V, s.restrictScalars (ZMod 2) = t := by
  let f : V →ₗ[F] V :=
    { toFun := t
      map_add' := t.map_add
      map_smul' := low_rank_field_linear t ht hr }
  exact ⟨LinearEquiv.ofBijective f t.bijective, by apply LinearEquiv.ext; intro M; rfl⟩

/-- A nonidentity low-rank actor has field rank one and binary rank two. -/
theorem low_rank_nonidentity (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (hr : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 2)
    (hne : t ≠ 1) :
    ∃ s : V ≃ₗ[F] V, s.restrictScalars (ZMod 2) = t ∧
      finrank F (LinearMap.range (s.toLinearMap - LinearMap.id)) = 1 ∧
      finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2 := by
  obtain ⟨s, hs⟩ := low_rank_field_equiv t ht hr
  have hdim := QuadraticForm.displacement_rank_restrictScalars (k := ZMod 2) s
  rw [hs, finrank_field] at hdim
  have hpos : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≠ 0 := by
    intro hz
    have he : t.toLinearMap - LinearMap.id = 0 :=
      LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
    exact hne (LinearEquiv.toLinearMap_injective (sub_eq_zero.mp he))
  exact ⟨s, hs, by omega, by omega⟩
end ClassicalOrthogonal.FourPlusMatrix.Binary
