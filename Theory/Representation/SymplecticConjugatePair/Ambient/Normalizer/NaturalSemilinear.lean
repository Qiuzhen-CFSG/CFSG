module

public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer.Coordinates

/-!
# Semilinear normalizers from the natural scalar commutant

Assume that the binary commutant of the genuine derived symplectic action
consists of coefficient scalars. Conjugating these scalars by a binary
normalizer constructs a field automorphism. Removing its entrywise action
leaves an invertible field-linear normalizer.

Pulling back the standard symplectic form and identifying the space with its
dual gives a commuting endomorphism, hence a scalar by the same hypothesis.
The resulting multiplier is nonzero. Square-root surjectivity in a finite
field of characteristic two then rescales the operator to an actual
symplectic matrix. Field automorphisms preserve the literal derived image
because they preserve the characteristic commutator subgroup. The argument
therefore includes the field of order two without replacing the derived group
by the full symplectic group.

This is a conditional normalizer calculation used in the paired-module
argument of Aschbacher–Smith H.7, printed pp.388–389 of `refs/quasithin.pdf`,
with the paired setup on printed p.696. The scalar-commutant hypothesis is
explicit and is discharged by the parent paired-normalizer assembly.
-/

public section
open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace SymplecticConjugatePair.Ambient.Normalizer
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [CharP F 2] in
private lemma natural_intertwines
    (e : Vector F ≃ₗ[ZMod 2] Vector F) (he : e ∈ naturalNormalizer)
    (x : commutator (Sp F)) :
    ∃ y : commutator (Sp F), ∀ v,
      e (naturalDerivedAction x v) = naturalDerivedAction y (e v) := by
  have hm := (Subgroup.mem_normalizer_iff.mp he
    (linearAction naturalDerivedAction x)).mp ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hm
  refine ⟨y, fun v => ?_⟩
  have h := congrArg (fun a : Vector F ≃ₗ[ZMod 2] Vector F => a (e v)) hy
  change naturalDerivedAction y (e v) = e (naturalDerivedAction x (e.symm (e v))) at h
  simpa only [LinearEquiv.symm_apply_apply] using h.symm

omit [CharP F 2] in
private theorem natural_semilinear
    (hscalar : ∀ q : Vector F →ₗ[ZMod 2] Vector F,
      (∀ (x : commutator (Sp F)) v,
        q (naturalDerivedAction x v) = naturalDerivedAction x (q v)) →
      ∃ c : F, ∀ v, q v = c • v)
    (e : Vector F ≃ₗ[ZMod 2] Vector F) (he : e ∈ naturalNormalizer) :
    ∃ σ : F ≃+* F, ∀ (c : F) v, e (c • v) = σ c • e v := by
  let q (c : F) : Vector F →ₗ[ZMod 2] Vector F :=
    { toFun := fun v => e (c • e.symm v)
      map_add' := by intro v w; simp [smul_add]
      map_smul' := by
        intro a v
        dsimp
        rw [e.symm.map_smul a, smul_comm c a, e.map_smul a] }
  have hq (c : F) : ∃ d : F, ∀ v, q c v = d • v := by
    apply hscalar
    intro x v
    obtain ⟨y, hy⟩ := natural_intertwines e.symm (naturalNormalizer.inv_mem he) x
    have hi (w : Vector F) : e (naturalDerivedAction y w) = naturalDerivedAction x (e w) := by
      apply e.symm.injective
      rw [LinearEquiv.symm_apply_apply, hy, LinearEquiv.symm_apply_apply]
    change e (c • e.symm (naturalDerivedAction x v)) =
      naturalDerivedAction x (e (c • e.symm v))
    rw [hy]
    have hs (w : Vector F) : naturalDerivedAction y (c • w) =
        c • naturalDerivedAction y w := (symplecticNatural 2 y.val).map_smul c w
    rw [← hs, hi]
  let φ : F → F := fun c => q c (Pi.single (.inl 0) 1) (.inl 0)
  have hφ (c : F) (v : Vector F) : q c v = φ c • v := by
    obtain ⟨d, hd⟩ := hq c
    have h : φ c = d := by simp [φ, hd]
    exact h ▸ hd v
  have hmul (a b : F) (v : Vector F) : q (a * b) v = q a (q b v) := by
    simp [q, mul_smul]
  let φhom : F →+* F :=
    { toFun := φ
      map_one' := by simp [φ, q]
      map_mul' := by
        intro a b
        change q (a * b) (Pi.single (.inl 0) 1) (.inl 0) = φ a * φ b
        rw [hmul, hφ, hφ]
        simp
      map_zero' := by simp [φ, q]
      map_add' := by intro a b; simp [φ, q, add_smul] }
  refine ⟨RingEquiv.ofBijective φhom
    ⟨φhom.injective, Finite.surjective_of_injective φhom.injective⟩, fun c v => ?_⟩
  have h := hφ c (e v)
  change e (c • v) = φ c • e v
  simpa only [q, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply] using h

omit [Finite F] [CharP F 2] in
private lemma field_mem_naturalNormalizer (σ : F ≃+* F) :
    fieldVector σ ∈ naturalNormalizer (F := F) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (linearAction (naturalDerivedAction (F := F))).range.map
    (MulAut.conj (fieldVector σ)).toMonoidHom =
      (linearAction (naturalDerivedAction (F := F))).range
  exact range_map_conj_of_intertwines
    (naturalDerivedAction (F := F)) (naturalDerivedAction (F := F))
    (MulAut.characteristic (commutator (Sp F)) (fieldAutomorphism σ))
    (fieldVector σ) (fun x v => fieldVector_intertwines σ x.val v)


omit [Finite F] [CharP F 2] in
private theorem linear_normalizer_similitude
    (hscalar : ∀ q : Vector F →ₗ[ZMod 2] Vector F,
      (∀ (x : commutator (Sp F)) v,
        q (naturalDerivedAction x v) = naturalDerivedAction x (q v)) →
      ∃ c : F, ∀ v, q v = c • v)
    (A : Vector F ≃ₗ[F] Vector F)
    (hA : A.restrictScalars (ZMod 2) ∈ naturalNormalizer) :
    ∃ c : F, c ≠ 0 ∧ ∀ v w, form F (A v) (A w) = c * form F v w := by
  let B := (form F).comp A.toLinearMap A.toLinearMap
  let T : Module.End F (Vector F) :=
    ((form F).toDual TwoLocalCover.form_nondegenerate).symm.toLinearMap.comp B
  have hT (v w : Vector F) : form F (T v) w = form F (A v) (A w) :=
    LinearMap.BilinForm.apply_toDual_symm_apply
      (hB := TwoLocalCover.form_nondegenerate) (B v) w
  have hB (x : commutator (Sp F)) (v w : Vector F) :
      form F (A (naturalDerivedAction x v)) (A (naturalDerivedAction x w)) =
        form F (A v) (A w) := by
    obtain ⟨y, hy⟩ := natural_intertwines (A.restrictScalars (ZMod 2)) hA x
    have hy' (v : Vector F) : A (naturalDerivedAction x v) =
        naturalDerivedAction y (A v) := hy v
    rw [hy', hy']
    exact preserves_form y.val (A v) (A w)
  obtain ⟨c, hc⟩ := hscalar (T.restrictScalars (ZMod 2)) (by
    intro x v
    change T (naturalDerivedAction x v) = naturalDerivedAction x (T v)
    apply ((form F).toDual TwoLocalCover.form_nondegenerate).injective
    apply LinearMap.ext
    intro w
    obtain ⟨w, rfl⟩ := (linearAction (naturalDerivedAction (F := F)) x).surjective w
    change form F (T (naturalDerivedAction x v)) (naturalDerivedAction x w) =
      form F (naturalDerivedAction x (T v)) (naturalDerivedAction x w)
    rw [hT, hB, ← hT]
    exact (preserves_form x.val (T v) w).symm)
  have hmul (v w : Vector F) : form F (A v) (A w) = c * form F v w := by
    rw [← hT, show T v = c • v from hc v]
    simp
  refine ⟨c, ?_, hmul⟩
  intro hc0
  have h := hmul (A.symm (Pi.single (.inl 0) 1)) (A.symm (Pi.single (.inr 0) 1))
  simp [hc0, form_apply, Pi.single_apply] at h

omit [Algebra (ZMod 2) F] in
private theorem similitude_eq_scalar_symplectic
    (A : Vector F ≃ₗ[F] Vector F) (c : F) (hc : c ≠ 0)
    (hmul : ∀ v w, form F (A v) (A w) = c * form F v w) :
    ∃ (a : Fˣ) (g : Sp F), ∀ v, A v = a.val • (g • v) := by
  obtain ⟨b, hb⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F)) c⁻¹
  change b ^ 2 = c⁻¹ at hb
  have hnorm : b * b * c = 1 := by
    rw [← pow_two, hb, inv_mul_cancel₀ hc]
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hnorm
  let L : Module.End F (Vector F) := b • A.toLinearMap
  have hL (v w : Vector F) : form F (L v) (L w) = form F v w := by
    change form F (b • A v) (b • A w) = _
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hmul]
    calc
      b * (b * (c * form F v w)) = (b * b * c) * form F v w := by ring
      _ = form F v w := by rw [hnorm, one_mul]
  let g : Sp F := ⟨LinearMap.toMatrix' L, by
    apply SymplecticGroup.mem_iff'.mpr
    have he := Matrix.toBilin'_comp (-Matrix.J (Fin 2) F)
      (LinearMap.toMatrix' L) (LinearMap.toMatrix' L)
    have hpres : (form F).comp L L = form F := by
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      exact hL v w
    simp only [Matrix.toLin'_toMatrix'] at he
    have hm := Matrix.toBilin'.injective (he.symm.trans hpres)
    simpa [Matrix.mul_neg, Matrix.neg_mul, form] using hm⟩
  have hg (v : Vector F) : g • v = b • A v :=
    LinearMap.toMatrix'_mulVec L v
  refine ⟨(Units.mk0 b hb0)⁻¹, g, fun v => ?_⟩
  rw [hg]
  change A v = b⁻¹ • b • A v
  rw [inv_smul_smul₀ hb0]

/-- A scalar commutant forces every binary normalizer of the genuine derived
natural image to be a coefficient scalar times an inner-field operator. -/
theorem naturalNormalizer_semilinear_of_scalar_commutant
    (hscalar : ∀ q : Vector F →ₗ[ZMod 2] Vector F,
      (∀ (x : commutator (Sp F)) v,
        q (naturalDerivedAction x v) = naturalDerivedAction x (q v)) →
      ∃ c : F, ∀ v, q v = c • v)
    (e : Vector F ≃ₗ[ZMod 2] Vector F) (he : e ∈ naturalNormalizer) :
    ∃ (a : Fˣ) (g : Sp F) (σ : F ≃+* F),
      ∀ v, e v = a.val • innerFieldVector g σ v := by
  obtain ⟨σ, hσ⟩ := natural_semilinear hscalar e he
  let l : Vector F →ₗ[F] Vector F :=
    { toFun := fun v => e (fieldVector σ.symm v)
      map_add' := by intro v w; rw [map_add, map_add]
      map_smul' := by
        intro c v
        have h : fieldVector σ.symm (c • v) = σ.symm c • fieldVector σ.symm v := by
          funext i
          exact map_mul σ.symm c (v i)
        dsimp only [RingHom.id_apply]
        rw [h, hσ, σ.apply_symm_apply] }
  have hl : Function.Bijective l := e.bijective.comp (fieldVector σ.symm).bijective
  let A := LinearEquiv.ofBijective l hl
  have hAb : A.restrictScalars (ZMod 2) = e * fieldVector σ.symm := by
    ext v i
    rfl
  have hA : A.restrictScalars (ZMod 2) ∈ naturalNormalizer := by
    rw [hAb]
    exact naturalNormalizer.mul_mem he (field_mem_naturalNormalizer σ.symm)
  obtain ⟨c, hc, hmul⟩ := linear_normalizer_similitude hscalar A hA
  obtain ⟨a, g, hg⟩ := similitude_eq_scalar_symplectic A c hc hmul
  refine ⟨a, g, σ, fun v => ?_⟩
  have hv : A (fieldVector σ v) = e v := by
    change e (fieldVector σ.symm (fieldVector σ v)) = e v
    congr 1
    ext i
    exact σ.symm_apply_apply (v i)
  rw [← hv, hg]
  rfl

end SymplecticConjugatePair.Ambient.Normalizer
