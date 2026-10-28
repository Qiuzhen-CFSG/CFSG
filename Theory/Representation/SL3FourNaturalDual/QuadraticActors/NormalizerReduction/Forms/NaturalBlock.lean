module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.Forms.Summands

/-!
# The natural block of a binary SL₃(4) normalizer

A binary normalizer preserving the natural and dual summands restricts to an
invertible additive map on the natural module. Conjugating field scalars by
this map preserves the natural SL₃(4) commutant, so the scalar-centralizer
calculation constructs a field homomorphism. Finiteness of F₄ makes it a field
automorphism. Removing that twist gives a field-linear equivalence, whose
matrix supplies the natural block's explicit semilinear formula.

The matrix is an arbitrary element of GL₃(4); no determinant-one restriction
or automorphism classification is assumed. This proves the natural-block
contract used in the full normalizer assembly.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
13.8.20, printed p.955 (PDF p.972), natural-plus-dual SL₃(4) case.
-/

public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction

private theorem naturalBlock_semilinear (f : BinaryGL) (hf : f ∈ normalizer)
    (hp : PreservesSummands f) :
    ∃ σ : F ≃+* F, ∀ (c : F) (w : W), firstBlock f (c • w) = σ c • firstBlock f w := by
  let e := firstBlockEquiv f hp
  have hinv (w : W) : firstBlock f.symm w = e.symm w := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    change firstBlock f (f.symm (w, 0)).1 = w
    rw [firstBlock_fst f hp, LinearEquiv.apply_symm_apply]
  have hsmul (g : SL) (c : F) (w : W) : natural g (c • w) = c • natural g w := by
    exact Matrix.mulVec_smul g.val c w
  let q (c : F) : W →+ W :=
    { toFun := fun w => e (c • e.symm w)
      map_zero' := by simp
      map_add' := by intro v w; simp [smul_add] }
  have hq (c : F) : ∃ d : F, ∀ w, q c w = d • w := by
    apply natural_centralizer_scalar
    intro g w
    obtain ⟨h, hh, _⟩ := normalizer_blocks_intertwine f.symm (normalizer.inv_mem hf) g
    have hi (v : W) : e.symm (natural g v) = natural h (e.symm v) := by
      simpa only [hinv] using hh v
    have he (v : W) : e (natural h v) = natural g (e v) := by
      apply e.symm.injective
      rw [LinearEquiv.symm_apply_apply, hi, LinearEquiv.symm_apply_apply]
    change e (c • e.symm (natural g w)) = natural g (e (c • e.symm w))
    rw [hi, ← hsmul, he]
  let φ : F → F := fun c => q c (Pi.single 0 1) 0
  have hφ (c : F) (w : W) : q c w = φ c • w := by
    obtain ⟨d, hd⟩ := hq c
    have he : φ c = d := by simp [φ, hd]
    exact he ▸ hd w
  have hmul (a b : F) (w : W) : q (a * b) w = q a (q b w) := by
    simp [q, mul_smul]
  let φhom : F →+* F :=
    { toFun := φ
      map_one' := by simp [φ, q]
      map_mul' := by
        intro a b
        change q (a * b) (Pi.single 0 1) 0 = φ a * φ b
        rw [hmul, hφ, hφ]
        simp
      map_zero' := by simp [φ, q]
      map_add' := by intro a b; simp [φ, q, add_smul] }
  have hbij : Function.Bijective φhom :=
    ⟨φhom.injective, Finite.surjective_of_injective φhom.injective⟩
  refine ⟨RingEquiv.ofBijective φhom hbij, fun c w => ?_⟩
  have he := hφ c (e w)
  change e (c • w) = φhom c • e w
  simpa only [q, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.symm_apply_apply,
    RingEquiv.ofBijective_apply, φhom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      using he

/-- The natural block of every summand-preserving binary normalizer is an
actual invertible matrix followed in its domain by a field automorphism. -/
theorem naturalBlock_standard (f : BinaryGL) (hf : f ∈ normalizer)
    (hp : PreservesSummands f) :
    ∃ (M : Matrix.GeneralLinearGroup (Fin 3) F) (σ : F ≃+* F),
      ∀ w : W, firstBlock f w = M.val.mulVec (σ ∘ w) := by
  obtain ⟨σ, hσ⟩ := naturalBlock_semilinear f hf hp
  have hcancel (w : W) : σ.symm ∘ (σ ∘ w) = w := by
    funext i
    exact σ.symm_apply_apply (w i)
  let l : W →ₗ[F] W :=
    { toFun := fun w => firstBlock f (σ.symm ∘ w)
      map_add' := by
        intro v w
        have he : σ.symm ∘ (v + w) = (σ.symm ∘ v) + (σ.symm ∘ w) := by
          funext i
          exact map_add σ.symm _ _
        rw [he, map_add]
      map_smul' := by
        intro c w
        have he : σ.symm ∘ (c • w) = σ.symm c • (σ.symm ∘ w) := by
          funext i
          exact map_mul σ.symm _ _
        dsimp only [RingHom.id_apply]
        rw [he, hσ, RingEquiv.apply_symm_apply] }
  have hl : Function.Bijective l := by
    constructor
    · intro v w hvw
      have he := (firstBlock_bijective f hp).1 hvw
      funext i
      exact σ.symm.injective (congrFun he i)
    · intro w
      obtain ⟨v, hv⟩ := (firstBlock_bijective f hp).2 w
      refine ⟨σ ∘ v, ?_⟩
      change firstBlock f (σ.symm ∘ (σ ∘ v)) = w
      simpa only [hcancel] using hv
  let E := LinearEquiv.ofBijective l hl
  let M : Matrix.GeneralLinearGroup (Fin 3) F :=
    Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv E)
  refine ⟨M, σ, fun w => ?_⟩
  have he := congrArg (fun g : LinearMap.GeneralLinearGroup F W => g.val (σ ∘ w))
    (Matrix.GeneralLinearGroup.toLin.apply_symm_apply
      (LinearMap.GeneralLinearGroup.ofLinearEquiv E))
  change M.val.mulVec (σ ∘ w) = firstBlock f (σ.symm ∘ (σ ∘ w)) at he
  simpa only [hcancel] using he.symm

end Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
