module

public import Theory.Representation.SL3DoubledNaturalOffenders.NormalizerCoverage.Semilinear

/-!
# General linear factors of doubled natural normalizers

A field-linear normalizer of the identically marked doubled natural SL₃ action
is the product of a genuine GL₃ matrix on the natural coordinates and a genuine
GL₂ matrix on the multiplicity coordinates. This includes the field with two
elements.

Normalization makes every block intertwine the same two natural actions. A
nonzero block has trivial kernel: elementary transvections propagate any nonzero
kernel vector to every coordinate vector. Its inverse removes the conjugated
natural action, leaving an invertible operator in the published multiplicity
commutant. The commutant unit theorem then supplies the invertible GL₂ matrix.

The final consumer applies the published odd-degree involution linearity theorem.
It discharges factor extraction in normalizer coverage; determinant normalization
and the source offender localization remain separate steps.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), B.5.9(3) and B.5.10(2), printed pp.107–109.
-/

public section

namespace Representation.SL3DoubledNaturalOffenders
open Matrix
variable {F : Type*} [Field F]

private theorem natural_transvection {i j : Fin 3} (hij : i ≠ j) (a : F)
    (v : Natural F) :
    (SpecialLinearGroup.transvection hij a).val.mulVec v =
      v + Pi.single i (a * v j) := by
  change ((1 : Matrix (Fin 3) (Fin 3) F) + Matrix.single i j a).mulVec v = _
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

private theorem intertwiner_injective (f : Natural F →ₗ[F] Natural F)
    (hf : f ≠ 0) (φ : SL F → SL F)
    (he : ∀ (g : SL F) v, f (g.val.mulVec v) = (φ g).val.mulVec (f v)) :
    Function.Injective f := by
  apply (LinearMap.ker_eq_bot).mp
  apply (LinearMap.ker_eq_bot').mpr
  intro v hv
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    apply hne
    funext j
    simpa using not_exists.mp h j
  have hstep (w : Natural F) (hw : f w = 0) {i j : Fin 3} (hij : i ≠ j) (a : F) :
      f (Pi.single i (a * w j)) = 0 := by
    have h := he (SpecialLinearGroup.transvection hij a) w
    rw [natural_transvection, map_add, hw, Matrix.mulVec_zero, zero_add] at h
    exact h
  have hs (i : Fin 3) (a : F) : f (Pi.single i a) = 0 := by
    by_cases hij : i = j
    · obtain ⟨k, hkj⟩ : ∃ k : Fin 3, k ≠ j := by fin_cases j <;> decide
      have hk : f (Pi.single k 1) = 0 := by
        simpa [hj] using hstep v hv hkj (v j)⁻¹
      subst i
      simpa using hstep (Pi.single k 1) hk hkj.symm a
    · simpa [hj] using hstep v hv hij (a / v j)
  apply hf
  apply LinearMap.ext
  intro w
  have hw : w = ∑ i : Fin 3, Pi.single i (w i) := by
    funext i
    simp [Finset.sum_apply]
  rw [hw, map_sum]
  simp [hs]

variable [Algebra (ZMod 2) F]

private theorem normalizer_intertwines (b : Ambient F) (hb : b ∈ normalizer F) :
    ∃ φ : SL F → SL F, ∀ (g : SL F) (v : Space F),
      (b : Module.End (ZMod 2) (Space F)) (representation F g v) =
        representation F (φ g) ((b : Module.End (ZMod 2) (Space F)) v) := by
  have hex (g : SL F) : ∃ h : SL F,
      (representation F).asGroupHom h = b * (representation F).asGroupHom g * b⁻¹ :=
    (Subgroup.mem_normalizer_iff.mp hb ((representation F).asGroupHom g)).mp ⟨g, rfl⟩
  choose φ hφ using hex
  refine ⟨φ, fun g v => ?_⟩
  have he : representation F (φ g) = (b : Module.End (ZMod 2) (Space F)) *
      representation F g * (↑b⁻¹ : Module.End (ZMod 2) (Space F)) :=
    congrArg Units.val (hφ g)
  have ht := congrArg (fun t : Module.End (ZMod 2) (Space F) =>
    t * (b : Module.End (ZMod 2) (Space F))) he
  have ht' : representation F (φ g) * (b : Module.End (ZMod 2) (Space F)) =
      (b : Module.End (ZMod 2) (Space F)) * representation F g := by
    simpa [mul_assoc] using ht
  exact (LinearMap.congr_fun ht' v).symm

private theorem representation_single (g : SL F) (j : Fin 2) (v : Natural F) :
    representation F g (Pi.single j v) = Pi.single j (g.val.mulVec v) := by
  funext i
  by_cases hi : i = j <;> simp [hi, Pi.single_eq_of_ne]

/-- A field-linear doubled-natural normalizer has actual invertible tensor factors. -/
theorem normalizer_linear_tensor_factors [Finite F] (b : Ambient F)
    (hb : b ∈ normalizer F)
    (hlin : ∀ (a : F) (v : Space F),
      (b : Module.End (ZMod 2) (Space F)) (a • v) =
        a • (b : Module.End (ZMod 2) (Space F)) v) :
    ∃ g : (Matrix (Fin 3) (Fin 3) F)ˣ,
      ∃ c : (Matrix (Fin 2) (Fin 2) F)ˣ,
        ∀ (v : Space F) (i : Fin 2),
          (b : Module.End (ZMod 2) (Space F)) v i =
            g.val.mulVec (multiplicity F c.val v i) := by
  classical
  obtain ⟨φ, hφ⟩ := normalizer_intertwines b hb
  let block (i j : Fin 2) : Natural F →ₗ[F] Natural F :=
    { toFun := fun v => (b : Module.End (ZMod 2) (Space F)) (Pi.single j v) i
      map_add' v w := by simp [Pi.single_add]
      map_smul' a v := by simp [Pi.single_smul, hlin] }
  have hblock (i j : Fin 2) (g : SL F) (v : Natural F) :
      block i j (g.val.mulVec v) = (φ g).val.mulVec (block i j v) := by
    change (b : Module.End (ZMod 2) (Space F)) (Pi.single j (g.val.mulVec v)) i = _
    rw [← representation_single]
    exact congrFun (hφ g (Pi.single j v)) i
  have hex : ∃ i : Fin 2, block i 0 ≠ 0 := by
    by_contra h
    have hz : (b : Module.End (ZMod 2) (Space F))
        (Pi.single 0 (fun _ => 1)) = 0 := by
      funext i
      exact LinearMap.congr_fun (not_not.mp (not_exists.mp h i)) (fun _ => 1)
    have he := (LinearMap.GeneralLinearGroup.toLinearEquiv b).injective
      (hz.trans (map_zero (b : Module.End (ZMod 2) (Space F))).symm)
    have hf := congrFun (congrFun he 0) 0
    simp at hf
  obtain ⟨i, hi⟩ := hex
  have hinj := intertwiner_injective (block i 0) hi φ (hblock i 0)
  let e : Natural F ≃ₗ[F] Natural F := LinearEquiv.ofBijective (block i 0)
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  have he (g : SL F) (v : Natural F) :
      e (g.val.mulVec v) = (φ g).val.mulVec (e v) := hblock i 0 g v
  let E : Ambient F := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (LinearEquiv.piCongrRight fun _ : Fin 2 => e.restrictScalars (ZMod 2))
  have hcentral : E⁻¹ * b ∈ Subgroup.centralizer (component F : Set (Ambient F)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro a ⟨g, rfl⟩
    apply Units.ext
    apply LinearMap.ext
    intro v
    funext j
    change g.val.mulVec (e.symm ((b : Module.End (ZMod 2) (Space F)) v j)) =
      e.symm ((b : Module.End (ZMod 2) (Space F)) (representation F g v) j)
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
    exact (congrFun (hφ g v) j).symm
  obtain ⟨c, hc⟩ := centralizer_units (E⁻¹ * b) hcentral
  let g : (Matrix (Fin 3) (Fin 3) F)ˣ :=
    Units.map (LinearMap.toMatrixAlgEquiv' :
      Module.End F (Natural F) ≃ₐ[F] Matrix (Fin 3) (Fin 3) F).toMonoidHom
      (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  refine ⟨g, c, fun v j => ?_⟩
  have ht := congrFun (LinearMap.congr_fun hc v) j
  change e.symm ((b : Module.End (ZMod 2) (Space F)) v j) = multiplicity F c.val v j at ht
  have hg (w : Natural F) : g.val.mulVec w = e w :=
    LinearMap.toMatrix'_mulVec e.toLinearMap w
  rw [hg, ← ht, e.apply_symm_apply]

/-- The field-linearity theorem supplies GL tensor factors for every involution
of the marked normalizer over an odd-degree binary field, including `F₂`. -/
theorem normalizer_involution_tensor_factors [Finite F] {m : ℕ} (hodd : Odd m)
    (hc : Nat.card F = 2 ^ m) (b : Ambient F) (hb : b ∈ normalizer F)
    (hb2 : b ^ 2 = 1) :
    ∃ g : (Matrix (Fin 3) (Fin 3) F)ˣ,
      ∃ c : (Matrix (Fin 2) (Fin 2) F)ˣ,
        ∀ (v : Space F) (i : Fin 2),
          (b : Module.End (ZMod 2) (Space F)) v i =
            g.val.mulVec (multiplicity F c.val v i) :=
  normalizer_linear_tensor_factors b hb
    (normalizer_involution_linear hodd hc b hb hb2)

end Representation.SL3DoubledNaturalOffenders
