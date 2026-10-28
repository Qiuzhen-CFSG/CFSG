module

public import CFSG.Quasithin.ChapterG.Section12.Geometry

/-!
# Transport of the hyperplane-transvection condition

Conjugation transports every functional on the perpendicular hyperplane,
so condition (*) is stable under the original form-preserving group.
Combined with irreducibility and the hyperplane identification, this
constructs the exact input pair needed by G.12.1 in the application G.12.12.
The invariant symplectic form is an explicit independent input here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.12.12(3)
and the application to G.12.1 on printed p.374.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section12
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Condition (*) is stable under the same group's action, with the
hyperplane functionals transported by the actual linear map. -/
theorem GoodVector.conjugate
    {G : Subgroup (V ≃ₗ[ZMod 2] V)} {B : LinearMap.BilinForm (ZMod 2) V}
    {hB : B.IsAlt} {v : V} (h : GoodVector G B hB v)
    (hG : G ≤ formStabilizer B) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ G) :
    GoodVector G B hB (g v) := by
  rw [goodVector_iff hB hG]
  refine ⟨fun he => h.nonzero (g.injective (he.trans g.map_zero.symm)), ?_⟩
  intro φ hφ
  let i : (B v).ker →ₗ[ZMod 2] (B (g v)).ker :=
    (g.toLinearMap.comp (B v).ker.subtype).codRestrict _ (by
      intro w
      change B (g v) (g w) = 0
      rw [hG hg v w]
      exact w.property)
  have hi : i ⟨v, hB v⟩ = ⟨g v, hB (g v)⟩ := rfl
  obtain ⟨q, hq⟩ := h.full (φ.comp i) (by
    simpa only [LinearMap.comp_apply, hi] using hφ)
  refine ⟨g * q.val * g⁻¹, G.mul_mem (G.mul_mem hg q.property.1) (G.inv_mem hg), ?_⟩
  intro w
  have hw : B v (g.symm w) = 0 := by
    have he := hG hg v (g.symm w)
    rw [g.apply_symm_apply] at he
    exact he.symm.trans w.property
  let w' : (B v).ker := ⟨g.symm w, hw⟩
  have hiw : i w' = w := by
    apply Subtype.ext
    exact g.apply_symm_apply w
  have he := congrArg g (hq w')
  simp only [map_add, map_smul, LinearMap.comp_apply, hiw] at he
  change g (q.val (g.symm w)) = g (g.symm w) + φ w • g v at he
  simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, g.apply_symm_apply] using he

variable [FiniteDimensional (ZMod 2) V]

/-- The full orbit inclusion in G.12.12(3), given the form from part (1). -/
theorem ModuleHypotheses.orbit_good
    {H K Q : Subgroup (V ≃ₗ[ZMod 2] V)} {W : Submodule (ZMod 2) V} {v : W}
    (h : ModuleHypotheses H K Q W v)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hpres : K ⊔ Q ≤ formStabilizer B) {k : V ≃ₗ[ZMod 2] V} (hk : k ∈ K) :
    GoodVector (K ⊔ Q) B hB (k v) :=
  (h.goodVector B hB hnd hpres).conjugate hpres ((show K ≤ K ⊔ Q from le_sup_left) hk)

/-- G.12.12 supplies all inputs of G.12.1 for the actual generated subgroup,
with no recognition premise. Only the existence of the form remains explicit. -/
theorem ModuleHypotheses.classification_inputs
    {H K Q : Subgroup (V ≃ₗ[ZMod 2] V)} {W : Submodule (ZMod 2) V} {v : W}
    (h : ModuleHypotheses H K Q W v)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hpres : K ⊔ Q ≤ formStabilizer B) :
    ∃ u : V, ClassificationHypotheses (K ⊔ Q) B u v := by
  obtain ⟨k, hk, hkw⟩ := h.exists_outside
  have heq := h.hyperplane_eq B hB hnd hpres
  have hpair : B (k v) v ≠ 0 := by
    intro hz
    apply hkw
    exact heq.ge (hB.eq_iff.mp hz)
  obtain ⟨n, hn⟩ := AlternatingForm.even_finrank B hB hnd
  have hd := h.dimension
  exact ⟨k v, ⟨hB, hnd, hpres, by omega,
    h.orbit_good B hB hnd hpres hk, h.goodVector B hB hnd hpres, hpair⟩⟩

/-- If the ambient group preserves the form, the very same pair supplies
G.12.1's inputs for its action as well. -/
theorem ModuleHypotheses.ambient_classification_inputs
    {H K Q : Subgroup (V ≃ₗ[ZMod 2] V)} {W : Submodule (ZMod 2) V} {v : W}
    (h : ModuleHypotheses H K Q W v)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hpres : H ≤ formStabilizer B) :
    ∃ u : V, ClassificationHypotheses H B u v := by
  have hle : K ⊔ Q ≤ H := sup_le h.K_le h.Q_le
  obtain ⟨u, hu⟩ := h.classification_inputs B hB hnd (hle.trans hpres)
  exact ⟨u, ⟨hu.alternating, hu.nondegenerate, hpres, hu.dimension,
    hu.good_u.mono hle hpres, hu.good_v.mono hle hpres, hu.pairing⟩⟩

end CFSG.Quasithin.ChapterG.Section12
