module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane.Orbit
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Refinement
/-!
# Two noncentral factors from the transitive syntheme plane

The canonical plane in the six-letter natural module is Lagrangian.
Transitivity on its nonzero vectors makes it a chief factor. Orthogonal
complementation identifies the interval above the plane with the reverse
interval below it, so the quotient is also chief. Both factors have binary
dimension two and are therefore noncentral.

Source: Aschbacher–Smith, 13.7.6(3a), printed p.939.
-/
@[expose] public section
open BinaryPermutation Subgroup Module Representation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPlaneChief
open NaturalGeometry NaturalPairing NondegeneratePlane
open BinaryLinearThree.ParabolicCyclic.ChiefCounts
private theorem plane_perp : form.orthogonal canonicalPlane = canonicalPlane := by
  have hle : canonicalPlane ≤ form.orthogonal canonicalPlane := by
    intro v hv w hw
    obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hv
    obtain ⟨c,d,rfl⟩ := Submodule.mem_span_pair.mp hw
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
      form_alt _,pair_form]
    have h01 : (∑ x,rawPair 0 1 x * rawPair 2 3 x) = (0 : ZMod 2) := by decide
    have h10 : (∑ x,rawPair 2 3 x * rawPair 0 1 x) = (0 : ZMod 2) := by decide
    simp only [h01,h10,smul_zero,zero_add]
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,canonicalPlane_finrank,
    finrank_natural_even (Fin 6) (by decide)]
  decide
variable {A : Type*} [Group A]
  (f : A →* S)
  (hi : ∀ a, canonicalPlane.map (naturalRepresentation Ω (f a)) = canonicalPlane)
private def invariantPlane : Subrepresentation ((naturalRepresentation Ω).comp f) where
  toSubmodule := canonicalPlane
  apply_mem_toSubmodule a _v hv := hi a ▸ Submodule.mem_map_of_mem hv
private theorem node_invariant (U : Subrepresentation ((naturalRepresentation Ω).comp f)) (a : A) :
    U.toSubmodule.map (naturalRepresentation Ω (f a)) = U.toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact U.apply_mem_toSubmodule a hv
  · intro v hv
    refine ⟨naturalRepresentation Ω (f a⁻¹) v,U.apply_mem_toSubmodule a⁻¹ hv,?_⟩
    simp only [map_inv,← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
private noncomputable def perp (U : Subrepresentation ((naturalRepresentation Ω).comp f)) :
    Subrepresentation ((naturalRepresentation Ω).comp f) where
  toSubmodule := form.orthogonal U.toSubmodule
  apply_mem_toSubmodule a v hv := by
    have h := orthogonal_invariant U.toSubmodule (f a) (node_invariant f U a)
    exact h ▸ Submodule.mem_map_of_mem hv

/-- A transitive natural plane is a chief submodule. -/
private theorem plane_chief_bot
    (ho : ∀ u ∈ canonicalPlane, u ≠ 0 → ∀ v ∈ canonicalPlane, v ≠ 0 →
      ∃ a : A, naturalRepresentation Ω (f a) u = v) :
    (⊥ : Subrepresentation ((naturalRepresentation Ω).comp f)) ⋖ invariantPlane f hi := by
  apply covBy_of_eq_or_eq
  · apply lt_of_le_not_ge bot_le
    intro h
    have he : (pairVector 0 1 : V) = 0 := h (Submodule.subset_span (by simp))
    exact pairVector01_ne_zero he
  · intro U _ hU
    by_cases hb : U ≤ ⊥
    · exact Or.inl (le_antisymm hb bot_le)
    · right
      obtain ⟨u,hu,hu0⟩ := SetLike.not_le_iff_exists.mp hb
      apply le_antisymm hU
      intro v hv
      by_cases hv0 : v = 0
      · exact hv0 ▸ U.toSubmodule.zero_mem
      obtain ⟨a,rfl⟩ := ho u (hU hu) hu0 v hv hv0
      exact U.apply_mem_toSubmodule a hu

/-- Orthogonal complementation makes the upper interval chief as well. -/
private theorem plane_chief_top
    (ho : ∀ u ∈ canonicalPlane, u ≠ 0 → ∀ v ∈ canonicalPlane, v ≠ 0 →
      ∃ a : A, naturalRepresentation Ω (f a) u = v) :
    invariantPlane f hi ⋖ (⊤ : Subrepresentation ((naturalRepresentation Ω).comp f)) := by
  have hb := plane_chief_bot f hi ho
  apply covBy_of_eq_or_eq
  · apply lt_of_le_not_ge le_top
    intro h
    have he : (invariantPlane f hi).toSubmodule = ⊤ := top_unique h
    have hd := congrArg (fun W : Submodule (ZMod 2) V => finrank (ZMod 2) W) he
    change finrank (ZMod 2) canonicalPlane = finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) at hd
    rw [canonicalPlane_finrank,finrank_top,finrank_natural_even (Fin 6) (by decide)] at hd
    norm_num at hd
  · intro U hPU _
    have hperp : perp f U ≤ invariantPlane f hi := by
      intro v hv
      have hh : v ∈ form.orthogonal canonicalPlane :=
        LinearMap.BilinForm.orthogonal_le hPU hv
      rwa [plane_perp] at hh
    rcases hb.eq_or_eq bot_le hperp with hz | he
    · right
      apply Subrepresentation.toSubmodule_injective
      have h0 : form.orthogonal U.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hz
      have hd := congrArg (fun W : Submodule (ZMod 2) V => finrank (ZMod 2) W) h0
      rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,finrank_bot] at hd
      apply Submodule.eq_top_of_finrank_eq
      have hu : finrank (ZMod 2) U.toSubmodule ≤ finrank (ZMod 2) V := Submodule.finrank_le _
      change finrank (ZMod 2) V - finrank (ZMod 2) U.toSubmodule = 0 at hd
      exact le_antisymm hu (Nat.sub_eq_zero_iff_le.mp hd)
    · left
      apply Subrepresentation.toSubmodule_injective
      have hper : form.orthogonal U.toSubmodule = canonicalPlane := congrArg Subrepresentation.toSubmodule he
      have h := congrArg form.orthogonal hper
      rwa [LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl,plane_perp] at h
private theorem plane_noncentral
    (ho : ∀ u ∈ canonicalPlane, u ≠ 0 → ∀ v ∈ canonicalPlane, v ≠ 0 →
      ∃ a : A, naturalRepresentation Ω (f a) u = v) :
    ¬ Central (⊥ : Subrepresentation ((naturalRepresentation Ω).comp f)) (invariantPlane f hi) := by
  intro hc
  obtain ⟨a,ha⟩ := ho (pairVector 0 1) (Submodule.subset_span (by simp)) pairVector01_ne_zero
    (pairVector 2 3) (Submodule.subset_span (by simp)) pairVector23_ne_zero
  have hz : naturalRepresentation Ω (f a) (pairVector 0 1) - pairVector 0 1 = 0 :=
    hc a _ (Submodule.subset_span (by simp))
  rw [ha] at hz
  exact pairVector01_ne_pairVector23 (sub_eq_zero.mp hz).symm

private theorem quotient_noncentral
    (ho : ∀ u ∈ canonicalPlane, u ≠ 0 → ∀ v ∈ canonicalPlane, v ≠ 0 →
      ∃ a : A, naturalRepresentation Ω (f a) u = v) :
    ¬ Central (invariantPlane f hi) (⊤ : Subrepresentation ((naturalRepresentation Ω).comp f)) := by
  intro hc
  apply plane_noncentral f hi ho
  intro a x hx
  change naturalRepresentation Ω (f a) x - x = 0
  apply form_nondegenerate.1
  intro y
  have hy : naturalRepresentation Ω (f a⁻¹) y - y ∈ canonicalPlane := hc a⁻¹ y (by trivial)
  have hxp : x ∈ form.orthogonal canonicalPlane := plane_perp.symm ▸ hx
  have hzero : form x (naturalRepresentation Ω (f a⁻¹) y - y) = 0 :=
    form_alt.eq_iff.mp (hxp _ hy)
  have he := form_invariant (f a) x (naturalRepresentation Ω (f a⁻¹) y)
  simp only [map_inv,← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,
    Module.End.one_apply] at he
  rw [map_sub] at hzero
  change form x (naturalRepresentation Ω (f a⁻¹) y) - form x y = 0 at hzero
  rw [map_sub,LinearMap.sub_apply,he]
  simpa only [map_inv] using hzero

include hi in
/-- A group acting transitively on the canonical plane has exactly two
noncentral chief factors on the whole natural six-letter module. -/
theorem natural_two_noncentral
    (ho : ∀ u ∈ canonicalPlane, u ≠ 0 → ∀ v ∈ canonicalPlane, v ≠ 0 →
      ∃ a : A, naturalRepresentation Ω (f a) u = v) :
    HasCount ((naturalRepresentation Ω).comp f) 2 := by
  obtain ⟨s,h0,h1,hc⟩ := exists_series_count_join
    (exists_noncentral_chief_series ⊥ (invariantPlane f hi)
      (plane_chief_bot f hi ho) (plane_noncentral f hi ho))
    (exists_noncentral_chief_series (invariantPlane f hi) ⊤
      (plane_chief_top f hi ho) (quotient_noncentral f hi ho))
  exact ⟨s,h0,h1,hc⟩
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPlaneChief
