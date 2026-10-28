module
public import Theory.Representation.BinaryOffender.Homogeneous.AutomorphismTwist
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Coverage

/-!
# Two supports in a binary linear-three homogeneous orbit

Inner automorphisms preserve a homogeneous Irr⁺ seed itself: an inner
intertwiner on its central image and full commutator generation remove
any central error. The checked inner/graph coverage of SL₃(2) therefore
bounds its orbit under any normalizing subgroup by two actual subspaces.
A moved orbit has stabilizer of index two. No assumption that the seed
is irreducible before quotienting its fixed space is needed.

Source: Aschbacher--Smith A.1.40--42 and the support argument in 14.6.22,
printed pp.31--32 and1038. The source consumer retains central covers;
identifying this orbit with the full component support is a separate step.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
  {K T : Subgroup G} {I : Submodule (ZMod 2) V}

private theorem graph_coset_difference {D : Type*} [Group D]
    (δ : MulAut D) (hi : Function.Involutive δ) (g h : D) :
    (MulAut.conj h * δ)⁻¹ * (MulAut.conj g * δ) = MulAut.conj (δ (h⁻¹ * g)) := by
  have hd : δ⁻¹ = δ := by
    apply MulEquiv.ext
    intro x
    apply δ.injective
    exact (δ.apply_symm_apply x).trans (hi x).symm
  rw [mul_inv_rev,hd,←(MulAut.conj : D →* MulAut D).map_inv h]
  apply MulEquiv.ext
  intro x
  simp only [MulAut.mul_apply,MulAut.conj_apply,inv_inv]
  simp only [map_mul,map_inv]
  rw [hi]
  group

/-- Inner component automorphisms preserve a homogeneous seed itself. -/
theorem IsIrrPlusWith.map_eq_of_inner
    (hI : IsIrrPlusWith ρ K T I) (t : T) (k : K)
    (ht : K.normalizerMonoidHom ⟨t,hI.normalizes t.property⟩ = MulAut.conj k) :
    I.map (ρ t.val) = I := by
  let σ := (quotientImage ρ K I hI.invariant).toRepresentation
  let c := LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom k⁻¹)
  apply hI.map_eq_of_central_twist ρ t c
  intro x v
  have hi : K.normalizerMonoidHom
      ⟨t.val⁻¹,hI.normalizes (T.inv_mem t.property)⟩ = MulAut.conj k⁻¹ := by
    change K.normalizerMonoidHom ((⟨t.val,hI.normalizes t.property⟩ : normalizer (K : Set G))⁻¹) = _
    rw [map_inv,ht,←map_inv]
  rw [hi]
  change σ k⁻¹ (σ x v) = σ (k⁻¹ * x * (k⁻¹)⁻¹) (σ k⁻¹ v)
  simp only [←Module.End.mul_apply,←map_mul]
  congr 2
  group

/-- A binary linear-three component has at most two literal homogeneous
seed conjugates, including when its natural quotient has a central cover. -/
theorem IsIrrPlusWith.linear_three_conjugates
    (hI : IsIrrPlusWith ρ K T I) (e : K ≃* Matrix.PSL3Two.SL) :
    ∃ t : T, ∀ s : T, I.map (ρ s.val) = I ∨ I.map (ρ s.val) = I.map (ρ t.val) := by
  let φ : T →* MulAut Matrix.PSL3Two.SL :=
    (MulAut.congr e).toMonoidHom.comp
      (K.normalizerMonoidHom.comp (inclusion hI.normalizes))
  have hinner (s : T) (g : Matrix.PSL3Two.SL) (hs : φ s = MulAut.conj g) :
      I.map (ρ s.val) = I := by
    apply hI.map_eq_of_inner ρ s (e.symm g)
    apply (MulAut.congr e).injective
    change φ s = (MulAut.congr e) (MulAut.conj (e.symm g))
    rw [hs]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  by_cases hfixed : ∀ s : T, I.map (ρ s.val) = I
  · exact ⟨1,fun s => Or.inl (hfixed s)⟩
  push Not at hfixed
  obtain ⟨t,ht⟩ := hfixed
  obtain ⟨h,hth | hth⟩ := Matrix.PSL3Two.MarkedAutomorphisms.inner_or_graph (φ t)
  · exact (ht (hinner t h hth)).elim
  refine ⟨t,fun s => ?_⟩
  obtain ⟨g,hsg | hsg⟩ := Matrix.PSL3Two.MarkedAutomorphisms.inner_or_graph (φ s)
  · exact Or.inl (hinner s g hsg)
  right
  have hs : φ (t⁻¹ * s) =
      MulAut.conj (Matrix.PSL3Two.MarkedAutomorphisms.diagram (h⁻¹ * g)) := by
    rw [map_mul,map_inv,hth,hsg]
    exact graph_coset_difference _ Matrix.PSL3Two.MarkedAutomorphisms.diagram_involutive g h
  have he := congrArg (Submodule.map (ρ t.val))
    (hinner (t⁻¹ * s) _ hs)
  rw [←Submodule.map_comp] at he
  have hm : (ρ t.val).comp (ρ (t⁻¹ * s).val) = ρ s.val := by
    change ρ t.val * ρ (t.val⁻¹ * s.val) = ρ s.val
    rw [←map_mul,mul_inv_cancel_left]
  rwa [hm] at he

/-- The full normalizer orbit is the sum of at most two actual seeds. -/
theorem IsIrrPlusWith.linear_three_orbit_span
    (hI : IsIrrPlusWith ρ K T I) (e : K ≃* Matrix.PSL3Two.SL) :
    ∃ t : T, orbitSpan ρ T I = I ⊔ I.map (ρ t.val) := by
  obtain ⟨t,ht⟩ := hI.linear_three_conjugates ρ e
  refine ⟨t,le_antisymm (iSup_le fun s => ?_)
    (sup_le (le_orbitSpan ρ T I) (le_iSup (fun s : T => I.map (ρ s.val)) t))⟩
  rcases ht s with h | h
  · rw [h]; exact le_sup_left
  · rw [h]; exact le_sup_right

/-- A moved binary-three homogeneous seed has stabilizer of index two
inside the supplied normalizing group. -/
theorem IsIrrPlusWith.linear_three_stabilizer_index
    (hI : IsIrrPlusWith ρ K T I) (e : K ≃* Matrix.PSL3Two.SL)
    (hmoved : orbitSpan ρ T I ≠ I) :
    (subspaceStabilizer ρ I).relIndex T = 2 := by
  obtain ⟨t,ht⟩ := hI.linear_three_conjugates ρ e
  have hnt : I.map (ρ t.val) ≠ I := by
    intro he
    apply hmoved
    exact orbitSpan_eq_self ρ (fun s hs => (subspace_map_eq_iff ρ I s).mp
      ((ht ⟨s,hs⟩).elim id (fun h => h.trans he)))
  apply Subgroup.index_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨t⁻¹,?_,fun s => ?_⟩
  · intro hh
    exact hnt ((subspace_map_eq_iff ρ I t.val).mpr
      ((subspaceStabilizer ρ I).inv_mem_iff.mp hh))
  rcases ht s with hs | hs
  · exact Or.inr ((subspace_map_eq_iff ρ I s.val).mp hs)
  · apply Or.inl
    apply (subspace_map_eq_iff ρ I (t⁻¹*s).val).mp
    have he := congrArg (Submodule.map (ρ t.val⁻¹)) hs
    rw [←Submodule.map_comp,←Submodule.map_comp] at he
    have hl : (ρ t.val⁻¹).comp (ρ s.val) = ρ (t⁻¹*s).val := (ρ.map_mul _ _).symm
    have hr : (ρ t.val⁻¹).comp (ρ t.val) = LinearMap.id := by
      change ρ t.val⁻¹ * ρ t.val = 1
      rw [←map_mul,inv_mul_cancel,map_one]
    simpa only [hl,hr,Submodule.map_id] using he

/-- The retained central covering kernels give a bound for the whole
normalizer orbit, without assuming either cover splits. -/
theorem IsIrrPlusWith.linear_three_orbit_finrank_le
    [FiniteDimensional (ZMod 2) V]
    (hI : IsIrrPlusWith ρ K T I) (e : K ≃* Matrix.PSL3Two.SL) :
    Module.finrank (ZMod 2) (orbitSpan ρ T I) ≤ 2 * Module.finrank (ZMod 2) I := by
  obtain ⟨t,ht⟩ := hI.linear_three_orbit_span ρ e
  rw [ht]
  exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (by
    have hh := Submodule.finrank_map_le (ρ t.val) I
    omega)

end Representation.BinaryOffender.Homogeneous
