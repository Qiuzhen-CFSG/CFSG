module
public import Theory.Representation.BinaryHyperplaneDisplacement
public import Theory.Representation.SpecialLinearNatural.BinaryPointStabilizer
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.Representation.BinaryIsometryRadicals

/-!
# The order-two obstruction for a binary parabolic actor

A subgroup of order two normalized by a point stabilizer is centralized by it.
Its displacement range would therefore be an invariant plane in the seed:
faithful rank bounds make the range at least a plane, while movement of the
hyperplane into the marked line makes it at most a plane. The full GL₃(2)
point stabilizer is transitive outside that line and preserves no plane.

This removes the order-two case after the hyperplane counting bound in
Aschbacher--Smith 12.9.4, printed pp.859--860. The normality is relative to
the actual point stabilizer inside the supplied seed actor.
-/

public noncomputable section
open Module Subgroup
namespace Representation.BinaryHyperplaneDisplacement

private theorem no_invariant_plane
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (hW : finrank (ZMod 2) W = 3) (v : W) (hv : v ≠ 0)
    (R : Submodule (ZMod 2) W) (hR : finrank (ZMod 2) R = 2)
    (hstable : ∀ φ : W ≃ₗ[ZMod 2] W, φ v = v → ∀ w ∈ R, φ w ∈ R) : False := by
  let e := (Module.finBasisOfFinrankEq (ZMod 2) W hW).equivFun
  have hnot : ¬ R ≤ Submodule.span (ZMod 2) {v} := by
    intro hh
    have := Submodule.finrank_mono hh
    rw [hR,finrank_span_singleton hv] at this
    omega
  obtain ⟨w,hwR,hw⟩ := SetLike.not_le_iff_exists.mp hnot
  have hw0 : w ≠ 0 := fun he => hw (he ▸ Submodule.zero_mem _)
  have hwv : w ≠ v := fun he => hw (he ▸ Submodule.mem_span_singleton_self _)
  have hall (z : W) (hz0 : z ≠ 0) (hzv : z ≠ v) : z ∈ R := by
    obtain ⟨g,hgv,hgw⟩ := BinaryPointStabilizer.exists_point_fixer (e v) (e w) (e z)
      (fun hh => hv (e.injective (hh.trans e.map_zero.symm)))
      (fun hh => hw0 (e.injective (hh.trans e.map_zero.symm)))
      (fun hh => hz0 (e.injective (hh.trans e.map_zero.symm)))
      (fun hh => hwv (e.injective hh)) (fun hh => hzv (e.injective hh))
    let t := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)
      ((Representation.specialLinearNatural 3).asGroupHom g)
    let φ := (e.trans t).trans e.symm
    have hφv : φ v = v := by
      apply e.injective
      change e (e.symm (t (e v))) = e v
      rw [e.apply_symm_apply]
      exact hgv
    have hφw : φ w = z := by
      apply e.injective
      change e (e.symm (t (e w))) = e z
      rw [e.apply_symm_apply]
      exact hgw
    exact hφw ▸ hstable φ hφv w hwR
  have hvR : v ∈ R := by
    have hsum : w + v ≠ 0 := by
      intro he
      have he' : w = -v := eq_neg_of_add_eq_zero_left he
      have hn : -v = v := neg_eq_iff_add_eq_zero.mpr (ZModModule.add_self v)
      exact hwv (he'.trans hn)
    have hsumv : w + v ≠ v := fun he => hw0 (add_right_cancel (he.trans (zero_add v).symm))
    have hh := R.sub_mem (hall (w+v) hsum hsumv) hwR
    simpa only [add_sub_cancel_left] using hh
  have ht : R = ⊤ := by
    apply top_unique
    intro z _
    by_cases hz : z = 0
    · exact hz ▸ R.zero_mem
    by_cases hzv : z = v
    · exact hzv ▸ hvR
    exact hall z hz hzv
  rw [ht,finrank_top,hW] at hR
  omega

/-- A two-element actor cannot be normal in the full point stabilizer on a
three-dimensional isotropic seed when its hyperplane movement is in that point. -/
theorem not_card_two_of_full_seed_action
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (hInv : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    (W : Submodule (ZMod 2) V) (hd : finrank (ZMod 2) W = 3)
    (hW : W = B.orthogonal W) (v : W) (hv : (v:V) ≠ 0)
    (S D : Subgroup G)
    (hfull : ∀ φ : W ≃ₗ[ZMod 2] W, ∃ s ∈ S, ∀ w : W, ρ s w = (φ w : V))
    (hnorm : ∀ s ∈ S, ρ s v = v → s ∈ normalizer (D : Set G))
    (hfix : ∀ a ∈ D, ∀ w ∈ W, ρ a w = w)
    (hmove : ∀ a ∈ D, ∀ w ∈ (B (v:V)).ker, ρ a w - w ∈ Submodule.span (ZMod 2) {(v:V)})
    (hlower : ∀ a ∈ D, a ≠ 1 → 2 ≤ finrank (ZMod 2) (ρ a - LinearMap.id).range) :
    Nat.card D ≠ 2 := by
  intro hcard
  have hnD : D ≠ ⊥ := by intro he; rw [he,Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩] at hcard; omega
  obtain ⟨a',ha'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hnD
  let a : G := a'
  have ha : a ∈ D := a'.property
  have ha1 : a ≠ 1 := fun hh => ha' (Subtype.ext hh)
  let N := ρ a - LinearMap.id
  let H := (B (v:V)).ker
  have hH : finrank (ZMod 2) H + 1 = finrank (ZMod 2) V :=
    Module.Dual.finrank_ker_add_one_of_ne_zero
      (fun hz => hv (hB.1 _ (fun w => LinearMap.congr_fun hz w)))
  have hNW : N.range ≤ W := by
    intro z hz
    obtain ⟨u,rfl⟩ := hz
    apply hW.ge
    intro w hw
    change B w (ρ a u-u) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    calc
      B w (ρ a u) = B (ρ a w) (ρ a u) := by rw [hfix a ha w hw]
      _ = B w u := hInv a w u
  let f := N.comp H.subtype
  have hr : f.range ≤ Submodule.span (ZMod 2) {(v:V)} := by
    rintro z ⟨w,rfl⟩
    exact hmove a ha w w.property
  have hf := f.finrank_range_add_finrank_ker
  have hrle := Submodule.finrank_mono hr
  rw [finrank_span_singleton hv] at hrle
  have hkle : f.ker.map H.subtype ≤ N.ker := by
    rintro z ⟨w,hw,rfl⟩
    exact hw
  have hkle' := Submodule.finrank_mono hkle
  rw [Submodule.finrank_map_subtype_eq] at hkle'
  have hN := N.finrank_range_add_finrank_ker
  have hl := hlower a ha ha1
  change 2 ≤ finrank (ZMod 2) N.range at hl
  have hdimR : finrank (ZMod 2) N.range = 2 := by omega
  let R := N.range.comap W.subtype
  have hRmap : R.map W.subtype = N.range := by
    rw [Submodule.map_comap_eq,Submodule.range_subtype,inf_eq_right.mpr hNW]
  have hdim : finrank (ZMod 2) R = 2 := by
    rw [←hRmap,Submodule.finrank_map_subtype_eq] at hdimR
    exact hdimR
  apply no_invariant_plane hd v (fun hh => hv (congrArg Subtype.val hh)) R hdim
  intro φ hφ w hw
  obtain ⟨s,hs,hact⟩ := hfull φ
  have hsv : ρ s v = v := (hact v).trans (congrArg Subtype.val hφ)
  have hcomm : a*s = s*a := (normalizer_le_centralizer_of_card_two D hcard
    (hnorm s hs hsv)) a ha
  obtain ⟨u,hu⟩ := (show (w:V) ∈ N.range from hw)
  change (φ w : V) ∈ N.range
  refine ⟨ρ s u,?_⟩
  rw [←hact w,←hu]
  change ρ a (ρ s u) - ρ s u = ρ s (ρ a u-u)
  rw [map_sub,←Module.End.mul_apply,←map_mul,hcomm,map_mul,Module.End.mul_apply]

end Representation.BinaryHyperplaneDisplacement
