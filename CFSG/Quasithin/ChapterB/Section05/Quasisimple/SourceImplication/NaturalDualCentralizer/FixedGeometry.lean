module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.SylowFlags
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pair
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The actual Sylow-fixed centralizer of the natural-plus-dual action

A binary Sylow subgroup is a full flag stabilizer. Its invariant lines and
hyperplanes are cuts of that flag, so its natural fixed vectors form the first
basis line and its fixed covectors form the last dual line. These two lines
are incident. Their pointwise centralizer is exactly the stabilizer of the
marked vector and covector.

The SL-to-linear equivalence intertwines the published `naturalPlusDual`
action without changing the module coordinates. The fixed-space equality and
the centralizer image below retain that exact map. This settles the geometric
identification needed before calculating the core and quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(6),
printed pp.99 and 103; `refs/quasithin.pdf`, PDF pp.110 and 114.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open BinaryNaturalDual BinaryNaturalDual.VectorStabilizers
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer

/-- The published action with its binary carrier made explicit for transport. -/
noncomputable abbrev slAction (d : ℕ) :
    Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin d) (ZMod 2))
      (CoordinateSpace d) := naturalPlusDual d

/-- The matrix and linear-automorphism models act identically in these coordinates. -/
theorem action_apply (d : ℕ) (g : Matrix.SpecialLinearGroup (Fin d) (ZMod 2))
    (v : CoordinateSpace d) :
    slAction d g v = naturalDualRepresentation (slEquivLinear d g) v := by
  rw [naturalDualRepresentation_apply]
  apply Prod.ext
  · change linearNatural BinaryField.two d g v.1 = slEquivLinear d g v.1
    rw [slEquivLinear_apply]
    exact specialLinearNatural_apply d g v.1
  · apply LinearMap.ext
    intro x
    change v.2 (linearNatural BinaryField.two d g⁻¹ x) =
      v.2 ((slEquivLinear d g).symm x)
    rw [← LinearEquiv.coe_inv, ← map_inv, slEquivLinear_apply]
    exact congrArg v.2 (specialLinearNatural_apply d g⁻¹ x)

/-- Equality of the actual representations after changing the actor. -/
theorem action_eq (d : ℕ) : slAction d =
    naturalDualRepresentation.comp (slEquivLinear d).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  exact action_apply d g v

private theorem fixes_line {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {A : Submodule (ZMod 2) V} (hA : Module.finrank (ZMod 2) A = 1)
    {g : BinaryLinear.GL V} (hg : g ∈ parabolic A) {v : V} (hv : v ∈ A) : g v = v := by
  by_cases hv0 : v = 0
  · simp [hv0]
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hA hv hv0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ (hg v).mpr hv)
  have hc0 : c ≠ 0 := by
    intro hz
    exact hv0 (g.map_eq_zero_iff.mp (by simpa [hz] using hc.symm))
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa [hc1] using hc.symm

private theorem preserves_form_iff {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : BinaryLinear.GL V) (f : Module.Dual (ZMod 2) V) :
    (∀ v, f (g v) = f v) ↔ g ∈ parabolic f.ker := by
  constructor
  · intro h v
    change f (g v) = 0 ↔ f v = 0
    rw [h]
  · intro h v
    have he : f (g v) = 0 ↔ f v = 0 := h v
    have binary : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
    exact binary _ _ he

private theorem cut_zero {m : ℕ} (hm : 0 < m) (b : Basis m) :
    cutSpace b ⟨0, hm⟩ = Submodule.span (ZMod 2) {b 0} := by
  unfold cutSpace
  congr 1
  ext v
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj0 : j = 0 := Fin.ext (by change j.val = 0; change j.val ≤ 0 at hj; omega)
    simp [hj0]
  · rintro rfl
    exact ⟨0, by change (0 : ℕ) ≤ 0; rfl, rfl⟩

private theorem cut_last {m : ℕ} (hm : 0 < m) (b : Basis m) :
    cutSpace b ⟨m - 1, by omega⟩ = (b.coord (Fin.last m)).ker := by
  ext v
  rw [cutSpace, Module.Basis.mem_span_image]
  change (↑(b.repr v).support ⊆ {j : Fin (m + 1) | j.val ≤ m - 1}) ↔
    b.repr v (Fin.last m) = 0
  constructor
  · intro h
    by_contra hn
    have := h (Finsupp.mem_support_iff.mpr hn)
    change m ≤ m - 1 at this
    omega
  · intro h j hj
    have hjne : j ≠ Fin.last m := by
      intro he
      subst j
      exact (Finsupp.mem_support_iff.mp hj) h
    have hval : j.val ≠ m := fun he => hjne (Fin.ext he)
    have := j.isLt
    change j.val ≤ m - 1
    omega

private theorem natural_fixed_iff {m : ℕ} (hm : 0 < m) (b : Basis m)
    (v : Space (m + 1)) :
    (∀ g ∈ cutStabilizer b Set.univ, g v = v) ↔
      v ∈ Submodule.span (ZMod 2) {b 0} := by
  constructor
  · intro hv
    by_cases hv0 : v = 0
    · simp [hv0]
    let W := Submodule.span (ZMod 2) {v}
    have hdim : Module.finrank (ZMod 2) W = 1 := finrank_span_singleton hv0
    have hW0 : W ≠ ⊥ := by intro h; rw [h, finrank_bot] at hdim; omega
    have hW1 : W ≠ ⊤ := by
      intro h
      rw [h, finrank_top, Module.finrank_fin_fun] at hdim
      omega
    have hstable : cutStabilizer b Set.univ ≤ parabolic W := by
      intro g hg w
      constructor
      · intro hw
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
        apply Submodule.mem_span_singleton.mpr
        refine ⟨a, g.injective ?_⟩
        rw [map_smul, hv g hg]
        exact ha
      · intro hw
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [map_smul, hv g hg]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
    obtain ⟨i, hi⟩ := fullFlag_invariant_subspace b W hW0 hW1 hstable
    have hdi := cutSpace_finrank b i
    rw [← hi, hdim] at hdi
    have hi0 : i = ⟨0, hm⟩ := Fin.ext (by change i.val = 0; omega)
    rw [hi0, cut_zero hm] at hi
    exact hi ▸ Submodule.subset_span (Set.mem_singleton v)
  · intro hv g hg
    apply fixes_line (finrank_span_singleton (b.ne_zero 0)) _ hv
    rw [← cut_zero hm]
    exact (mem_cutStabilizer b Set.univ g).mp hg ⟨0, hm⟩ (Set.mem_univ _)

private theorem dual_fixed_iff {m : ℕ} (hm : 0 < m) (b : Basis m)
    (f : Module.Dual (ZMod 2) (Space (m + 1))) :
    (∀ g ∈ cutStabilizer b Set.univ, ∀ v, f (g v) = f v) ↔
      f ∈ Submodule.span (ZMod 2) {b.coord (Fin.last m)} := by
  have hq : b.coord (Fin.last m) ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h (b (Fin.last m))
    simp at this
  have hkdim : Module.finrank (ZMod 2) (b.coord (Fin.last m)).ker = m := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hq
    rw [Module.finrank_fin_fun] at h
    omega
  have hann : (b.coord (Fin.last m)).ker.dualAnnihilator =
      Submodule.span (ZMod 2) {b.coord (Fin.last m)} := by
    apply eq_span_singleton_of_mem_of_finrank_eq_one
    · have h := Subspace.finrank_add_finrank_dualAnnihilator_eq
        (b.coord (Fin.last m)).ker
      rw [hkdim, Module.finrank_fin_fun] at h
      omega
    · rw [Submodule.mem_dualAnnihilator]
      exact fun _ hv => hv
    · exact hq
  constructor
  · intro hf
    by_cases hf0 : f = 0
    · simp [hf0]
    have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hf0
    rw [Module.finrank_fin_fun] at hdim
    have hk0 : f.ker ≠ ⊥ := by intro h; rw [h, finrank_bot] at hdim; omega
    have hk1 : f.ker ≠ ⊤ := by intro h; rw [h, finrank_top, Module.finrank_fin_fun] at hdim; omega
    obtain ⟨i, hi⟩ := fullFlag_invariant_subspace b f.ker hk0 hk1
      (fun g hg => (preserves_form_iff g f).mp (hf g hg))
    have hdi := cutSpace_finrank b i
    rw [← hi] at hdi
    have hi1 : i = ⟨m - 1, by omega⟩ := Fin.ext (by change i.val = m - 1; omega)
    rw [hi1, cut_last hm] at hi
    rw [← hann]
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    exact (hi.symm ▸ hv : v ∈ f.ker)
  · intro hf g hg
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hf
    intro v
    have hh := (preserves_form_iff g (b.coord (Fin.last m))).mpr
      (by rw [← cut_last hm]; exact
        (mem_cutStabilizer b Set.univ g).mp hg ⟨m - 1, by omega⟩ (Set.mem_univ _)) v
    change a • b.coord (Fin.last m) (g v) = a • b.coord (Fin.last m) v
    rw [hh]

/-- The full flag fixes the two endpoint lines in the natural-plus-dual module. -/
theorem fixedSpace_fullFlag {m : ℕ} (hm : 0 < m) (b : Basis m) :
    fixedSpace naturalDualRepresentation (cutStabilizer b Set.univ) =
      (Submodule.span (ZMod 2) {b 0}).prod
        (Submodule.span (ZMod 2) {b.coord (Fin.last m)}) := by
  ext v
  change (∀ g : cutStabilizer b Set.univ, naturalDualRepresentation g.val v = v) ↔
    v.1 ∈ Submodule.span (ZMod 2) {b 0} ∧
      v.2 ∈ Submodule.span (ZMod 2) {b.coord (Fin.last m)}
  constructor
  · intro hv
    have hp (g) (hg : g ∈ cutStabilizer b Set.univ) : g ∈ pairStabilizer v.1 v.2 :=
      (mem_pairStabilizer_iff_action _ _ _).mpr (hv ⟨g, hg⟩)
    exact ⟨(natural_fixed_iff hm b v.1).mp (fun g hg => (hp g hg).1),
      (dual_fixed_iff hm b v.2).mp (fun g hg => (hp g hg).2)⟩
  · rintro ⟨hx, hf⟩ g
    exact (mem_pairStabilizer_iff_action _ _ _).mp
      ⟨(natural_fixed_iff hm b v.1).mpr hx g.val g.property,
        (dual_fixed_iff hm b v.2).mpr hf g.val g.property⟩

/-- Pointwise fixation of the two endpoint lines is the literal pair stabilizer. -/
theorem kernel_prod_lines {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (x : V) (f : Module.Dual (ZMod 2) V) :
    subspaceKernel naturalDualRepresentation
      ((Submodule.span (ZMod 2) {x}).prod (Submodule.span (ZMod 2) {f})) ⊤ =
        pairStabilizer x f := by
  ext g
  constructor
  · intro hg
    apply (mem_pairStabilizer_iff_action _ _ _).mpr
    exact hg.2 (x, f)
      ⟨Submodule.subset_span (Set.mem_singleton x),
        Submodule.subset_span (Set.mem_singleton f)⟩
  · intro hg
    refine ⟨mem_top g, ?_⟩
    rintro ⟨v, q⟩ ⟨hv, hq⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
    apply (mem_pairStabilizer_iff_action _ _ _).mp
    refine ⟨?_, ?_⟩
    · rw [map_smul, hg.1]
    · intro w
      change c • f (g w) = c • f w
      rw [hg.2]

/-- Every Sylow fixes exactly the natural and dual lines of an incident pair. -/
theorem exists_linear_fixed_pair {m : ℕ} (hm : 0 < m)
    (T : Sylow 2 (LinearGroup (m + 1))) :
    ∃ (x : Space (m + 1)) (f : Module.Dual (ZMod 2) (Space (m + 1))),
      x ≠ 0 ∧ f ≠ 0 ∧ f x = 0 ∧
      fixedSpace naturalDualRepresentation T =
        (Submodule.span (ZMod 2) {x}).prod (Submodule.span (ZMod 2) {f}) := by
  obtain ⟨b, hb⟩ := sylow_eq_cutStabilizer T
  refine ⟨b 0, b.coord (Fin.last m), b.ne_zero 0, ?_, ?_, ?_⟩
  · intro h
    have := LinearMap.congr_fun h (b (Fin.last m))
    simp at this
  · have hne : (0 : Fin (m + 1)) ≠ Fin.last m := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at this
      omega
    simp [hne]
  · rw [hb]
    exact fixedSpace_fullFlag hm b

/-- The exact SL representation and the linear-automorphism representation
have the same fixed subspace under the specified SL-to-linear map. -/
theorem fixedSpace_map (d : ℕ) (A : Subgroup (Matrix.SpecialLinearGroup (Fin d) (ZMod 2))) :
    fixedSpace (slAction d) A = fixedSpace naturalDualRepresentation
      (A.map (slEquivLinear d).toMonoidHom) := by
  rw [action_eq, fixedSpace_comp_map]

/-- The source Sylow fixed-space calculation, including incidence. -/
theorem exists_fixed_pair {d : ℕ} (hd : 2 ≤ d)
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin d) (ZMod 2))) :
    ∃ (x : Space d) (f : Module.Dual (ZMod 2) (Space d)),
      x ≠ 0 ∧ f ≠ 0 ∧ f x = 0 ∧ fixedSpace (slAction d) T =
        (Submodule.span (ZMod 2) {x}).prod (Submodule.span (ZMod 2) {f}) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  let S := T.mapSurjective (f := (slEquivLinear (m + 1)).toMonoidHom)
    (slEquivLinear (m + 1)).surjective
  obtain ⟨x, f, hx, hf, hfx, hfix⟩ := exists_linear_fixed_pair (by omega : 0 < m) S
  refine ⟨x, f, hx, hf, hfx, ?_⟩
  rw [fixedSpace_map]
  exact hfix

/-- Pointwise kernels transport along the actual, intertwining group equivalence. -/
theorem kernel_map (d : ℕ) (W : Submodule (ZMod 2) (CoordinateSpace d)) :
    (subspaceKernel (slAction d) W ⊤).map (slEquivLinear d).toMonoidHom =
      subspaceKernel naturalDualRepresentation W ⊤ := by
  ext g
  obtain ⟨a, rfl⟩ := (slEquivLinear d).surjective g
  rw [mem_map_equiv, MulEquiv.symm_apply_apply]
  simp only [mem_subspaceKernel, mem_top, true_and, action_apply]

/-- This is the literal centralizer image, not an abstract parabolic model. -/
theorem centralizer_map {d : ℕ}
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)))
    (x : Space d) (f : Module.Dual (ZMod 2) (Space d))
    (hfix : fixedSpace (slAction d) T =
      (Submodule.span (ZMod 2) {x}).prod (Submodule.span (ZMod 2) {f})) :
    (subspaceKernel (slAction d) (fixedSpace (slAction d) T) ⊤).map
      (slEquivLinear d).toMonoidHom = pairStabilizer x f := by
  rw [kernel_map, hfix, kernel_prod_lines]

end CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer
