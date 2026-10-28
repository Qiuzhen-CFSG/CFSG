module

public import Theory.LinearAlgebra.QuadraticForm.Reflection
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Wall residual forms for quadratic isometries

For a finite-dimensional nondegenerate quadratic space, the image of `g - 1`
for an isometry `g` carries Wall's residual form.  We construct it using a
linear section of the range map and expose its representative formula,
nonsingularity, and the anisotropic-vector criterion used by the
Cartan--Dieudonné Wall-core reduction.  We then prove its corrected diagonal
identity and the reflection-composition rank update.

The normalization is deliberately source-faithful to Mathlib: its
`QuadraticMap.associated` form is one half of the polar form.  Consequently
the diagonal contract is

`2 * wallForm Q g u u = -Q u`,

not `wallForm Q g u u = -Q u`.  This explicit factor is the compatibility
theorem used by the Wall-core reduction.  The construction follows Wall's
classical residual-form proof of Cartan--Dieudonné.  In the nonalternating
branch an anisotropic moved line can be selected so that its right-orthogonal
complement is either zero or remains nonalternating, hence every nontrivial
one-reflection rank drop stays in that branch.  If an initial anisotropic line
has alternating complement, the selection proof replaces its generator by an
explicit linear combination with vectors in that complement.  In the
alternating branch the moved space is totally isotropic and even-dimensional;
one exceptional reflection raises its rank by one and makes its Wall form
nonalternating.  The isotropic dimension bound absorbs this two-reflection
detour in the ambient Cartan--Dieudonné bound.
-/

open Module
open QuadraticMap

namespace QuadraticForm

variable {k V : Type*} [Field k] [Invertible (2 : k)]
variable [AddCommGroup V] [Module k V]

/-- The moved-space map `g - 1`. -/
public noncomputable def wallMovedMap (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) :=
  g.toLinearEquiv.toLinearMap - LinearMap.id

/-- The moved space of an isometry, as the range of `g - 1`. -/
public noncomputable def wallMovedSpace (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) :=
  LinearMap.range (wallMovedMap Q g)

omit [Invertible (2 : k)] in
private lemma wallMoved_mem (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (x : V) :
    wallMovedMap Q g x ∈ wallMovedSpace Q g := by
  change wallMovedMap Q g x ∈ LinearMap.range (wallMovedMap Q g)
  exact LinearMap.mem_range_self (wallMovedMap Q g) x

/- The proof that a moved vector lies in the range is implementation detail;
   this public constructor keeps it out of downstream theorem statements. -/
@[expose] public noncomputable def wallMovedPoint (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (x : V) : wallMovedSpace Q g :=
  ⟨wallMovedMap Q g x, by
    change wallMovedMap Q g x ∈ LinearMap.range (wallMovedMap Q g)
    exact LinearMap.mem_range_self (wallMovedMap Q g) x⟩

omit [Invertible (2 : k)] in
@[simp] public lemma wallMovedPoint_coe (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (x : V) :
    (wallMovedPoint Q g x : V) = wallMovedMap Q g x :=
  rfl

private noncomputable def wallSection (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) : wallMovedSpace Q g →ₗ[k] V :=
  Classical.choose ((wallMovedMap Q g).rangeRestrict.exists_rightInverse_of_surjective
    (wallMovedMap Q g).range_rangeRestrict)

omit [Invertible (2 : k)] in
private lemma wallSection_spec (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) :
    (wallMovedMap Q g).rangeRestrict ∘ₗ wallSection Q g = LinearMap.id :=
  Classical.choose_spec ((wallMovedMap Q g).rangeRestrict.exists_rightInverse_of_surjective
    (wallMovedMap Q g).range_rangeRestrict)

omit [Invertible (2 : k)] in
private lemma wallSection_apply_spec (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (u : wallMovedSpace Q g) :
    wallMovedMap Q g (wallSection Q g u) = u := by
  have h := LinearMap.congr_fun (wallSection_spec Q g) u
  exact congrArg Subtype.val h

/-- The Wall residual form on the moved space. -/
public noncomputable def wallForm (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) : LinearMap.BilinMap k (wallMovedSpace Q g) k :=
  Q.associated.compl₁₂ (wallMovedSpace Q g).subtype (wallSection Q g)

@[simp] private lemma wallForm_apply (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (u v : wallMovedSpace Q g) :
    wallForm Q g u v = Q.associated u (wallSection Q g v) :=
  rfl

private lemma associated_isometry (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (x y : V) :
    Q.associated (g.toLinearEquiv x) (g.toLinearEquiv y) = Q.associated x y := by
  have hcomp : Q.comp g.toLinearEquiv.toLinearMap = Q := by
    ext z
    exact g.map_app z
  calc
    Q.associated (g.toLinearEquiv x) (g.toLinearEquiv y) =
        (Q.associated.compl₁₂ g.toLinearEquiv.toLinearMap
          g.toLinearEquiv.toLinearMap) x y := rfl
    _ = (Q.comp g.toLinearEquiv.toLinearMap).associated x y := by
      rw [QuadraticMap.associated_comp]
    _ = Q.associated x y := by rw [hcomp]

private lemma associated_isometry_left (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (x y : V) :
    Q.associated (g.toLinearEquiv x) y = Q.associated x (g.toLinearEquiv.symm y) := by
  rw [← associated_isometry Q g x (g.toLinearEquiv.symm y)]
  simp

private lemma associated_isometry_right (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (x y : V) :
    Q.associated x (g.toLinearEquiv y) = Q.associated (g.toLinearEquiv.symm x) y := by
  rw [QuadraticMap.associated_isSymm k Q, associated_isometry_left Q g y x,
    QuadraticMap.associated_isSymm k Q]

private lemma moved_fixed_orthogonal (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) {x z : V}
    (hz : wallMovedMap Q g z = 0) :
    Q.associated (wallMovedMap Q g x) z = 0 := by
  change Q.associated (g.toLinearEquiv x - x) z = 0
  rw [map_sub, LinearMap.sub_apply, associated_isometry_left Q g x z]
  have hz' : g.toLinearEquiv z = z := by
    exact sub_eq_zero.mp hz
  have hz'' : g.toLinearEquiv.symm z = z := by
    have h := congrArg g.toLinearEquiv.symm hz'
    simpa using h.symm
  rw [hz'']
  simp

private lemma moved_fixed_orthogonal' (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) {x z : V}
    (hz : wallMovedMap Q g z = 0) :
    Q.associated z (wallMovedMap Q g x) = 0 := by
  rw [QuadraticMap.associated_isSymm k Q]
  exact moved_fixed_orthogonal Q g hz

/-- The representative formula for the Wall form.

This is the compatibility interface for consumers that represent moved-space
vectors as `(g - 1) x`: the chosen linear section disappears because the
complementary fixed vector is orthogonal to the moved space.
-/
public lemma wallForm_representative (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (x y : V) :
    wallForm Q g (wallMovedPoint Q g x) (wallMovedPoint Q g y) =
      Q.associated (wallMovedMap Q g x) y := by
  let u : wallMovedSpace Q g := wallMovedPoint Q g x
  let v : wallMovedSpace Q g := wallMovedPoint Q g y
  have hs := wallSection_apply_spec Q g v
  have hfixed : wallMovedMap Q g (y - wallSection Q g v) = 0 := by
    rw [map_sub, hs]
    change (wallMovedMap Q g y) - (v : V) = 0
    simp [v]
  calc
    wallForm Q g u v = Q.associated (wallMovedMap Q g x) (wallSection Q g v) := rfl
    _ = 0 + Q.associated (wallMovedMap Q g x) (wallSection Q g v) := by simp
    _ = Q.associated (wallMovedMap Q g x) (y - wallSection Q g v) +
        Q.associated (wallMovedMap Q g x) (wallSection Q g v) := by
      rw [moved_fixed_orthogonal Q g hfixed]
    _ = Q.associated (wallMovedMap Q g x)
        (y - wallSection Q g v + wallSection Q g v) := by rw [map_add]
    _ = Q.associated (wallMovedMap Q g x) y := by rw [sub_add_cancel]

/- The range-section argument also proves nonsingularity once the ambient
   quadratic form is nondegenerate.  This is used by the residual reduction. -/
public lemma wallForm_nondegenerate (Q : QuadraticForm k V)
    [FiniteDimensional k V] (hQ : Q.Nondegenerate)
    (g : Q.IsometryEquiv Q) :
    (wallForm Q g).Nondegenerate := by
  let B := wallForm Q g
  constructor
  · intro u hu
    apply Subtype.ext
    have hu' : ∀ y : V, Q.associated (u : V) y = 0 := by
      intro y
      have h := hu ⟨wallMovedMap Q g y, wallMoved_mem Q g y⟩
      rw [wallForm_apply] at h
      let v : wallMovedSpace Q g :=
        ⟨wallMovedMap Q g y, wallMoved_mem Q g y⟩
      have hfixed : wallMovedMap Q g (y - wallSection Q g v) = 0 := by
        rw [map_sub, wallSection_apply_spec Q g v]
        change wallMovedMap Q g y - (v : V) = 0
        simp [v]
      have horth := moved_fixed_orthogonal Q g hfixed
        (x := wallSection Q g u) (z := y - wallSection Q g v)
      rw [wallSection_apply_spec Q g u] at horth
      calc
        Q.associated (u : V) y =
            Q.associated (u : V) (y - wallSection Q g v + wallSection Q g v) := by
          rw [sub_add_cancel]
        _ = Q.associated (u : V) (y - wallSection Q g v) +
            Q.associated (u : V) (wallSection Q g v) := by
          rw [map_add]
        _ = 0 := by rw [horth, h, zero_add]
    have hu'' : (u : V) ∈ LinearMap.ker Q.associated := by
      rw [LinearMap.mem_ker]
      ext y
      exact hu' y
    have hker : LinearMap.ker Q.associated = ⊥ := by
      rw [← QuadraticMap.radical_eq_ker_associated, hQ.radical_eq_bot]
    rw [hker] at hu''
    simpa using hu''
  · intro v hv
    apply Subtype.ext
    have hfixed : wallMovedMap Q g (wallSection Q g v) = (v : V) :=
      wallSection_apply_spec Q g v
    have hdiff : g.toLinearEquiv.symm (wallSection Q g v) - wallSection Q g v ∈
        LinearMap.ker Q.associated := by
      rw [LinearMap.mem_ker]
      ext x
      have h := hv ⟨wallMovedMap Q g x, wallMoved_mem Q g x⟩
      rw [wallForm_apply] at h
      change Q.associated (g.toLinearEquiv x - x) (wallSection Q g v) = 0 at h
      calc
        Q.associated (g.toLinearEquiv.symm (wallSection Q g v) - wallSection Q g v) x =
            Q.associated x (g.toLinearEquiv.symm (wallSection Q g v) - wallSection Q g v) :=
          QuadraticMap.associated_isSymm k Q _ _
        _ = Q.associated (g.toLinearEquiv x) (wallSection Q g v) -
            Q.associated x (wallSection Q g v) := by
          rw [LinearMap.map_sub (Q.associated x), ← associated_isometry_left Q g x]
        _ = Q.associated (g.toLinearEquiv x - x) (wallSection Q g v) := by
          exact congrArg (fun f => f (wallSection Q g v))
            (LinearMap.map_sub Q.associated (g.toLinearEquiv x) x).symm
        _ = 0 := h
    have hker : LinearMap.ker Q.associated = ⊥ := by
      rw [← QuadraticMap.radical_eq_ker_associated, hQ.radical_eq_bot]
    have hdiff0 : g.toLinearEquiv.symm (wallSection Q g v) - wallSection Q g v = 0 := by
      rw [hker] at hdiff
      simpa using hdiff
    have hsymm : g.toLinearEquiv.symm (wallSection Q g v) = wallSection Q g v :=
      sub_eq_zero.mp hdiff0
    have hself : g.toLinearEquiv (wallSection Q g v) = wallSection Q g v := by
      have h := congrArg g.toLinearEquiv hsymm
      simpa using h.symm
    have hzero : wallMovedMap Q g (wallSection Q g v) = 0 := by
      exact sub_eq_zero.mpr hself
    rw [hfixed] at hzero
    exact hzero

/- For a nondegenerate nonalternating bilinear form, choose an anisotropic
   line whose right-orthogonal complement is nonalternating unless it is zero.
   The two branches below handle whether the old alternating complement has a
   nonzero cross-functional with the chosen line. -/
private theorem exists_anisotropic_right_complement_not_isAlt
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (B : LinearMap.BilinForm k W) (hB : B.Nondegenerate)
    (hnotAlt : ¬ B.IsAlt) :
    ∃ u : W, B u u ≠ 0 ∧
      (0 < finrank k (LinearMap.ker (B.flip u)) →
        ¬(B.domRestrict₁₂ (LinearMap.ker (B.flip u))
          (LinearMap.ker (B.flip u))).IsAlt) := by
  change ¬(∀ u : W, B u u = 0) at hnotAlt
  push Not at hnotAlt
  obtain ⟨u, hu⟩ := hnotAlt
  let H := LinearMap.ker (B.flip u)
  let BH := B.domRestrict₁₂ H H
  have hBH : BH.Nondegenerate :=
    LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft (by
      intro x hx
      apply Subtype.ext
      apply hB.1 (x : W)
      intro y
      let c := B y u * (B u u)⁻¹
      have hz : B (y - c • u) u = 0 := by
        simp only [map_sub, map_smul, LinearMap.sub_apply,
          LinearMap.smul_apply, smul_eq_mul]
        simp [c, hu]
      let z : H := ⟨y - c • u, by simpa [H] using hz⟩
      have hxu : B (x : W) u = 0 := by
        have hxmem := x.property
        change B (x : W) u = 0 at hxmem
        exact hxmem
      calc
        B (x : W) y = B (x : W) ((z : W) + c • u) := by simp [z]
        _ = B (x : W) (z : W) + c * B (x : W) u := by
          simp only [map_add, map_smul, smul_eq_mul]
        _ = 0 := by rw [show B (x : W) (z : W) = 0 from hx z, hxu]; simp)
  by_cases hAlt : BH.IsAlt
  · by_cases hHzero : finrank k H = 0
    · refine ⟨u, hu, ?_⟩
      intro hHpos
      exact ((Nat.ne_of_gt hHpos) hHzero).elim
    have hHpos : 0 < finrank k H := Nat.pos_of_ne_zero hHzero
    let _ : Nontrivial H := Module.nontrivial_of_finrank_pos hHpos
    let ell : H →ₗ[k] k := (B u).domRestrict H
    by_cases hell : ell = 0
    · obtain ⟨x, hx⟩ := exists_ne (0 : H)
      have hex : ∃ t₀ : H, BH t₀ x ≠ 0 := by
        by_contra h
        push Not at h
        exact hx (hBH.2 x h)
      obtain ⟨t₀, ht₀⟩ := hex
      let t : H := (B u u * (BH t₀ x)⁻¹) • t₀
      have htx : BH t x = B u u := by
        simp [t, ht₀]
      have hux : B u (x : W) = 0 := by
        have := LinearMap.congr_fun hell x
        simpa [ell] using this
      have hut : B u (t : W) = 0 := by
        have := LinearMap.congr_fun hell t
        simpa [ell] using this
      have hxu : B (x : W) u = 0 := by
        have hxmem := x.property
        change B (x : W) u = 0 at hxmem
        exact hxmem
      have htu : B (t : W) u = 0 := by
        have htmem := t.property
        change B (t : W) u = 0 at htmem
        exact htmem
      have hxx : B (x : W) (x : W) = 0 := by
        exact hAlt x
      have htt : B (t : W) (t : W) = 0 := by
        exact hAlt t
      have htx' : B (t : W) (x : W) = B u u := htx
      let u' : W := u + (x : W)
      let y : W := u - (t : W)
      have hu' : B u' u' = B u u := by
        simp [u', hux, hxu, hxx]
      have hyu' : B y u' = 0 := by
        simp [y, u', hux, htu, htx']
      have hyy : B y y = B u u := by
        simp [y, hut, htu, htt]
      refine ⟨u', hu' ▸ hu, ?_⟩
      intro _ hAlt'
      let y' : LinearMap.ker (B.flip u') := ⟨y, by simpa using hyu'⟩
      have hyzero := hAlt' y'
      change B y y = 0 at hyzero
      exact hu (hyy ▸ hyzero)
    · have hex : ∃ x₀ : H, ell x₀ ≠ 0 := by
        by_contra h
        push Not at h
        apply hell
        ext x
        exact h x
      obtain ⟨x₀, hx₀⟩ := hex
      let x : H := (B u u * (ell x₀)⁻¹) • x₀
      have hxell : ell x = B u u := by
        simp [x, hx₀]
      let t : H := (LinearMap.BilinForm.toDual BH hBH).symm ell
      have htell (z : H) : BH t z = ell z := by
        exact LinearMap.BilinForm.apply_toDual_symm_apply
          (B := BH) (hB := hBH) ell z
      have hellt : ell t = 0 := by
        rw [← htell t]
        exact hAlt t
      have hux : B u (x : W) = B u u := hxell
      have hut : B u (t : W) = 0 := hellt
      have hxu : B (x : W) u = 0 := by
        have hxmem := x.property
        change B (x : W) u = 0 at hxmem
        exact hxmem
      have htu : B (t : W) u = 0 := by
        have htmem := t.property
        change B (t : W) u = 0 at htmem
        exact htmem
      have hxx : B (x : W) (x : W) = 0 := hAlt x
      have htt : B (t : W) (t : W) = 0 := hAlt t
      have htx : B (t : W) (x : W) = B u u := by
        rw [show B (t : W) (x : W) = BH t x from rfl, htell, hxell]
      let u' : W := u + (x : W)
      let y : W := u - (2 : k) • (t : W)
      have hu' : B u' u' = 2 * B u u := by
        simp [u', hux, hxu, hxx]
        ring
      have hu'ne : B u' u' ≠ 0 := by
        rw [hu']
        exact mul_ne_zero (Invertible.ne_zero (2 : k)) hu
      have hyu' : B y u' = 0 := by
        simp [y, u', hux, htu, htx]
        ring
      have hyy : B y y = B u u := by
        simp [y, hut, htu, htt]
      refine ⟨u', hu'ne, ?_⟩
      intro _ hAlt'
      let y' : LinearMap.ker (B.flip u') := ⟨y, by simpa using hyu'⟩
      have hyzero := hAlt' y'
      change B y y = 0 at hyzero
      exact hu (hyy ▸ hyzero)
  · exact ⟨u, hu, fun _ ↦ hAlt⟩

/-- Mathlib's associated form is half the polar form, so the Wall diagonal
identity has an explicit factor of two. -/
public lemma two_mul_wallForm_apply_self (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (u : wallMovedSpace Q g) :
    2 * wallForm Q g u u = -Q (u : V) := by
  obtain ⟨x, hx⟩ := u.property
  let u' : wallMovedSpace Q g := wallMovedPoint Q g x
  have hu : u = u' := Subtype.ext hx.symm
  rw [hu]
  change 2 * wallForm Q g (wallMovedPoint Q g x) (wallMovedPoint Q g x) =
    -Q (wallMovedMap Q g x)
  rw [wallForm_representative]
  let t := wallMovedMap Q g x
  change 2 * Q.associated t x = -Q t
  change 2 * Q.associated (g.toLinearEquiv x - x) x =
    -Q (g.toLinearEquiv x - x)
  rw [map_sub, LinearMap.sub_apply]
  have hq := QuadraticMap.map_add Q (g.toLinearEquiv x) (-x)
  rw [Q.map_neg, QuadraticMap.polar_neg_right] at hq
  have hpolar := congrArg (fun B => B (g.toLinearEquiv x) x)
    (QuadraticMap.two_nsmul_associated k Q)
  have hpolar' : QuadraticMap.polar Q (g.toLinearEquiv x) x =
      2 * Q.associated (g.toLinearEquiv x) x := by
    simpa only [QuadraticMap.polarBilin_apply_apply, LinearMap.smul_apply,
      nsmul_eq_mul, Nat.cast_ofNat] using hpolar.symm
  rw [← sub_eq_add_neg] at hq
  have hg : Q (g.toLinearEquiv x) = Q x := g.map_app x
  rw [hg, hpolar'] at hq
  change 2 * (Q.associated (g.toLinearEquiv x) x - Q.associated x x) =
    -Q (g.toLinearEquiv x - x)
  rw [mul_sub]
  rw [QuadraticMap.associated_eq_self_apply k Q x]
  rw [hq]
  ring

private lemma quadratic_ne_zero_of_wallForm_self_ne_zero
    (Q : QuadraticForm k V) (g : Q.IsometryEquiv Q)
    (u : wallMovedSpace Q g) (hu : wallForm Q g u u ≠ 0) :
    Q (u : V) ≠ 0 := by
  intro hQu
  apply hu
  have hdiag := two_mul_wallForm_apply_self Q g u
  rw [hQu, neg_zero] at hdiag
  exact (mul_eq_zero.mp hdiag).resolve_left (Invertible.ne_zero (2 : k))

private lemma associated_moved_isometry_eq_neg_wallForm
    (Q : QuadraticForm k V) (g : Q.IsometryEquiv Q) (x a : V) :
    Q.associated (wallMovedMap Q g a) (g x) =
      -wallForm Q g (wallMovedPoint Q g x) (wallMovedPoint Q g a) := by
  calc
    Q.associated (wallMovedMap Q g a) (g x) =
        Q.associated (g a - a) (g x) := rfl
    _ = Q.associated (g a) (g x) - Q.associated a (g x) := by
      rw [map_sub, LinearMap.sub_apply]
    _ = Q.associated a x - Q.associated a (g x) := by
      rw [show Q.associated (g a) (g x) = Q.associated a x from
        associated_isometry Q g a x]
    _ = -Q.associated a (g x - x) := by rw [map_sub]; ring
    _ = -Q.associated (g x - x) a := by
      rw [QuadraticMap.associated_isSymm k Q]
    _ = -Q.associated (wallMovedMap Q g x) a := rfl
    _ = -wallForm Q g (wallMovedPoint Q g x) (wallMovedPoint Q g a) := by
      rw [wallForm_representative]

/-- A nonalternating Wall form yields an anisotropic moved vector. -/
public lemma exists_anisotropic_moved_of_not_isAlt
    (Q : QuadraticForm k V) (g : Q.IsometryEquiv Q)
    (hχ : ¬ (wallForm Q g).IsAlt) :
    ∃ u : wallMovedSpace Q g, Q (u : V) ≠ 0 := by
  change ¬ (∀ u : wallMovedSpace Q g, wallForm Q g u u = 0) at hχ
  push Not at hχ
  obtain ⟨u, hu⟩ := hχ
  refine ⟨u, ?_⟩
  intro hQ
  have h := two_mul_wallForm_apply_self Q g u
  rw [hQ, neg_zero] at h
  exact hu ((mul_eq_zero.mp h).resolve_left (Invertible.ne_zero (2 : k)))

private noncomputable def wallReflectionIsometry (Q : QuadraticForm k V)
    (v : V) (hv : Q v ≠ 0) : Q.IsometryEquiv Q where
  toLinearEquiv := anisotropicReflection Q v hv
  map_app' := anisotropicReflection_preserves Q v hv

private noncomputable def wallReflectAfter (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (v : V) (hv : Q v ≠ 0) : Q.IsometryEquiv Q :=
  g.trans (wallReflectionIsometry Q v hv)

@[simp] private lemma wallReflectAfter_apply (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (v : V) (hv : Q v ≠ 0) (x : V) :
    wallReflectAfter Q g v hv x = anisotropicReflection Q v hv (g x) :=
  rfl

private lemma wallMovedMap_wallReflectAfter_apply (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (v : V) (hv : Q v ≠ 0) (x : V) :
    wallMovedMap Q (wallReflectAfter Q g v hv) x =
      wallMovedMap Q g x -
        (2 * (Q v)⁻¹ * Q.associated v (g x)) • v := by
  change anisotropicReflection Q v hv (g x) - x =
    (g x - x) - (2 * (Q v)⁻¹ * Q.associated v (g x)) • v
  rw [anisotropicReflection_apply]
  abel

private lemma wallReflectAfter_fixed_of_fixed (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (v : V) (hv : Q v ≠ 0) {x : V}
    (hx : wallMovedMap Q g x = 0) (hvx : Q.associated v x = 0) :
    wallMovedMap Q (wallReflectAfter Q g v hv) x = 0 := by
  have hgx : g x = x := sub_eq_zero.mp hx
  rw [wallMovedMap_wallReflectAfter_apply, hx, hgx, hvx]
  simp

private lemma wallReflectAfter_fixed_preimage (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (u : wallMovedSpace Q g)
    (hu : Q (u : V) ≠ 0) {a : V}
    (ha : wallMovedMap Q g a = (u : V)) :
    wallMovedMap Q (wallReflectAfter Q g (u : V) hu) a = 0 := by
  have hu' : u = wallMovedPoint Q g a := by
    apply Subtype.ext
    exact ha.symm
  have hwall : wallForm Q g u u = Q.associated (u : V) a := by
    rw [hu', wallForm_representative]
    simp [ha]
  have hdiag := two_mul_wallForm_apply_self Q g u
  rw [hwall] at hdiag
  have hga : g a = a + (u : V) := by
    change g a - a = (u : V) at ha
    rw [sub_eq_iff_eq_add] at ha
    simpa [add_comm] using ha
  have hcoef : 2 * (Q (u : V))⁻¹ * Q.associated (u : V) (g a) = 1 := by
    rw [hga, map_add, QuadraticMap.associated_eq_self_apply]
    calc
      2 * (Q (u : V))⁻¹ *
          (Q.associated (u : V) a + Q (u : V)) =
          (Q (u : V))⁻¹ *
            (2 * Q.associated (u : V) a + 2 * Q (u : V)) := by ring
      _ = (Q (u : V))⁻¹ * Q (u : V) := by rw [hdiag]; ring
      _ = 1 := inv_mul_cancel₀ hu
  rw [wallMovedMap_wallReflectAfter_apply, ha, hcoef]
  simp

private lemma wallReflectAfter_regular_ker (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (u : wallMovedSpace Q g)
    (hu : Q (u : V) ≠ 0) {a : V}
    (ha : wallMovedMap Q g a = (u : V)) :
    LinearMap.ker (wallMovedMap Q (wallReflectAfter Q g (u : V) hu)) =
      LinearMap.ker (wallMovedMap Q g) ⊔ k ∙ a := by
  apply le_antisymm
  · intro x hx
    have hx0 := LinearMap.mem_ker.mp hx
    rw [wallMovedMap_wallReflectAfter_apply] at hx0
    let c := 2 * (Q (u : V))⁻¹ * Q.associated (u : V) (g x)
    have hAx : wallMovedMap Q g x = c • (u : V) := sub_eq_zero.mp hx0
    have hz : wallMovedMap Q g (x - c • a) = 0 := by
      rw [map_sub, map_smul, hAx, ha]
      simp
    have hzmem : x - c • a ∈ LinearMap.ker (wallMovedMap Q g) :=
      LinearMap.mem_ker.mpr hz
    have hca : c • a ∈ k ∙ a :=
      Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
    have hadd := add_mem
      (Submodule.mem_sup_left hzmem) (Submodule.mem_sup_right hca)
    simpa only [sub_add_cancel] using hadd
  · apply sup_le
    · intro x hx
      have hx0 := LinearMap.mem_ker.mp hx
      have hux : Q.associated (u : V) x = 0 := by
        rw [← ha]
        exact moved_fixed_orthogonal Q g hx0
      exact LinearMap.mem_ker.mpr
        (wallReflectAfter_fixed_of_fixed Q g (u : V) hu hx0 hux)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact LinearMap.mem_ker.mpr
        (wallReflectAfter_fixed_preimage Q g u hu ha)

/-- Left-composition by the reflection in an anisotropic moved vector lowers
the moved-space dimension by one.  The returned pointwise formula lets a
consumer reconstruct `g` by applying the same involutive reflection again. -/
public theorem exists_wallRankDrop_of_anisotropic_moved [FiniteDimensional k V]
    (Q : QuadraticForm k V) (g : Q.IsometryEquiv Q)
    (u : wallMovedSpace Q g) (hu : Q (u : V) ≠ 0) :
    ∃ h : Q.IsometryEquiv Q,
      (∀ x, h x = anisotropicReflection Q (u : V) hu (g x)) ∧
      finrank k (wallMovedSpace Q h) + 1 =
        finrank k (wallMovedSpace Q g) := by
  obtain ⟨a, ha⟩ := u.property
  let h := wallReflectAfter Q g (u : V) hu
  refine ⟨h, fun _ ↦ rfl, ?_⟩
  have hu0 : (u : V) ≠ 0 := by
    intro hu'
    apply hu
    rw [hu']
    exact Q.map_zero
  have ha_not : a ∉ LinearMap.ker (wallMovedMap Q g) := by
    intro hamem
    have ha0 := LinearMap.mem_ker.mp hamem
    rw [ha] at ha0
    exact hu0 ha0
  have hker := wallReflectAfter_regular_ker Q g u hu ha
  have hkerfin :
      finrank k (LinearMap.ker (wallMovedMap Q h)) =
        finrank k (LinearMap.ker (wallMovedMap Q g)) + 1 := by
    rw [hker, Submodule.finrank_sup_span_singleton ha_not]
  have hrankh := LinearMap.finrank_range_add_finrank_ker (wallMovedMap Q h)
  have hrankg := LinearMap.finrank_range_add_finrank_ker (wallMovedMap Q g)
  change finrank k (wallMovedSpace Q h) +
      finrank k (LinearMap.ker (wallMovedMap Q h)) = finrank k V at hrankh
  change finrank k (wallMovedSpace Q g) +
      finrank k (LinearMap.ker (wallMovedMap Q g)) = finrank k V at hrankg
  lia

private lemma right_orthogonal_mem_reflected_moved
    (Q : QuadraticForm k V) (g : Q.IsometryEquiv Q)
    (u v : wallMovedSpace Q g) (hu : Q (u : V) ≠ 0)
    (hvu : wallForm Q g v u = 0) (h : Q.IsometryEquiv Q)
    (hh : ∀ x, h x = anisotropicReflection Q (u : V) hu (g x)) :
    (v : V) ∈ wallMovedSpace Q h := by
  obtain ⟨a, ha⟩ := u.property
  obtain ⟨x, hx⟩ := v.property
  have huPoint : u = wallMovedPoint Q g a := by
    apply Subtype.ext
    exact ha.symm
  have hvPoint : v = wallMovedPoint Q g x := by
    apply Subtype.ext
    exact hx.symm
  have hassociated : Q.associated (u : V) (g x) = 0 := by
    calc
      Q.associated (u : V) (g x) =
          Q.associated (wallMovedMap Q g a) (g x) := by rw [ha]
      _ = -wallForm Q g (wallMovedPoint Q g x) (wallMovedPoint Q g a) :=
        associated_moved_isometry_eq_neg_wallForm Q g x a
      _ = -wallForm Q g v u := by rw [hvPoint, huPoint]
      _ = 0 := by rw [hvu, neg_zero]
  change (v : V) ∈ LinearMap.range (wallMovedMap Q h)
  refine ⟨x, ?_⟩
  change h x - x = (v : V)
  rw [hh, anisotropicReflection_apply, hassociated]
  change g x - x = (v : V) at hx
  simpa using hx

/-- A nonalternating Wall form admits a one-reflection rank drop which remains
nonalternating unless the new moved space is zero.  The vector is selected so
that the new moved space, identified with its old Wall-right-orthogonal
complement, contains an anisotropic vector whenever it has positive rank. -/
public theorem exists_wallRankDrop_preserving_not_isAlt
    [FiniteDimensional k V] (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (g : Q.IsometryEquiv Q) (hnotAlt : ¬(wallForm Q g).IsAlt) :
    ∃ u : wallMovedSpace Q g, ∃ hu : Q (u : V) ≠ 0,
      ∃ h : Q.IsometryEquiv Q,
        (∀ x, h x = anisotropicReflection Q (u : V) hu (g x)) ∧
        finrank k (wallMovedSpace Q h) + 1 =
          finrank k (wallMovedSpace Q g) ∧
        (0 < finrank k (wallMovedSpace Q h) →
          ¬(wallForm Q h).IsAlt) := by
  obtain ⟨u, huWall, huPreserves⟩ :=
    exists_anisotropic_right_complement_not_isAlt
      (wallForm Q g) (wallForm_nondegenerate Q hQ g) hnotAlt
  have hu : Q (u : V) ≠ 0 :=
    quadratic_ne_zero_of_wallForm_self_ne_zero Q g u huWall
  obtain ⟨h, hh, hrank⟩ :=
    exists_wallRankDrop_of_anisotropic_moved Q g u hu
  refine ⟨u, hu, h, hh, hrank, ?_⟩
  intro hnewPos hnewAlt
  have hfunctional : (wallForm Q g).flip u ≠ 0 := by
    intro hzero
    have hz := LinearMap.congr_fun hzero u
    exact huWall (by simpa using hz)
  have hcomplementRank :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hfunctional
  have hcomplementPos :
      0 < finrank k (LinearMap.ker ((wallForm Q g).flip u)) := by
    lia
  have hcomplementNotAlt := huPreserves hcomplementPos
  change ¬(∀ v : LinearMap.ker ((wallForm Q g).flip u),
    wallForm Q g (v : wallMovedSpace Q g) v = 0) at hcomplementNotAlt
  push Not at hcomplementNotAlt
  obtain ⟨v, hvSelf⟩ := hcomplementNotAlt
  have hvu : wallForm Q g (v : wallMovedSpace Q g) u = 0 := by
    have hvmem := v.property
    change wallForm Q g (v : wallMovedSpace Q g) u = 0 at hvmem
    exact hvmem
  have hvQ : Q (v : V) ≠ 0 :=
    quadratic_ne_zero_of_wallForm_self_ne_zero Q g v hvSelf
  let v' : wallMovedSpace Q h :=
    ⟨(v : V), right_orthogonal_mem_reflected_moved Q g u v hu hvu h hh⟩
  have hdiag := two_mul_wallForm_apply_self Q h v'
  rw [hnewAlt v', mul_zero] at hdiag
  exact hvQ (by simpa [v'] using hdiag.symm)

/-- If the Wall form is alternating, every moved vector is isotropic for `Q`. -/
public theorem wallMoved_isotropic_of_isAlt (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (hχ : (wallForm Q g).IsAlt)
    (u : wallMovedSpace Q g) : Q (u : V) = 0 := by
  have hdiag := two_mul_wallForm_apply_self Q g u
  rw [hχ u, mul_zero] at hdiag
  simpa using hdiag.symm

private theorem even_finrank_of_isAlt_nondegenerate
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (B : LinearMap.BilinForm k W) (hAlt : B.IsAlt)
    (hB : B.Nondegenerate) : Even (finrank k W) := by
  let b := Module.finBasis k W
  let A := LinearMap.BilinForm.toMatrix b B
  have hA : A.transpose = -A := by
    ext i j
    dsimp only [A]
    rw [Matrix.transpose_apply, Matrix.neg_apply,
      LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.toMatrix_apply]
    exact (LinearMap.IsAlt.neg hAlt (b i) (b j)).symm
  have hdet_ne : A.det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
  have hdet : A.det = (-1 : k) ^ finrank k W * A.det := by
    calc
      A.det = A.transpose.det := (Matrix.det_transpose A).symm
      _ = (-A).det := by rw [hA]
      _ = (-1 : k) ^ Fintype.card (Fin (finrank k W)) * A.det :=
        Matrix.det_neg A
      _ = (-1 : k) ^ finrank k W * A.det := by simp
  have hpow : (-1 : k) ^ finrank k W = 1 := by
    apply mul_right_cancel₀ hdet_ne
    simpa using hdet.symm
  apply (neg_one_pow_eq_one_iff_even ?_).mp hpow
  intro hneg
  apply two_ne_zero (α := k)
  linear_combination -hneg

/-- A nondegenerate alternating Wall form has even moved-space dimension. -/
public theorem even_finrank_wallMovedSpace_of_isAlt [FiniteDimensional k V]
    (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (g : Q.IsometryEquiv Q) (hχ : (wallForm Q g).IsAlt) :
    Even (finrank k (wallMovedSpace Q g)) :=
  even_finrank_of_isAlt_nondegenerate (wallForm Q g) hχ
    (wallForm_nondegenerate Q hQ g)

/-- In the alternating branch, twice the moved-space dimension is at most the
ambient dimension. -/
public theorem twice_finrank_wallMovedSpace_le_of_isAlt [FiniteDimensional k V]
    (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (g : Q.IsometryEquiv Q) (hχ : (wallForm Q g).IsAlt) :
    2 * finrank k (wallMovedSpace Q g) ≤ finrank k V := by
  let W := wallMovedSpace Q g
  let B := Q.polarBilin
  have hB : B.Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hle : W ≤ LinearMap.BilinForm.orthogonal B W := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    let x' : W := ⟨x, hx⟩
    let y' : W := ⟨y, hy⟩
    have hx0 : Q x = 0 := wallMoved_isotropic_of_isAlt Q g hχ x'
    have hy0 : Q y = 0 := wallMoved_isotropic_of_isAlt Q g hχ y'
    have hxy0 : Q (y + x) = 0 := by
      have h := wallMoved_isotropic_of_isAlt Q g hχ (y' + x')
      simpa [x', y'] using h
    have hadd := QuadraticMap.map_add Q y x
    rw [hxy0, hy0, hx0] at hadd
    simpa [B] using hadd.symm
  have hmono : finrank k W ≤
      finrank k (LinearMap.BilinForm.orthogonal B W) :=
    Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hB] at hmono
  have hWle : finrank k W ≤ finrank k V := Submodule.finrank_le W
  change 2 * finrank k W ≤ finrank k V
  omega

private theorem wallMovedSpace_eq_orthogonal_fixed [FiniteDimensional k V]
    (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (g : Q.IsometryEquiv Q) :
    wallMovedSpace Q g = LinearMap.BilinForm.orthogonal Q.associated
      (LinearMap.ker (wallMovedMap Q g)) := by
  let W := wallMovedSpace Q g
  let K := LinearMap.ker (wallMovedMap Q g)
  have hle : W ≤ LinearMap.BilinForm.orthogonal Q.associated K := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro z hz
    rw [QuadraticMap.associated_isSymm k Q]
    obtain ⟨x, hx⟩ := hu
    rw [← hx]
    exact moved_fixed_orthogonal Q g (LinearMap.mem_ker.mp hz)
  apply Submodule.eq_of_le_of_finrank_le hle
  have hB : Q.associated.Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff.mpr hQ
  rw [LinearMap.BilinForm.finrank_orthogonal hB]
  have hrank := LinearMap.finrank_range_add_finrank_ker (wallMovedMap Q g)
  change finrank k W + finrank k K = finrank k V at hrank
  lia

private lemma wallReflectAfter_exceptional_ker_iff (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (v : V) (hv : Q v ≠ 0)
    (hvW : v ∉ wallMovedSpace Q g) (x : V) :
    x ∈ LinearMap.ker (wallMovedMap Q (wallReflectAfter Q g v hv)) ↔
      x ∈ LinearMap.ker (wallMovedMap Q g) ∧ Q.associated v x = 0 := by
  constructor
  · intro hx
    have hx0 := LinearMap.mem_ker.mp hx
    rw [wallMovedMap_wallReflectAfter_apply] at hx0
    let c := 2 * (Q v)⁻¹ * Q.associated v (g x)
    have hAx : wallMovedMap Q g x = c • v := sub_eq_zero.mp hx0
    have hAxW : wallMovedMap Q g x ∈ wallMovedSpace Q g :=
      LinearMap.mem_range_self (wallMovedMap Q g) x
    have hAxv : wallMovedMap Q g x ∈ k ∙ v := by
      rw [hAx]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    have hAxinf : wallMovedMap Q g x ∈
        wallMovedSpace Q g ⊓ k ∙ v := ⟨hAxW, hAxv⟩
    have hAxbot := (Submodule.disjoint_span_singleton_of_notMem hvW).le_bot hAxinf
    have hAx0 : wallMovedMap Q g x = 0 := by simpa using hAxbot
    have hgx : g x = x := sub_eq_zero.mp hAx0
    have hcv : c • v = 0 := by
      rw [hAx0] at hAx
      exact hAx.symm
    have hv0 : v ≠ 0 := by
      intro hv'
      apply hv
      rw [hv']
      exact Q.map_zero
    have hc : c = 0 := (smul_eq_zero.mp hcv).resolve_right hv0
    have hfactor : 2 * (Q v)⁻¹ ≠ 0 :=
      mul_ne_zero (Invertible.ne_zero (2 : k)) (inv_ne_zero hv)
    have hvx : Q.associated v x = 0 := by
      change (2 * (Q v)⁻¹) * Q.associated v (g x) = 0 at hc
      rw [hgx] at hc
      exact (mul_eq_zero.mp hc).resolve_left hfactor
    exact ⟨LinearMap.mem_ker.mpr hAx0, hvx⟩
  · rintro ⟨hx, hvx⟩
    have hx0 := LinearMap.mem_ker.mp hx
    exact LinearMap.mem_ker.mpr
      (wallReflectAfter_fixed_of_fixed Q g v hv hx0 hvx)

private lemma exists_fixed_not_orthogonal_of_not_mem_moved
    [FiniteDimensional k V] (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (g : Q.IsometryEquiv Q) {v : V} (hvW : v ∉ wallMovedSpace Q g) :
    ∃ a : V, a ∈ LinearMap.ker (wallMovedMap Q g) ∧
      Q.associated v a ≠ 0 := by
  have hvorth : v ∉ LinearMap.BilinForm.orthogonal Q.associated
      (LinearMap.ker (wallMovedMap Q g)) := by
    rwa [← wallMovedSpace_eq_orthogonal_fixed Q hQ g]
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hvorth
  have hex : ∃ a : V, a ∈ LinearMap.ker (wallMovedMap Q g) ∧
      Q.associated a v ≠ 0 := by
    by_contra hno
    apply hvorth
    intro a ha
    by_contra hav
    exact hno ⟨a, ha, hav⟩
  obtain ⟨a, ha, hav⟩ := hex
  refine ⟨a, ha, ?_⟩
  rw [QuadraticMap.associated_isSymm k Q]
  exact hav

private lemma wallReflectAfter_exceptional_ker (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q) (v : V) (hv : Q v ≠ 0)
    (hvW : v ∉ wallMovedSpace Q g) {a : V}
    (ha : a ∈ LinearMap.ker (wallMovedMap Q g))
    (hva : Q.associated v a ≠ 0) :
    LinearMap.ker (wallMovedMap Q g) =
      LinearMap.ker (wallMovedMap Q (wallReflectAfter Q g v hv)) ⊔ k ∙ a := by
  apply le_antisymm
  · intro x hx
    let c := Q.associated v x * (Q.associated v a)⁻¹
    have hzfixed : x - c • a ∈ LinearMap.ker (wallMovedMap Q g) := by
      rw [LinearMap.mem_ker, map_sub, map_smul,
        LinearMap.mem_ker.mp hx, LinearMap.mem_ker.mp ha]
      simp
    have hzorth : Q.associated v (x - c • a) = 0 := by
      rw [map_sub]
      change Q.associated v x - (Q.associated v) (c • a) = 0
      rw [map_smul]
      change Q.associated v x - c * Q.associated v a = 0
      rw [show c * Q.associated v a = Q.associated v x by
        simp [c, hva]]
      exact sub_self _
    have hz : x - c • a ∈
        LinearMap.ker (wallMovedMap Q (wallReflectAfter Q g v hv)) :=
      (wallReflectAfter_exceptional_ker_iff Q g v hv hvW _).mpr
        ⟨hzfixed, hzorth⟩
    have hca : c • a ∈ k ∙ a :=
      Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
    have hadd := add_mem
      (Submodule.mem_sup_left hz) (Submodule.mem_sup_right hca)
    simpa only [sub_add_cancel] using hadd
  · apply sup_le
    · intro x hx
      exact (wallReflectAfter_exceptional_ker_iff Q g v hv hvW x).mp hx |>.1
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ha

private theorem exists_wallRankIncrease_of_not_mem_moved
    [FiniteDimensional k V] (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (g : Q.IsometryEquiv Q) (v : V) (hv : Q v ≠ 0)
    (hvW : v ∉ wallMovedSpace Q g) :
    ∃ h : Q.IsometryEquiv Q,
      (∀ x, h x = anisotropicReflection Q v hv (g x)) ∧
      finrank k (wallMovedSpace Q h) =
        finrank k (wallMovedSpace Q g) + 1 := by
  obtain ⟨a, ha, hva⟩ :=
    exists_fixed_not_orthogonal_of_not_mem_moved Q hQ g hvW
  let h := wallReflectAfter Q g v hv
  refine ⟨h, fun _ ↦ rfl, ?_⟩
  have ha_not : a ∉ LinearMap.ker (wallMovedMap Q h) := by
    intro hah
    exact hva ((wallReflectAfter_exceptional_ker_iff Q g v hv hvW a).mp hah).2
  have hker := wallReflectAfter_exceptional_ker Q g v hv hvW ha hva
  have hkerfin : finrank k (LinearMap.ker (wallMovedMap Q g)) =
      finrank k (LinearMap.ker (wallMovedMap Q h)) + 1 := by
    rw [hker, Submodule.finrank_sup_span_singleton ha_not]
  have hrankh := LinearMap.finrank_range_add_finrank_ker (wallMovedMap Q h)
  have hrankg := LinearMap.finrank_range_add_finrank_ker (wallMovedMap Q g)
  change finrank k (wallMovedSpace Q h) +
      finrank k (LinearMap.ker (wallMovedMap Q h)) = finrank k V at hrankh
  change finrank k (wallMovedSpace Q g) +
      finrank k (LinearMap.ker (wallMovedMap Q g)) = finrank k V at hrankg
  lia

private lemma exists_anisotropic_moved_wallReflectAfter_of_fixed_not_orthogonal
    (Q : QuadraticForm k V) (g : Q.IsometryEquiv Q)
    (v : V) (hv : Q v ≠ 0) {a : V}
    (ha : wallMovedMap Q g a = 0) (hva : Q.associated v a ≠ 0) :
    ∃ u : wallMovedSpace Q (wallReflectAfter Q g v hv), Q (u : V) ≠ 0 := by
  let h := wallReflectAfter Q g v hv
  let u := wallMovedPoint Q h a
  let c := 2 * (Q v)⁻¹ * Q.associated v a
  have hg : g a = a := sub_eq_zero.mp ha
  have hu : (u : V) = -(c • v) := by
    change wallMovedMap Q h a = -(c • v)
    rw [wallMovedMap_wallReflectAfter_apply, ha, hg]
    simp [c]
  have hc : c ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (Invertible.ne_zero (2 : k)) (inv_ne_zero hv)) hva
  refine ⟨u, ?_⟩
  rw [hu, Q.map_neg, Q.map_smul]
  exact mul_ne_zero (mul_ne_zero hc hc) hv

private lemma exists_anisotropic_of_nondegenerate [Nontrivial V]
    (Q : QuadraticForm k V) (hQ : Q.Nondegenerate) :
    ∃ v : V, Q v ≠ 0 := by
  apply QuadraticMap.exists_quadraticMap_ne_zero
  change Q.associated ≠ 0
  exact LinearMap.BilinForm.Nondegenerate.ne_zero
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ)

private theorem exists_wallExceptionalAdjustment [FiniteDimensional k V]
    (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (g : Q.IsometryEquiv Q) (hχ : (wallForm Q g).IsAlt)
    (hrank_pos : 0 < finrank k (wallMovedSpace Q g)) :
    Even (finrank k (wallMovedSpace Q g)) ∧
      finrank k (wallMovedSpace Q g) + 2 ≤ finrank k V ∧
      ∃ v : V, ∃ hv : Q v ≠ 0, ∃ h : Q.IsometryEquiv Q,
        (∀ x, h x = anisotropicReflection Q v hv (g x)) ∧
        finrank k (wallMovedSpace Q h) =
          finrank k (wallMovedSpace Q g) + 1 ∧
        ¬(wallForm Q h).IsAlt := by
  have heven := even_finrank_wallMovedSpace_of_isAlt Q hQ g hχ
  have htwice := twice_finrank_wallMovedSpace_le_of_isAlt Q hQ g hχ
  have hbound : finrank k (wallMovedSpace Q g) + 2 ≤ finrank k V := by
    obtain ⟨m, hm⟩ := heven
    omega
  refine ⟨heven, hbound, ?_⟩
  have hVpos : 0 < finrank k V :=
    hrank_pos.trans_le (Submodule.finrank_le (wallMovedSpace Q g))
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hVpos
  obtain ⟨v, hv⟩ := exists_anisotropic_of_nondegenerate Q hQ
  have hvW : v ∉ wallMovedSpace Q g := by
    intro hvW
    let u : wallMovedSpace Q g := ⟨v, hvW⟩
    exact hv (wallMoved_isotropic_of_isAlt Q g hχ u)
  let h := wallReflectAfter Q g v hv
  have hrank : finrank k (wallMovedSpace Q h) =
      finrank k (wallMovedSpace Q g) + 1 := by
    obtain ⟨h', hh', hrank'⟩ :=
      exists_wallRankIncrease_of_not_mem_moved Q hQ g v hv hvW
    have hh : h' = h := by
      apply DFunLike.ext _ _
      intro x
      exact hh' x
    rw [← hh]
    exact hrank'
  have hnotAlt : ¬(wallForm Q h).IsAlt := by
    obtain ⟨a, ha, hva⟩ :=
      exists_fixed_not_orthogonal_of_not_mem_moved Q hQ g hvW
    obtain ⟨u, hu⟩ :=
      exists_anisotropic_moved_wallReflectAfter_of_fixed_not_orthogonal
        Q g v hv (LinearMap.mem_ker.mp ha) hva
    intro hAlt
    exact hu (wallMoved_isotropic_of_isAlt Q h hAlt u)
  exact ⟨v, hv, h, fun _ ↦ rfl, hrank, hnotAlt⟩

omit [Invertible (2 : k)] in
public theorem eq_refl_of_finrank_wallMovedSpace_eq_zero
    [FiniteDimensional k V] (Q : QuadraticForm k V)
    (g : Q.IsometryEquiv Q)
    (hrank : finrank k (wallMovedSpace Q g) = 0) :
    g = QuadraticMap.IsometryEquiv.refl Q := by
  have hbot : wallMovedSpace Q g = ⊥ :=
    Submodule.finrank_eq_zero.mp hrank
  apply DFunLike.ext _ _
  intro x
  have hx : wallMovedMap Q g x = 0 := by
    have hxmem : wallMovedMap Q g x ∈ wallMovedSpace Q g :=
      LinearMap.mem_range_self (wallMovedMap Q g) x
    rw [hbot] at hxmem
    simpa using hxmem
  exact sub_eq_zero.mp hx

omit [Invertible (2 : k)] in
/-- The identity isometry has zero-dimensional moved space. -/
public theorem finrank_wallMovedSpace_refl_eq_zero [FiniteDimensional k V]
    (Q : QuadraticForm k V) :
    finrank k (wallMovedSpace Q (QuadraticMap.IsometryEquiv.refl Q)) = 0 := by
  have hmap : wallMovedMap Q (QuadraticMap.IsometryEquiv.refl Q) = 0 := by
    ext x
    change x - x = 0
    simp
  have hspace : wallMovedSpace Q (QuadraticMap.IsometryEquiv.refl Q) = ⊥ := by
    rw [wallMovedSpace, hmap]
    exact LinearMap.range_zero
  rw [hspace]
  simp

/-- Wall's residual-form reduction: an isometry is the identity, admits a
one-reflection rank drop, or lies in the alternating exceptional branch.  In
the exceptional branch one preliminary reflection makes the residual form
nonalternating, raises residual rank by one, and the original residual rank
has the parity and ambient bound needed to absorb the two-reflection detour. -/
public theorem wallResidualReduction [FiniteDimensional k V]
    (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (g : Q.IsometryEquiv Q) :
    g = QuadraticMap.IsometryEquiv.refl Q ∨
      (∃ u : wallMovedSpace Q g, ∃ hu : Q (u : V) ≠ 0,
        ∃ h : Q.IsometryEquiv Q,
          (∀ x, h x = anisotropicReflection Q (u : V) hu (g x)) ∧
          finrank k (wallMovedSpace Q h) + 1 =
            finrank k (wallMovedSpace Q g)) ∨
      ((wallForm Q g).IsAlt ∧
        Even (finrank k (wallMovedSpace Q g)) ∧
        finrank k (wallMovedSpace Q g) + 2 ≤ finrank k V ∧
        ∃ v : V, ∃ hv : Q v ≠ 0, ∃ h : Q.IsometryEquiv Q,
          (∀ x, h x = anisotropicReflection Q v hv (g x)) ∧
          finrank k (wallMovedSpace Q h) =
            finrank k (wallMovedSpace Q g) + 1 ∧
          ¬(wallForm Q h).IsAlt) := by
  by_cases hzero : finrank k (wallMovedSpace Q g) = 0
  · exact Or.inl (eq_refl_of_finrank_wallMovedSpace_eq_zero Q g hzero)
  by_cases hχ : (wallForm Q g).IsAlt
  · right
    right
    have hpos : 0 < finrank k (wallMovedSpace Q g) := Nat.pos_of_ne_zero hzero
    obtain ⟨heven, hbound, hexceptional⟩ :=
      exists_wallExceptionalAdjustment Q hQ g hχ hpos
    exact ⟨hχ, heven, hbound, hexceptional⟩
  · right
    left
    obtain ⟨u, hu⟩ := exists_anisotropic_moved_of_not_isAlt Q g hχ
    obtain ⟨h, hh, hrank⟩ :=
      exists_wallRankDrop_of_anisotropic_moved Q g u hu
    exact ⟨u, hu, h, hh, hrank⟩

end QuadraticForm
