module
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.FirstCohomologyDuality
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The three-dimensional orthogonal cover of SL₂ in characteristic two

On coordinates `(r,x,y)`, the quadratic form is `r²+xy`. A matrix with rows
`(a,b)` and `(c,d)` acts by
`(r+√(ac)x+√(bd)y, ax+by, cx+dy)`. The determinant identity proves both the
representation law and invariance of the form. Its polar radical is the
fixed first coordinate axis, and projection onto `(x,y)` is a central cover
when the field has more than two elements.

The upper root fixes the plane `y=0`. Its unique singular point is the
`x`-axis; the displacement for parameter `t` is the line `(√t,t,0)`.
Different nonzero parameters give disjoint nonsingular lines, and two such
lines generate the fixed plane. This includes the field of order four.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma I.2.3(1a,b)
and the model calculation for (3), printed p.413/PDF p.424. Identification
with the universal binary cover is supplied in the `Universal` extension.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2OrthogonalCover
open Matrix Matrix.SpecialLinearGroup Representation.OneCohomology
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
abbrev Plane (F : Type*) := Fin 2 → F
abbrev Space (F : Type*) := Fin 3 → F
abbrev SL (F : Type*) [Field F] := SpecialLinearGroup (Fin 2) F
abbrev root : F ≃+* F := (frobeniusEquiv F 2).symm
lemma root_sq (x : F) : root (x ^ 2) = x := frobeniusEquiv_symm_pow F 2 x
lemma sq_root (x : F) : root x ^ 2 = x := frobeniusEquiv_symm_pow_p F 2 x
omit [Finite F] in
lemma det_relation (g : SL F) : g.val 0 0 * g.val 1 1 + g.val 0 1 * g.val 1 0 = 1 := by
  simpa only [det_fin_two, CharTwo.sub_eq_add] using g.property

/-- Linear lift of the natural action preserving r² + xy. -/
def actionMap (g : SL F) : Space F →ₗ[F] Space F where
  toFun v := ![v 0 + root (g.val 0 0 * g.val 1 0) * v 1 +
      root (g.val 0 1 * g.val 1 1) * v 2,
    g.val 0 0 * v 1 + g.val 0 1 * v 2,
    g.val 1 0 * v 1 + g.val 1 1 * v 2]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a v := by ext i; fin_cases i <;> simp <;> ring

lemma root_column (g h : SL F) (i : Fin 2) :
    root ((g * h).val 0 i * (g * h).val 1 i) =
      root (h.val 0 i * h.val 1 i) +
      root (g.val 0 0 * g.val 1 0) * h.val 0 i +
      root (g.val 0 1 * g.val 1 1) * h.val 1 i := by
  apply CharTwo.sq_injective
  simp only [CharTwo.add_sq, mul_pow, sq_root, coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  calc
    _ = (g.val 0 0 * g.val 1 0) * h.val 0 i ^ 2 +
      (g.val 0 1 * g.val 1 1) * h.val 1 i ^ 2 +
      (g.val 0 0 * g.val 1 1 + g.val 0 1 * g.val 1 0) *
        (h.val 0 i * h.val 1 i) := by ring
    _ = _ := by rw [det_relation]; ring

def action : Representation F (SL F) (Space F) where
  toFun := actionMap
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    fin_cases i <;> simp [actionMap]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext i
    fin_cases i
    · change v 0 + root ((g * h).val 0 0 * (g * h).val 1 0) * v 1 +
          root ((g * h).val 0 1 * (g * h).val 1 1) * v 2 = _
      rw [root_column, root_column]
      simp [actionMap]
      ring
    · simp [actionMap, Matrix.mul_apply, Fin.sum_univ_two]; ring
    · simp [actionMap, Matrix.mul_apply, Fin.sum_univ_two]; ring

lemma action_apply (g : SL F) (v : Space F) :
    action g v = ![v 0 + root (g.val 0 0 * g.val 1 0) * v 1 +
      root (g.val 0 1 * g.val 1 1) * v 2,
    g.val 0 0 * v 1 + g.val 0 1 * v 2,
    g.val 1 0 * v 1 + g.val 1 1 * v 2] := rfl

def form : QuadraticForm F (Space F) :=
  QuadraticMap.proj 0 0 + QuadraticMap.proj 1 2
omit [Finite F] [CharP F 2] in
lemma form_apply (v : Space F) : form v = v 0 ^ 2 + v 1 * v 2 := by
  simp [form, QuadraticMap.proj, QuadraticMap.linMulLin_apply, pow_two]
lemma form_invariant (g : SL F) (v : Space F) : form (action g v) = form v := by
  rw [form_apply, form_apply]
  change (v 0 + root (g.val 0 0 * g.val 1 0) * v 1 +
      root (g.val 0 1 * g.val 1 1) * v 2) ^ 2 +
    (g.val 0 0 * v 1 + g.val 0 1 * v 2) *
    (g.val 1 0 * v 1 + g.val 1 1 * v 2) = _
  simp only [CharTwo.add_sq, mul_pow, sq_root]
  have hd := det_relation g
  calc
    _ = v 0 ^ 2 +
      (g.val 0 0 * g.val 1 0 * v 1 ^ 2 + g.val 0 0 * g.val 1 0 * v 1 ^ 2) +
      (g.val 0 1 * g.val 1 1 * v 2 ^ 2 + g.val 0 1 * g.val 1 1 * v 2 ^ 2) +
      (g.val 0 0 * g.val 1 1 + g.val 0 1 * g.val 1 0) * (v 1 * v 2) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, hd]; ring

def natural : Representation F (SL F) (Plane F) := specialLinearNatural 2

def projectionMap : Space F →ₗ[F] Plane F where
  toFun v := ![v 1, v 2]
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' a v := by ext i; fin_cases i <;> simp

def projection : action.IntertwiningMap (natural (F := F)) :=
  projectionMap.intertwiningMap_of_isIntertwiningMap action natural (by
    intro g v
    change ![(action g v) 1, (action g v) 2] = natural g ![v 1, v 2]
    ext i
    fin_cases i <;> simp [action_apply, natural, specialLinearNatural_apply,
      mulVec, dotProduct, Fin.sum_univ_two])
lemma projection_apply (v : Space F) : projection v = ![v 1, v 2] := rfl
lemma projection_surjective : Function.Surjective (projection (F := F)) := by
  intro v
  refine ⟨![0, v 0, v 1], ?_⟩
  ext i; fin_cases i <;> rfl

omit [Finite F] in
lemma polar_apply (v w : Space F) : form.polarBilin v w = v 1 * w 2 + v 2 * w 1 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, form_apply,
    Pi.add_apply, CharTwo.add_sq]
  ring
omit [Finite F] in
lemma mem_polar_ker (v : Space F) : v ∈ (form (F := F)).polarBilin.ker ↔ v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · intro h
    have h1 := LinearMap.congr_fun h ![0, 0, 1]
    have h2 := LinearMap.congr_fun h ![0, 1, 0]
    change form.polarBilin v ![0,0,1] = 0 at h1
    change form.polarBilin v ![0,1,0] = 0 at h2
    rw [polar_apply] at h1 h2
    exact ⟨by simpa using h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    apply LinearMap.ext
    intro w
    change form.polarBilin v w = 0
    rw [polar_apply, h1, h2]
    simp
lemma projection_kernel : (projection (F := F)).toLinearMap.ker = form.polarBilin.ker := by
  ext v
  rw [mem_polar_ker]
  change (![v 1, v 2] : Plane F) = 0 ↔ _
  simp [funext_iff, Fin.forall_fin_two]
omit [Finite F] in
lemma polar_ker_eq_span : (form (F := F)).polarBilin.ker = Submodule.span F {![1,0,0]} := by
  ext v
  rw [mem_polar_ker, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨v 0, ?_⟩
    ext i; fin_cases i <;> simp [h1, h2]
  · rintro ⟨c, rfl⟩; simp
omit [Finite F] in
lemma radical_dimension : Module.finrank F (form (F := F)).polarBilin.ker = 1 := by
  rw [polar_ker_eq_span]
  exact finrank_span_singleton (by simp)
omit [Finite F] in
lemma form_nondegenerate : (form (F := F)).Nondegenerate := by
  constructor
  · apply bot_unique
    intro v hv
    have hp := (mem_polar_ker v).mp hv.2
    have h0 : v 0 = 0 := by
      have hq := hv.1
      rw [form_apply, hp.1, hp.2, zero_mul, add_zero] at hq
      exact (pow_eq_zero_iff (by decide)).mp hq
    change v = 0
    ext i; fin_cases i <;> simp [h0, hp.1, hp.2]
  · rw [← Module.finrank_eq_rank, radical_dimension]
    exact le_rfl

abbrev upper (t : F) : SL F := transvection zero_ne_one t
abbrev lower (t : F) : SL F := transvection one_ne_zero t
lemma action_upper (t : F) (v : Space F) :
    action (upper t) v = ![v 0 + root t * v 2, v 1 + t * v 2, v 2] := by
  ext i; fin_cases i <;> simp [action_apply, upper, transvection_coe]
lemma action_lower (t : F) (v : Space F) :
    action (lower t) v = ![v 0 + root t * v 1, v 1, t * v 1 + v 2] := by
  ext i; fin_cases i <;> simp [action_apply, lower, transvection_coe]
lemma upper_displacement (t : F) (v : Space F) :
    action (upper t) v - v = ![root t * v 2, t * v 2, 0] := by
  rw [action_upper]
  ext i; fin_cases i <;> simp
lemma fixed_radical : fixed (action (F := F)) = form.polarBilin.ker := by
  ext v
  rw [mem_polar_ker]
  constructor
  · intro h
    have hu := congrFun (h (upper 1)) 1
    have hl := congrFun (h (lower 1)) 2
    exact ⟨by simpa [action_lower] using hl, by simpa [action_upper] using hu⟩
  · rintro ⟨h1, h2⟩ g
    ext i; fin_cases i <;> simp [action_apply, h1, h2]

/-- Literal preimage of the first coordinate line in the natural quotient. -/
def fixedPlane : Submodule F (Space F) := (LinearMap.proj 2).ker
omit [Finite F] [CharP F 2] in
lemma mem_fixedPlane (v : Space F) : v ∈ fixedPlane ↔ v 2 = 0 := Iff.rfl
lemma upper_fixed_iff (t : F) (ht : t ≠ 0) (v : Space F) :
    action (upper t) v = v ↔ v ∈ fixedPlane := by
  rw [← sub_eq_zero, upper_displacement]
  constructor
  · intro h
    exact (mul_eq_zero.mp (congrFun h 1)).resolve_left ht
  · intro h
    change v 2 = 0 at h
    simp [h]
lemma root_fixed : fixed (action.comp (upperUnipotent F).subtype) = fixedPlane := by
  apply le_antisymm
  · intro v hv
    exact (upper_fixed_iff 1 one_ne_zero v).mp (hv ⟨upper 1, (mem_upperUnipotent F _).mpr ⟨1,rfl⟩⟩)
  · intro v hv g
    obtain ⟨t, ht⟩ := (mem_upperUnipotent F g.val).mp g.property
    change action g.val v = v
    rw [← ht]
    ext i; fin_cases i <;> simp [action_upper, (mem_fixedPlane v).mp hv]

omit [CharP F 2] in
lemma exists_parameter (hF : 2 < Nat.card F) : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
  classical
  let := Fintype.ofFinite F
  have h : ({0, 1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [Nat.card_eq_fintype_card] using hF
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  exact ⟨a, by simpa using ha⟩

lemma fixedPlane_displacements (hF : 2 < Nat.card F) (v : Space F) (hv : v ∈ fixedPlane) :
    ∃ (t : F) (u w : Space F), v = (action (upper 1) u - u) + (action (upper t) w - w) := by
  obtain ⟨a, ha, ha1⟩ := exists_parameter hF
  have hd : a ^ 2 - a ≠ 0 := by
    rw [show a ^ 2 - a = a * (a - 1) by ring]
    exact mul_ne_zero ha (sub_ne_zero.mpr ha1)
  let z := (v 1 - v 0) / (a ^ 2 - a)
  let y := v 0 - a * z
  refine ⟨a ^ 2, ![0,0,y], ![0,0,z], ?_⟩
  rw [upper_displacement, upper_displacement, root_sq]
  ext i
  fin_cases i
  · simp [y]
  · dsimp
    simp only [one_mul]
    change v 1 = y + a ^ 2 * z
    dsimp only [y, z]
    field_simp [hd]
    ring
  · simpa using (mem_fixedPlane v).mp hv

lemma root_commutator (hF : 2 < Nat.card F) :
    Coinvariants.ker (action.comp (upperUnipotent F).subtype) = fixedPlane := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩, rfl⟩
    obtain ⟨t, ht⟩ := (mem_upperUnipotent F g.val).mp g.property
    change (action g.val v - v) 2 = 0
    rw [← ht]
    rw [upper_displacement]
    rfl
  · intro v hv
    obtain ⟨t,u,w,he⟩ := fixedPlane_displacements hF v hv
    rw [he]
    exact Submodule.add_mem _
      (Coinvariants.sub_mem_ker (ρ := action.comp (upperUnipotent F).subtype) ⟨upper 1, (mem_upperUnipotent F _).mpr ⟨1,rfl⟩⟩ u)
      (Coinvariants.sub_mem_ker (ρ := action.comp (upperUnipotent F).subtype) ⟨upper t, (mem_upperUnipotent F _).mpr ⟨t,rfl⟩⟩ w)

lemma action_full (hF : 2 < Nat.card F) : Coinvariants.ker (action (F := F)) = ⊤ := by
  have hplane : fixedPlane ≤ Coinvariants.ker (action (F := F)) := by
    intro v hv
    obtain ⟨t,u,w,he⟩ := fixedPlane_displacements hF v hv
    rw [he]
    exact Submodule.add_mem _ (Coinvariants.sub_mem_ker _ _) (Coinvariants.sub_mem_ker _ _)
  have hl : (![1,0,1] : Space F) ∈ Coinvariants.ker (action (F := F)) := by
    have h := Coinvariants.sub_mem_ker (ρ := action (F := F)) (lower 1) ![0,1,0]
    simpa [action_lower] using h
  apply top_unique
  intro v _
  have he : v = ![v 0 - v 2, v 1, 0] + v 2 • ![1,0,1] := by
    ext i; fin_cases i <;> simp
  rw [he]
  exact Submodule.add_mem _ (hplane (by rfl)) (Submodule.smul_mem _ _ hl)

lemma projection_isCover (hF : 2 < Nat.card F) : IsCover (projection (F := F)) := by
  refine ⟨projection_surjective, ?_, action_full hF⟩
  rw [projection_kernel, fixed_radical]


/-- The unique singular point in the root-fixed plane. -/
def singularPoint : Submodule F (Space F) := Submodule.span F {![0,1,0]}
omit [Finite F] [CharP F 2] in
lemma singularPoint_dimension : Module.finrank F (singularPoint (F := F)) = 1 :=
  finrank_span_singleton (by simp)
omit [Finite F] [CharP F 2] in
lemma mem_singularPoint (v : Space F) : v ∈ singularPoint ↔ v 0 = 0 ∧ v 2 = 0 := by
  rw [singularPoint, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩; simp
  · rintro ⟨h0,h2⟩
    refine ⟨v 1, ?_⟩
    ext i; fin_cases i <;> simp [h0,h2]
omit [Finite F] [CharP F 2] in
lemma singular_in_fixedPlane (v : Space F) (hv : v ∈ fixedPlane) :
    form v = 0 ↔ v ∈ singularPoint := by
  rw [form_apply, (mem_fixedPlane v).mp hv, mul_zero, add_zero,
    mem_singularPoint, and_iff_left ((mem_fixedPlane v).mp hv)]
  exact pow_eq_zero_iff (by decide)
omit [Finite F] [CharP F 2] in
lemma singularPoint_unique (P : Submodule F (Space F))
    (hP : Module.finrank F P = 1) (hplane : P ≤ fixedPlane)
    (hsingular : ∀ v ∈ P, form v = 0) : P = singularPoint := by
  apply Submodule.eq_of_le_of_finrank_eq
    (fun v hv => (singular_in_fixedPlane v (hplane hv)).mp (hsingular v hv))
  rw [hP, singularPoint_dimension]
omit [Finite F] in
lemma fixedPlane_decomposition : fixedPlane (F := F) = singularPoint ⊔ form.polarBilin.ker := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_sup]
    refine ⟨![0,v 1,0], (mem_singularPoint _).mpr ⟨rfl,rfl⟩,
      ![v 0,0,0], (mem_polar_ker _).mpr ⟨rfl,rfl⟩, ?_⟩
    ext i; fin_cases i <;> simp [(mem_fixedPlane v).mp hv]
  · apply sup_le
    · intro v hv; exact ((mem_singularPoint v).mp hv).2
    · intro v hv; exact ((mem_polar_ker v).mp hv).2
omit [Finite F] in
lemma singularPoint_disjoint_radical :
    Disjoint (singularPoint (F := F)) form.polarBilin.ker := by
  rw [Submodule.disjoint_def]
  intro v hP hR
  have hP' := (mem_singularPoint v).mp hP
  have hR' := (mem_polar_ker v).mp hR
  ext i; fin_cases i <;> simp [hP'.1, hP'.2, hR'.1]

/-- The F-linear image of the displacement by an individual root element. -/
def rootDisplacement (t : F) : Submodule F (Space F) :=
  LinearMap.range (action (upper t) - LinearMap.id)
lemma rootDisplacement_eq_span (t : F) :
    rootDisplacement t = Submodule.span F {![root t,t,0]} := by
  ext v
  rw [rootDisplacement, LinearMap.mem_range, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨w 2, ?_⟩
    change _ = action (upper t) w - w
    rw [upper_displacement]
    ext i; fin_cases i <;> simp [mul_comm]
  · rintro ⟨c, rfl⟩
    refine ⟨![0,0,c], ?_⟩
    change action (upper t) ![0,0,c] - ![0,0,c] = _
    rw [upper_displacement]
    ext i; fin_cases i <;> simp [mul_comm]
lemma rootDisplacement_dimension (t : F) (ht : t ≠ 0) :
    Module.finrank F (rootDisplacement t) = 1 := by
  rw [rootDisplacement_eq_span]
  apply finrank_span_singleton
  intro h
  exact ht (congrFun h 1)
lemma rootDisplacement_le_plane (t : F) : rootDisplacement t ≤ fixedPlane := by
  rintro v ⟨w, rfl⟩
  change (action (upper t) w - w) 2 = 0
  rw [upper_displacement]
  rfl
lemma rootDisplacement_nonsingular (t : F) (ht : t ≠ 0)
    (v : Space F) (hv : v ∈ rootDisplacement t) (hne : v ≠ 0) : form v ≠ 0 := by
  obtain ⟨w,rfl⟩ := hv
  change form (action (upper t) w - w) ≠ 0
  change action (upper t) w - w ≠ 0 at hne
  rw [upper_displacement] at hne ⊢
  have hw : w 2 ≠ 0 := by intro h; apply hne; simp [h]
  simpa [form_apply, mul_pow, sq_root] using mul_ne_zero ht (pow_ne_zero 2 hw)
lemma rootDisplacement_ne_radical (t : F) (ht : t ≠ 0) :
    rootDisplacement t ≠ (form (F := F)).polarBilin.ker := by
  intro he
  have hm : (![root t,t,0] : Space F) ∈ rootDisplacement t := by
    rw [rootDisplacement_eq_span]
    exact Submodule.subset_span (by simp)
  rw [he] at hm
  exact ht ((mem_polar_ker _).mp hm).1
lemma rootDisplacement_disjoint (s t : F) (hs : s ≠ 0) (_ht : t ≠ 0) (hst : s ≠ t) :
    Disjoint (rootDisplacement s) (rootDisplacement t) := by
  rw [Submodule.disjoint_def]
  intro v hvS hvT
  by_contra hv0
  obtain ⟨u,hu⟩ := hvS
  obtain ⟨w,hw⟩ := hvT
  change action (upper s) u - u = v at hu
  change action (upper t) w - w = v at hw
  rw [upper_displacement] at hu hw
  have hy : u 2 ≠ 0 := by
    intro hy
    apply hv0
    rw [← hu]
    simp [hy]
  have hr : root s ≠ 0 := (map_ne_zero root).mpr hs
  have h0 : v 0 ≠ 0 := by
    rw [← hu]
    exact mul_ne_zero hr hy
  have hS : s * v 0 ^ 2 = v 1 ^ 2 := by
    rw [← hu]
    change s * (root s * u 2) ^ 2 = (s * u 2) ^ 2
    rw [mul_pow, sq_root, mul_pow]
    ring
  have hT : t * v 0 ^ 2 = v 1 ^ 2 := by
    rw [← hw]
    change t * (root t * w 2) ^ 2 = (t * w 2) ^ 2
    rw [mul_pow, sq_root, mul_pow]
    ring
  exact hst (mul_right_cancel₀ (pow_ne_zero 2 h0) (hS.trans hT.symm))


end Representation.SL2OrthogonalCover
