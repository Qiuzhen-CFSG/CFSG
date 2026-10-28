module

public import Theory.Representation.OrthogonalFourMinusRankOne.RootActors
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# The fixed-field lines in an orthogonal root group

In the Hermitian model for Ω₄⁻(2ˢ), the root parameter field is a quadratic
extension of its fixed field. Its one-dimensional fixed-field subspaces are
exactly the normalizer conjugates of R_t. They partition the nonidentity root
elements. Diagonal conjugation scales parameters by squares, and squaring is
surjective in this finite field of characteristic two.

Source: Aschbacher–Smith, K.3.1.2, printed p.454. This argument also covers s=1.
-/

@[expose] public noncomputable section
namespace Representation.OrthogonalFourMinus.RankOne
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.BinaryOffender Matrix.SpecialLinearGroup
variable (s : ℕ) [NeZero s]

/-- Scalar multiplication of the additive fixed field in the root parameter field. -/
def rootLineHom (u : Field s) : Multiplicative (fixedField s) →*
    Matrix.SpecialLinearGroup (Fin 2) (Field s) where
  toFun k := upper s (u * k.toAdd.val)
  map_one' := by
    change upper s (u * 0) = 1
    rw [mul_zero]
    exact transvection_coeff_zero _
  map_mul' a b := by
    change upper s (u * (a.toAdd.val + b.toAdd.val)) = _
    rw [mul_add]
    exact transvection_add _ _ _

/-- The actual fixed-field line uK, embedded as upper root matrices. -/
def rootLine (u : Field s) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)) :=
  (rootLineHom s u).range

omit [NeZero s] in
theorem upper_injective : Function.Injective (upper s) := by
  intro u v h
  have he := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (Field s) => A.val 0 1) h
  simpa [upper, transvection_coe] using he

omit [NeZero s] in
theorem mem_rootLine_iff (u : Field s) (A : Matrix.SpecialLinearGroup (Fin 2) (Field s)) :
    A ∈ rootLine s u ↔ ∃ k : fixedField s, upper s (u * k.val) = A := by
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨k.toAdd, rfl⟩
  · rintro ⟨k, rfl⟩; exact ⟨Multiplicative.ofAdd k, rfl⟩

omit [NeZero s] in
theorem upper_mem_rootLine_iff {u : Field s} (hu : u ≠ 0) (v : Field s) :
    upper s v ∈ rootLine s u ↔ conjugation s (v / u) = v / u := by
  rw [mem_rootLine_iff]
  constructor
  · rintro ⟨k, hk⟩
    have he := upper_injective s hk
    rw [← he, mul_div_cancel_left₀ _ hu]
    exact k.property
  · intro hv
    exact ⟨⟨v / u, hv⟩, congrArg (upper s) (mul_div_cancel₀ v hu)⟩

omit [NeZero s] in
theorem rootLine_le_upper (u : Field s) : rootLine s u ≤ upperUnipotent (Field s) := by
  intro A hA
  obtain ⟨k, rfl⟩ := (mem_rootLine_iff s u A).mp hA
  exact (mem_upperUnipotent _ _).mpr ⟨_, rfl⟩

omit [NeZero s] in
theorem upper_mem_rootLine (u : Field s) : upper s u ∈ rootLine s u :=
  (mem_rootLine_iff s u _).mpr ⟨1, by simp⟩

theorem rootLine_one : rootLine s 1 = fixedRootGroup s := by
  ext A
  simp only [mem_rootLine_iff, one_mul, mem_fixedRootGroup_iff]

/-- The diagonal torus sends R_t onto precisely the indicated fixed-field line. -/
theorem fixedRoot_map_diag (a : Field s) (ha : a ≠ 0) :
    (fixedRootGroup s).map (MulAut.conj (diag2 a ha)).toMonoidHom = rootLine s (a ^ 2) := by
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨k, rfl⟩ := (mem_fixedRootGroup_iff s B).mp hB
    exact (mem_rootLine_iff s _ _).mpr ⟨k, (diag_conj_upper a ha _).symm⟩
  · intro hA
    obtain ⟨k, rfl⟩ := (mem_rootLine_iff s _ A).mp hA
    exact ⟨upper s k.val, (mem_fixedRootGroup_iff s _).mpr ⟨k, rfl⟩,
      diag_conj_upper a ha _⟩

theorem rootLine_eq_normalizer_conjugate {u : Field s} (hu : u ≠ 0) :
    ∃ g ∈ rankOneBorel (Field s),
      rootLine s u = (fixedRootGroup s).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨a, ha⟩ := isSquare_of_charTwo' u
  have ha0 : a ≠ 0 := by intro hz; simp [hz] at ha; exact hu ha
  refine ⟨diag2 a ha0, diag_mem_rankOneBorel a ha0, ?_⟩
  rw [fixedRoot_map_diag, sq, ← ha]

/-- Conversely, every normalizer conjugate is a genuine fixed-field line. -/
theorem normalizer_conjugate_eq_rootLine
    (g : Matrix.SpecialLinearGroup (Fin 2) (Field s)) (hg : g ∈ rankOneBorel (Field s)) :
    ∃ u : Field s, u ≠ 0 ∧
      (fixedRootGroup s).map (MulAut.conj g).toMonoidHom = rootLine s u := by
  have h10 := (mem_rankOneBorel_iff g).mp hg
  have hd : g.val 0 0 * g.val 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, h10, mul_zero, sub_zero] using g.property
  refine ⟨g.val 0 0 ^ 2, pow_ne_zero _ (left_ne_zero_of_mul_eq_one hd), ?_⟩
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨k, rfl⟩ := (mem_fixedRootGroup_iff s B).mp hB
    exact (mem_rootLine_iff s _ _).mpr ⟨k, (triangular_conj_upper h10 _).symm⟩
  · intro hA
    obtain ⟨k, rfl⟩ := (mem_rootLine_iff s _ A).mp hA
    exact ⟨upper s k.val, (mem_fixedRootGroup_iff s _).mpr ⟨k, rfl⟩,
      triangular_conj_upper h10 _⟩

omit [NeZero s] in
/-- A nonzero common parameter identifies two fixed-field lines. -/
theorem rootLine_eq_of_common {u v w : Field s} (hu : u ≠ 0) (hv : v ≠ 0)
    (hw : w ≠ 0) (hwu : upper s w ∈ rootLine s u)
    (hwv : upper s w ∈ rootLine s v) : rootLine s u = rootLine s v := by
  have hwu' := (upper_mem_rootLine_iff s hu w).mp hwu
  have hwv' := (upper_mem_rootLine_iff s hv w).mp hwv
  have huv : conjugation s (u / v) = u / v := by
    have he : (w / v) / (w / u) = u / v := by field_simp
    rw [← he, map_div₀, hwv', hwu']
  have hvu : conjugation s (v / u) = v / u := by
    have he : (u / v)⁻¹ = v / u := inv_div _ _
    rw [← he, map_inv₀, huv]
  have hle (a b : Field s) (ha : a ≠ 0) (hb : b ≠ 0)
      (hab : conjugation s (a / b) = a / b) : rootLine s a ≤ rootLine s b := by
    intro A hA
    obtain ⟨k, rfl⟩ := (mem_rootLine_iff s a A).mp hA
    apply (upper_mem_rootLine_iff s hb _).mpr
    have he : a * k.val / b = a / b * k.val := by ring
    have hk : conjugation s k.val = k.val := k.property
    rw [he, map_mul, hab, hk]
  exact le_antisymm (hle u v hu hv huv) (hle v u hv hu hvu)

omit [NeZero s] in
theorem rootLine_disjoint {u v : Field s} (hu : u ≠ 0) (hv : v ≠ 0)
    (hne : rootLine s u ≠ rootLine s v) : Disjoint (rootLine s u) (rootLine s v) := by
  rw [Subgroup.disjoint_def]
  intro A hAu hAv
  obtain ⟨w, rfl⟩ := (mem_upperUnipotent _ _).mp (rootLine_le_upper s u hAu)
  by_cases hw : w = 0
  · subst w; exact transvection_coeff_zero _
  · exact (hne (rootLine_eq_of_common s hu hv hw hAu hAv)).elim

/-- The nonidentity elements are partitioned by normalizer conjugates of R_t. -/
theorem root_partition (A : Matrix.SpecialLinearGroup (Fin 2) (Field s))
    (hA : A ∈ upperUnipotent (Field s)) (hne : A ≠ 1) :
    ∃! R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)),
      (∃ g ∈ rankOneBorel (Field s), R = (fixedRootGroup s).map (MulAut.conj g).toMonoidHom) ∧
      A ∈ R := by
  obtain ⟨u, rfl⟩ := (mem_upperUnipotent _ _).mp hA
  have hu : u ≠ 0 := by intro h; subst u; exact hne (transvection_coeff_zero _)
  refine ⟨rootLine s u, ⟨rootLine_eq_normalizer_conjugate s hu, upper_mem_rootLine s u⟩, ?_⟩
  rintro R ⟨⟨g, hg, rfl⟩, hR⟩
  obtain ⟨v, hv, he⟩ := normalizer_conjugate_eq_rootLine s g hg
  rw [he] at hR ⊢
  exact rootLine_eq_of_common s hv hu hu hR (upper_mem_rootLine s u)

/-- Distinct normalizer conjugates meet in the identity subgroup. -/
theorem normalizer_conjugates_disjoint
    (g k : Matrix.SpecialLinearGroup (Fin 2) (Field s))
    (hg : g ∈ rankOneBorel (Field s)) (hk : k ∈ rankOneBorel (Field s))
    (hne : (fixedRootGroup s).map (MulAut.conj g).toMonoidHom ≠
      (fixedRootGroup s).map (MulAut.conj k).toMonoidHom) :
    Disjoint ((fixedRootGroup s).map (MulAut.conj g).toMonoidHom)
      ((fixedRootGroup s).map (MulAut.conj k).toMonoidHom) := by
  obtain ⟨u, hu, he⟩ := normalizer_conjugate_eq_rootLine s g hg
  obtain ⟨v, hv, hf⟩ := normalizer_conjugate_eq_rootLine s k hk
  rw [he, hf] at hne ⊢
  exact rootLine_disjoint s hu hv hne

end Representation.OrthogonalFourMinus.RankOne
