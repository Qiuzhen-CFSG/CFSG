/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
The Siegel parameter and conjugation arguments adapt the licensed construction
in SplitOdd/BinaryEightObstruction/Simplicity/Basic.lean to arbitrary forms.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.NormalizedComplement
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.ScalarQuotients
public import Theory.SpecificGroups.LieType.A02ParabolicSections

/-!
# Singular-direction root normalizers for orthogonal sections

The additive Siegel parameter group at a singular vector is a two-group in
characteristic two. Every isometry fixing that vector normalizes it. In a
split space, two coordinate roots witness both nontriviality and properness
of its normalizer: a conjugated root moves the marked vector. These explicit
calculations require neither simplicity nor a parabolic classification.

The complement embeddings in `SourceGeometry` use this actual two-local for
Aschbacher–Smith A.2.18, printed p.40; compare GLS3 §2.6.
-/

@[expose] public noncomputable section
universe u
namespace ClassicalOrthogonal.A02ParabolicSections
open Theory.AlgebraicGroup Quadratic ReflectionGeneration Subgroup
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

def root (u v : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) : elementarySubgroup Q :=
  ⟨siegelElement Q u v hu huv, siegelElement_mem Q u v hu huv⟩

theorem root_zero (u : V) (hu : Q u = 0) : root Q u 0 hu (by simp) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  exact siegel_zero Q u

theorem root_add (u v w : V) (hu : Q u = 0)
    (hv : Q.polarBilin u v = 0) (hw : Q.polarBilin u w = 0) :
    root Q u (v+w) hu (by rw [map_add, hv, hw, add_zero]) =
      root Q u v hu hv * root Q u w hu hw := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact (siegel_add Q u v w x hu hv hw).symm

theorem root_conj (g : elementarySubgroup Q) (u v : V)
    (hu : Q u = 0) (hv : Q.polarBilin u v = 0) :
    g * root Q u v hu hv * g⁻¹ =
      root Q (g.val.val u) (g.val.val v)
        ((isometry_preserves Q g.val u).trans hu)
        ((isometry_polar Q (isometryCarrierEquiv Q g.val) u v).trans hv) := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (isometryCarrierEquiv Q g.val) (siegel Q u v (g.val.val.symm x)) = _
  rw [siegel_covariant]
  exact congrArg (siegel Q (g.val.val u) (g.val.val v)) (g.val.val.apply_symm_apply x)

def rootHom (u : V) (hu : Q u = 0) :
    Multiplicative (Q.polarBilin u).ker →* elementarySubgroup Q where
  toFun v := root Q u v.toAdd.val hu v.toAdd.prop
  map_one' := root_zero Q u hu
  map_mul' v w := root_add Q u v.toAdd.val w.toAdd.val hu v.toAdd.prop w.toAdd.prop

def rootGroup (u : V) (hu : Q u = 0) : Subgroup (elementarySubgroup Q) :=
  (rootHom Q u hu).range

theorem root_mem (u v : V) (hu : Q u = 0) (hv : Q.polarBilin u v = 0) :
    root Q u v hu hv ∈ rootGroup Q u hu := ⟨Multiplicative.ofAdd ⟨v,hv⟩, rfl⟩

theorem rootGroup_fix (u : V) (hu : Q u = 0) {g : elementarySubgroup Q}
    (hg : g ∈ rootGroup Q u hu) : g.val.val u = u := by
  rcases hg with ⟨v,rfl⟩
  exact siegel_fix Q u v.toAdd.val hu v.toAdd.prop

theorem rootGroup_two [CharP F 2] (u : V) (hu : Q u = 0) :
    IsPGroup 2 (rootGroup Q u hu) := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  obtain ⟨v, hv⟩ := x.prop
  change x.val ^ (2^1) = 1
  rw [← hv, ← map_pow]
  have hp : v^2 = 1 := by
    change Multiplicative.ofAdd (2 • v.toAdd) = Multiplicative.ofAdd 0
    congr 1
    apply Subtype.ext
    change (2:ℕ) • v.toAdd.val = 0
    rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F 2, zero_smul]
  simp only [pow_one, hp, map_one]

theorem fix_mem_rootNormalizer (u : V) (hu : Q u = 0)
    (g : elementarySubgroup Q) (hg : g.val.val u = u) :
    g ∈ normalizer (rootGroup Q u hu : Set (elementarySubgroup Q)) := by
  have hf (g : elementarySubgroup Q) (hg : g.val.val u = u)
      {a : elementarySubgroup Q} (ha : a ∈ rootGroup Q u hu) :
      g * a * g⁻¹ ∈ rootGroup Q u hu := by
    rcases ha with ⟨v,rfl⟩
    have hv : Q.polarBilin u (g.val.val v.toAdd.val) = 0 := by
      have h := (isometry_polar Q (isometryCarrierEquiv Q g.val) u v.toAdd.val).trans v.toAdd.prop
      change Q.polarBilin (g.val.val u) (g.val.val v.toAdd.val) = 0 at h
      simpa only [hg] using h
    refine ⟨Multiplicative.ofAdd ⟨g.val.val v.toAdd.val, hv⟩, ?_⟩
    change root Q u (g.val.val v.toAdd.val) _ _ = g * root Q u _ _ _ * g⁻¹
    convert (root_conj Q g u v.toAdd.val hu v.toAdd.prop).symm using 1
    simp only [hg]
  rw [mem_normalizer_iff]
  intro a
  refine ⟨hf g hg, fun ha => ?_⟩
  have hi : g⁻¹.val.val u = u := g.val.val.symm_apply_eq.mpr hg.symm
  have hb := hf g⁻¹ hi ha
  simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hb

theorem root_square [CharP F 2] (u v : V) (hu : Q u = 0)
    (hv : Q.polarBilin u v = 0) : root Q u v hu hv ^ 2 = 1 := by
  rw [pow_two, ← root_add]
  have hvv : v+v=0 := by
    rw [← two_smul ℕ v, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F 2, zero_smul]
  simpa only [hvv] using root_zero Q u hu

variable {Q}
variable {n : ℕ}

def splitRootGroup (i : Fin n) : Subgroup (OmegaPlus n F) :=
  rootGroup (formD n F) (e i) (formD_e i)

theorem splitRootGroup_ne_bot {i j : Fin n} (hij : i ≠ j) :
    splitRootGroup (F:=F) i ≠ ⊥ := by
  let a : OmegaPlus n F := root (formD n F) (e i) (f j) (formD_e i)
    (by rw [polarD_f]; simp [ClassicalOrthogonal.e, hij])
  have ha : a ∈ splitRootGroup i := root_mem _ _ _ _ _
  intro ht
  have heq : a = 1 := Subgroup.mem_bot.mp (ht ▸ ha)
  have hv := congrArg (fun x : OmegaPlus n F => x.val.val (e j)) heq
  change siegel (formD n F) (e i) (f j) (e j) = e j at hv
  have hc := congrFun hv (.inl i)
  simp only [siegel, polarD_e, polarD_f, formD_f] at hc
  simp [ClassicalOrthogonal.e, hij] at hc

theorem splitRootNormalizer_ne_top [CharP F 2] {i j : Fin n} (hij : i ≠ j) :
    normalizer (splitRootGroup (F:=F) i : Set (OmegaPlus n F)) ≠ ⊤ := by
  let a : OmegaPlus n F := root (formD n F) (e i) (f j) (formD_e i)
    (by rw [polarD_f]; simp [ClassicalOrthogonal.e, hij])
  let b : OmegaPlus n F := root (formD n F) (f i) (e j) (formD_f i)
    (by rw [polar_swap, polarD_f]; simp [ClassicalOrthogonal.e, Ne.symm hij])
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by
    change b*b=1
    exact (pow_two b) ▸ root_square _ _ _ _ _)
  intro ht
  have hb : b ∈ normalizer (splitRootGroup (F:=F) i : Set (OmegaPlus n F)) := by
    rw [ht]; trivial
  have ha : a ∈ splitRootGroup i := root_mem _ _ _ _ _
  have hc := rootGroup_fix (formD n F) (e i) (formD_e i)
    ((mem_normalizer_iff.mp hb a).mp ha)
  change b.val.val (a.val.val (b⁻¹.val.val (e i))) = e i at hc
  rw [hbi] at hc
  have hbe : b.val.val (e i) = e i - e j := by
    change siegel (formD n F) (f i) (e j) (e i) = _
    simp only [siegel, polarD_e, polarD_f, formD_e]
    simp [ClassicalOrthogonal.e]
  have hbj : b.val.val (e j) = e j := by
    change siegel (formD n F) (f i) (e j) (e j) = _
    simp only [siegel, polarD_e, polarD_f, formD_e]
    simp [ClassicalOrthogonal.e, hij]
  have hai : a.val.val (e i) = e i := by
    change siegel (formD n F) (e i) (f j) (e i) = _
    simp only [siegel, polarD_e, polarD_f, formD_f]
    simp [ClassicalOrthogonal.e, Ne.symm hij]
  have haj : a.val.val (e j) = e j + e i := by
    change siegel (formD n F) (e i) (f j) (e j) = _
    simp only [siegel, polarD_e, polarD_f, formD_f]
    simp [ClassicalOrthogonal.e]
  rw [hbe, map_sub, hai, haj, map_sub, map_add, hbe, hbj] at hc
  have hv := congrFun hc (.inl i)
  simp [ClassicalOrthogonal.e, hij] at hv

end ClassicalOrthogonal.A02ParabolicSections
