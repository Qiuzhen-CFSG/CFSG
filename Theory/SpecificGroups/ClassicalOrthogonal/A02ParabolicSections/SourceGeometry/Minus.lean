/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
The complement coordinates adapt Minus/BinarySixObstruction/Generation/Reflections.lean.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module
public import Theory.SpecificGroups.ClassicalOrthogonal.A02ParabolicSections.SourceGeometry.OmegaRoot

/-!
# Actual minus orthogonal sections in singular-root normalizers

Deleting the first hyperbolic pair identifies its perpendicular complement
with the literal smaller minus form, retaining the chosen anisotropic plane.
Extension maps full orthogonal groups injectively, hence maps their actual
commutator subgroups. Iteration embeds the minus-six carrier and respects
its projective quotient in characteristic two.

Two singular roots, written as commutators using a spare hyperbolic pair,
certify that the marked root normalizer is a proper two-local. Complement
extension fixes the marked vector and places the smaller carrier there.
`minusTailSection` supplies the exact numerator and quotient marking used by
`EvenLie.OrthogonalSections.Source.Minus` in Aschbacher–Smith A.2.18,
printed p.40 (compare GLS3 §2.6).
-/

@[expose] public noncomputable section
universe u
namespace ClassicalOrthogonal.A02ParabolicSections.MinusTail
open Theory.AlgebraicGroup ClassicalOrthogonal.Quadratic
open ClassicalOrthogonal.ReflectionGeneration Subgroup
open Theory.SpecificGroups.LieType TheoremDRootNormalizer
variable {F : Type u} [Field F]

abbrev V (m : ℕ) := Minus.Space F m
abbrev Q (m : ℕ) (a : F) := Minus.form F m a
abbrev O (m : ℕ) (a : F) := quadraticIsometrySubgroup (Q m a)
abbrev M (m : ℕ) (a : F) := Minus.Omega F (V m) (Q m a)

def ve {m : ℕ} (i : Fin m) : V (F:=F) m := (Pi.single i (1,0), 0)
def vf {m : ℕ} (i : Fin m) : V (F:=F) m := (Pi.single i (0,1), 0)

@[simp] theorem q_ve {m : ℕ} (a : F) (i : Fin m) : Q m a (ve i) = 0 := by
  simp [ve, Minus.form_apply, Pi.single_apply, apply_ite]
@[simp] theorem q_vf {m : ℕ} (a : F) (i : Fin m) : Q m a (vf i) = 0 := by
  simp [vf, Minus.form_apply, Pi.single_apply, apply_ite]
@[simp] theorem polar_ve {m : ℕ} (a : F) (x : V m) (i : Fin m) :
    (Q m a).polarBilin x (ve i) = (x.1 i).2 := by
  rw [Minus.form_polar]
  simp [ve, Pi.single_apply, apply_ite]
@[simp] theorem polar_vf {m : ℕ} (a : F) (x : V m) (i : Fin m) :
    (Q m a).polarBilin x (vf i) = (x.1 i).1 := by
  rw [Minus.form_polar]
  simp [vf, Pi.single_apply, apply_ite]
@[simp] theorem polar_ve_vf {m : ℕ} (a : F) (i : Fin m) :
    (Q m a).polarBilin (ve i) (vf i) = 1 := by rw [polar_vf]; simp [ve]

def minusComplement (m : ℕ) (a : F) :
    (complementForm (Q (m+1) a) (ve 0) (vf 0)).IsometryEquiv (Q m a) where
  toFun x := ((fun i => x.val.1 i.succ), x.val.2)
  invFun x := ⟨(Fin.cons 0 x.1, x.2), by
    rw [mem_complement, polar_ve, polar_vf]
    exact ⟨rfl,rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    have hx := x.prop
    rw [mem_complement, polar_ve, polar_vf] at hx
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun j => rfl) i
      exact Prod.ext hx.2.symm hx.1.symm
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_app' x := by
    have hx := x.prop
    rw [mem_complement, polar_ve, polar_vf] at hx
    change Q m a _ = Q (m+1) a x.val
    simp [Q, Minus.form_apply, Fin.sum_univ_succ, hx.1, hx.2]

def tailFull (m : ℕ) (a : F) : O m a →* O (m+1) a :=
  (complementLift (Q (m+1) a) (ve 0) (vf 0) (q_ve a 0) (q_vf a 0)
    (polar_ve_vf a 0)).comp (isometryGroupTransport (minusComplement m a).symm).toMonoidHom

theorem tailFull_injective (m : ℕ) (a : F) : Function.Injective (tailFull m a) :=
  (complementLift_injective (Q (m+1) a) (ve 0) (vf 0) (q_ve a 0) (q_vf a 0)
    (polar_ve_vf a 0)).comp (isometryGroupTransport (minusComplement m a).symm).injective

def tailHom (m : ℕ) (a : F) : M m a →* M (m+1) a :=
  ((tailFull m a).comp (commutator (O m a)).subtype).codRestrict _ (by
    intro g
    have hm : tailFull m a g.val ∈ (commutator (O m a)).map (tailFull m a) :=
      Subgroup.mem_map_of_mem _ g.prop
    rw [map_commutator_eq] at hm
    exact Subgroup.commutator_mono le_top le_top hm)

theorem tailHom_injective (m : ℕ) (a : F) : Function.Injective (tailHom m a) := by
  intro g h he
  apply Subtype.ext
  exact tailFull_injective m a (congrArg (fun x : M (m+1) a => x.val) he)

theorem tailHom_fix (m : ℕ) (a : F) (g : M m a) :
    (tailHom m a g).val.val (ve 0) = ve 0 :=
  complementLift_fix_e (Q (m+1) a) (ve 0) (vf 0) (q_ve a 0) (q_vf a 0)
    (polar_ve_vf a 0) _

def tailIter (a : F) : (n : ℕ) → M 2 a →* M (3+n) a
  | 0 => tailHom 2 a
  | n+1 => (tailHom (3+n) a).comp (tailIter a n)

theorem tailIter_injective (a : F) (n : ℕ) : Function.Injective (tailIter a n) := by
  induction n with
  | zero => exact tailHom_injective 2 a
  | succ n ih => exact (tailHom_injective _ a).comp ih

theorem tailIter_fix (a : F) (n : ℕ) (g : M 2 a) :
    (tailIter a n g).val.val (ve 0) = ve 0 := by
  cases n <;> exact tailHom_fix _ _ _

def rootEF {m : ℕ} (a : F) {i j k : Fin m}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : M m a :=
  ⟨siegelElement (Q m a) (ve i) (vf j) (q_ve a i)
    (by rw [polar_vf]; simp [ve, Ne.symm hij]), by
    apply singular_root_mem_omega (Q m a) (ve i) (vf j) (ve k) (vf k)
      (q_ve a i) (q_vf a j) (q_vf a k)
    all_goals simp only [polar_ve, polar_vf]
    all_goals simp [ve, vf, Ne.symm hik, Ne.symm hjk]⟩

def rootFE {m : ℕ} (a : F) {i j k : Fin m}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : M m a :=
  ⟨siegelElement (Q m a) (vf i) (ve j) (q_vf a i)
    (by rw [polar_ve]; simp [vf, Ne.symm hij]), by
    apply singular_root_mem_omega (Q m a) (vf i) (ve j) (ve k) (vf k)
      (q_vf a i) (q_ve a j) (q_vf a k)
    all_goals simp only [polar_ve, polar_vf]
    all_goals simp [ve, vf, Ne.symm hik, Ne.symm hjk]⟩

def twoSubgroup (a : F) (n : ℕ) : Subgroup (M (3+n) a) :=
  omegaRootGroup (Q (3+n) a) (ve 0) (q_ve a 0)

private def r (a : F) (n : ℕ) : M (3+n) a :=
  rootEF a (i:=0) (j:=⟨1,by omega⟩) (k:=⟨2,by omega⟩)
    (by simp) (by simp) (by simp)
private def s (a : F) (n : ℕ) : M (3+n) a :=
  rootFE a (i:=0) (j:=⟨1,by omega⟩) (k:=⟨2,by omega⟩)
    (by simp) (by simp) (by simp)

private theorem r_mem (a : F) (n : ℕ) : r a n ∈ twoSubgroup a n :=
  ⟨Multiplicative.ofAdd ⟨vf ⟨1,by omega⟩,
    by change (Q (3+n) a).polarBilin (ve 0) (vf ⟨1,by omega⟩) = 0
       rw [polar_vf]; simp [ve]⟩, rfl⟩

theorem twoSubgroup_ne_bot (a : F) (n : ℕ) : twoSubgroup a n ≠ ⊥ := by
  intro ht
  have he : r a n = 1 := Subgroup.mem_bot.mp (ht ▸ r_mem a n)
  have hv := congrArg (fun g : M (3+n) a => ((g.val.val (ve ⟨1,by omega⟩)).1 0).1) he
  change ((siegel (Q (3+n) a) (ve 0) (vf ⟨1,by omega⟩) (ve ⟨1,by omega⟩)).1 0).1 = _ at hv
  simp only [siegel, polar_ve, polar_vf, q_vf] at hv
  simp [ve, vf] at hv

variable [CharP F 2]

theorem twoSubgroup_two (a : F) (n : ℕ) : IsPGroup 2 (twoSubgroup a n) :=
  omegaRootGroup_two _ _ _

theorem twoNormalizer_ne_top (a : F) (n : ℕ) :
    normalizer (twoSubgroup a n : Set (M (3+n) a)) ≠ ⊤ := by
  let j : Fin (3+n) := ⟨1,by omega⟩
  have hs2 : (s a n)^2 = 1 := by
    apply Subtype.ext
    exact congrArg (fun g : elementarySubgroup (Q (3+n) a) => g.val)
      (root_square (Q (3+n) a) (vf 0) (ve j) (q_vf a 0)
        (by rw [polar_ve]; simp [vf, j]))
  have hsi : (s a n)⁻¹ = s a n := inv_eq_of_mul_eq_one_left ((pow_two (s a n)) ▸ hs2)
  intro ht
  have hs : s a n ∈ normalizer (twoSubgroup a n : Set (M (3+n) a)) := by rw [ht]; trivial
  have hc := omegaRootGroup_fix (Q (3+n) a) (ve 0) (q_ve a 0)
    ((mem_normalizer_iff.mp hs (r a n)).mp (r_mem a n))
  change (s a n).val.val ((r a n).val.val ((s a n)⁻¹.val.val (ve 0))) = ve 0 at hc
  rw [hsi] at hc
  have hse : (s a n).val.val (ve 0) = ve 0 - ve j := by
    change siegel (Q (3+n) a) (vf 0) (ve j) (ve 0) = _
    simp only [siegel, polar_ve, polar_vf, q_ve]
    simp [ve, j]
  have hsj : (s a n).val.val (ve j) = ve j := by
    change siegel (Q (3+n) a) (vf 0) (ve j) (ve j) = _
    simp only [siegel, polar_ve, polar_vf, q_ve]
    simp [ve, j]
  have hre : (r a n).val.val (ve 0) = ve 0 := by
    change siegel (Q (3+n) a) (ve 0) (vf j) (ve 0) = _
    simp only [siegel, polar_ve, polar_vf, q_vf]
    simp [ve, j]
  have hrj : (r a n).val.val (ve j) = ve j + ve 0 := by
    change siegel (Q (3+n) a) (ve 0) (vf j) (ve j) = _
    simp only [siegel, polar_ve, polar_vf, q_vf]
    simp [ve, j]
  rw [hse, map_sub, hre, hrj, map_sub, map_add, hse, hsj] at hc
  have hv := congrArg (fun x : V (F:=F) (3+n) => (x.1 0).1) hc
  simp [ve, j] at hv

variable [Finite F]

def modelEquiv (m : ℕ) : M m (Minus.parameter F) ≃* ClassicalGroup.POmegaMinus (m+1) F :=
  minusOmegaEquivProjective (m+1)

def projectiveTwo (n : ℕ) : Subgroup (ClassicalGroup.POmegaMinus (3+n+1) F) :=
  (twoSubgroup (Minus.parameter F) n).map (modelEquiv (3+n)).toMonoidHom

def projectiveTail (n : ℕ) : ClassicalGroup.POmegaMinus 3 F →*
    ClassicalGroup.POmegaMinus (3+n+1) F :=
  (modelEquiv (3+n)).toMonoidHom.comp
    ((tailIter (Minus.parameter F) n).comp (modelEquiv 2).symm.toMonoidHom)

theorem projectiveTail_injective (n : ℕ) : Function.Injective (projectiveTail (F:=F) n) :=
  (modelEquiv _).injective.comp ((tailIter_injective _ _).comp (modelEquiv _).symm.injective)

def minusTailSection (n : ℕ) : NormalizerSection (ClassicalGroup.POmegaMinus (3+n+1) F)
    (ClassicalGroup.POmegaMinus 3 F) := by
  refine NormalizerSection.ofEmbedding (projectiveTwo n) ?_ ?_ ?_
    (projectiveTail n) (projectiveTail_injective n) ?_
  · exact fun h => twoSubgroup_ne_bot _ n
      ((Subgroup.map_eq_bot_iff_of_injective _ (modelEquiv _).injective).mp h)
  · exact (twoSubgroup_two (Minus.parameter F) n).of_equiv
      ((twoSubgroup _ n).equivMapOfInjective _ (modelEquiv _).injective)
  · intro ht
    apply twoNormalizer_ne_top (Minus.parameter F) n
    apply Subgroup.map_injective (modelEquiv _).injective
    exact (map_equiv_normalizer_eq (twoSubgroup (Minus.parameter F) n)
      (modelEquiv (3+n))).trans (ht.trans
        (Subgroup.map_top_of_surjective _ (modelEquiv (3+n)).surjective).symm)
  · rintro _ ⟨g,rfl⟩
    rw [projectiveTwo, ← map_equiv_normalizer_eq]
    refine ⟨tailIter (Minus.parameter F) n ((modelEquiv 2).symm g), ?_, rfl⟩
    exact fix_mem_omegaRootNormalizer _ _ _ _ (tailIter_fix _ _ _)

end ClassicalOrthogonal.A02ParabolicSections.MinusTail
