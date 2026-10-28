module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.Basic
public import Theory.SpecificGroups.PSp4Three.Generation
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.FieldTheory.Perfect
import Mathlib.Tactic.LinearCombination

/-!
# Orthogonal stabilizers are maximal in Sp₄(4)

A polar-compatible quadratic four-form has a maximal proper isometry
stabilizer in the literal symplectic matrix group. If an overgroup moves
the form, the square root of its quadratic defect is a nonzero functional.
On its affine level one, the two forms cannot take only the values zero
and one: polarization would make a three-space totally isotropic.
Thus two different nonzero parameters occur in one transvection root.
Over F₄ they generate that entire root. Equal-norm reflection transport
then supplies all nonsingular roots, and conjugation supplies the singular
roots. Transvection generation finishes the proof for both orthogonal types.

This is the maximality calculation used in Aschbacher--Smith 11.2.2,
printed p.767. The complement and original-subgroup applications are in
ComplementMaximality and OriginalMaximality. It does not yet prove that
outer field actors preserve the component orbit; that remains with
qt-d-1222-natural-weak-parameters and its final source assembly owner
qt-d-1222-natural-weak-closure-source.
-/

open ClassicalOrthogonal.Quadratic
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalMaximality
universe u
variable {F W : Type u} [Field F] [CharP F 2] [AddCommGroup W] [Module F W]

private theorem distinct_pairings (Q : QuadraticForm F W)
    (hnd : Q.polarBilin.Nondegenerate) {u v : W}
    (hu : Q u ≠ 0) (hq : Q u = Q v) (hne : u ≠ v) (a : F) :
    ∃ w, Q.polarBilin u w = 1 ∧ Q.polarBilin v w = a := by
  obtain ⟨x,hx⟩ := exists_normalized_partner Q u (fun hz => hu (hnd.1 u hz ▸ Q.map_zero))
  have hex : ∃ y, Q.polarBilin u y = 0 ∧ Q.polarBilin v y ≠ 0 := by
    by_contra! hn
    have hvu : v = (Q.polarBilin v x) • u := by
      apply sub_eq_zero.mp
      apply hnd.1
      intro y
      have hh := hn (y - Q.polarBilin u y • x) (by simp only [map_sub,map_smul,hx,smul_eq_mul,mul_one,sub_self])
      simp only [map_sub,map_smul,smul_eq_mul] at hh
      simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
      linear_combination hh
    have hs : (Q.polarBilin v x)^2 = 1 := by
      have hh := hq
      rw [hvu,Q.map_smul,smul_eq_mul] at hh
      exact (mul_right_cancel₀ hu (by simpa only [one_mul,pow_two] using hh.symm))
    have hs1 : Q.polarBilin v x = 1 := CharTwo.sq_injective (by simpa using hs)
    exact hne (by simpa only [hs1,one_smul] using hvu.symm)
  obtain ⟨y,hy,hyv⟩ := hex
  refine ⟨x + ((a-Q.polarBilin v x)/Q.polarBilin v y) • y,?_,?_⟩
  · simp only [map_add,map_smul,hx,hy,smul_zero,add_zero]
  · simp only [map_add,map_smul,smul_eq_mul]
    rw [div_mul_cancel₀ _ hyv]
    ring

private theorem reflection_equal (Q : QuadraticForm F W) {u v : W}
    (hq : Q u = Q v) (hp : Q.polarBilin u v ≠ 0) :
    ∃ g : Q.IsometryEquiv Q, g u = v := by
  have hs : Q (u-v) = Q.polarBilin u v := by
    rw [sub_value,hq,CharTwo.add_self_eq_zero,zero_sub,CharTwo.neg_eq]
  refine ⟨reflectionIsometry Q (u-v) (hs ▸ hp),?_⟩
  change reflectionLinear Q (u-v) (hs ▸ hp) u = v
  rw [reflectionLinear_apply]
  have hb : Q.polarBilin u (u-v) = Q.polarBilin u v := by
    rw [map_sub,polar_self,CharTwo.two_eq_zero,zero_mul,zero_sub,CharTwo.neg_eq]
  rw [hs,hb,inv_mul_cancel₀ hp,one_smul,sub_sub_cancel]

theorem equal_value_transitive (Q : QuadraticForm F W)
    (hnd : Q.polarBilin.Nondegenerate) (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    {u v : W} (hu : Q u ≠ 0) (hq : Q u = Q v) :
    ∃ g : Q.IsometryEquiv Q, g u = v := by
  by_cases he : u = v
  · exact ⟨QuadraticMap.IsometryEquiv.refl Q,he⟩
  by_cases hp : Q.polarBilin u v ≠ 0
  · exact reflection_equal Q hq hp
  push Not at hp
  obtain ⟨w,huw,hvw⟩ := distinct_pairings Q hnd hu hq he a
  have huu : Q.polarBilin u u = 0 := by rw [polar_self,CharTwo.two_eq_zero,zero_mul]
  have hvv : Q.polarBilin v v = 0 := by rw [polar_self,CharTwo.two_eq_zero,zero_mul]
  have hvu : Q.polarBilin v u = 0 := (polar_swap Q v u).trans hp
  have huv : Q (u+v) = 0 := by
    rw [QuadraticMap.map_add Q]; change Q u + Q v + Q.polarBilin u v = 0
    rw [hq,hp,CharTwo.add_self_eq_zero,add_zero]
  have hwuv : Q.polarBilin w (u+v) = 1+a := by
    rw [map_add,polar_swap Q w u,polar_swap Q w v,huw,hvw]
  have hden : 1+a ≠ 0 := by
    intro hh
    exact ha1 (by simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_right hh))
  let z := w + ((Q u-Q w)/(1+a)) • (u+v)
  have hqz : Q z = Q u := by
    dsimp [z]
    rw [ClassicalOrthogonal.Quadratic.add_smul,huv,hwuv,mul_zero,add_zero,div_mul_cancel₀ _ hden]
    ring
  have huz : Q.polarBilin u z = 1 := by simp only [z,map_add,map_smul,huu,hp,add_zero,smul_zero,huw]
  have hvz : Q.polarBilin v z = a := by simp only [z,map_add,map_smul,hvu,hvv,add_zero,smul_zero,hvw]
  obtain ⟨g,hg⟩ := reflection_equal Q hqz.symm (huz ▸ one_ne_zero)
  obtain ⟨k,hk⟩ := reflection_equal Q (hqz.trans hq)
    (by rw [polar_swap Q z v,hvz]; exact ha0)
  exact ⟨g.trans k,by change k (g u) = v; rw [hg,hk]⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalMaximality

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalMaximality
open Matrix.PSp4Three
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

def quadraticStabilizer (Q : QuadraticForm F (Vector 2 F)) : Subgroup (Sp 2 F) where
  carrier := {g | ∀ x, Q (g • x) = Q x}
  one_mem' := by simp
  mul_mem' := by intro g h hg hh x; rw [mul_smul,hg,hh]
  inv_mem' := by
    intro g hg x
    have h := hg (g⁻¹ • x)
    simpa only [smul_inv_smul] using h.symm

omit [Finite F] in
private theorem reflection_mem (Q : QuadraticForm F (Vector 2 F))
    (hp : Q.polarBilin = form) {v : Vector 2 F} (hv : Q v ≠ 0) :
    transvection v (Q v)⁻¹ ∈ quadraticStabilizer Q := by
  intro x
  have hh := reflection_preserves Q v hv x
  change Q (reflectionLinear Q v hv x) = Q x at hh
  rw [reflectionLinear_apply,sub_eq_add_neg,←neg_smul,CharTwo.neg_eq,hp] at hh
  simpa only [transvection_apply] using hh

omit [CharP F 2] [Finite F] in
private theorem isometry_mem (Q : QuadraticForm F (Vector 2 F))
    (hp : Q.polarBilin = form) (g : Q.IsometryEquiv Q) :
    ∃ a ∈ quadraticStabilizer Q, ∀ x, a • x = g x := by
  have hg : ∀ x y, form (g x) (g y) = form x y := by
    rw [←hp]
    exact isometry_polar Q g
  exact ⟨ofLinear g.toLinearEquiv hg,fun x => by rw [ofLinear_apply]; exact g.map_app x,
    ofLinear_apply _ _⟩

/-- One full transvection root and the orthogonal stabilizer generate Sp4. -/
theorem eq_top_of_full_root (Q : QuadraticForm F (Vector 2 F))
    (hp : Q.polarBilin = form) (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (H : Subgroup (Sp 2 F)) (hH : quadraticStabilizer Q ≤ H)
    (u : Vector 2 F) (hu : Q u ≠ 0)
    (hroot : ∀ t, transvection u t ∈ H) : H = ⊤ := by
  have hnd : Q.polarBilin.Nondegenerate := hp.symm ▸ form_nondegenerate
  have hnonsingular : ∀ v, Q v ≠ 0 → ∀ t, transvection v t ∈ H := by
    intro v hv t
    obtain ⟨c,hc⟩ := (Finite.surjective_of_injective
      (f := fun x : F => x^2) CharTwo.sq_injective) (Q v / Q u)
    change c^2 = Q v / Q u at hc
    have hcv : Q (c • u) = Q v := by
      rw [Q.map_smul,smul_eq_mul,←pow_two,hc,div_mul_cancel₀ _ hu]
    obtain ⟨k,hk⟩ := equal_value_transitive Q hnd a ha0 ha1
      (hcv.symm ▸ hv) hcv
    obtain ⟨g,hg,hgx⟩ := isometry_mem Q hp k
    rw [←hk,←hgx,←transvection_conjugate]
    exact H.mul_mem (H.mul_mem (hH hg) (by rw [transvection_scale]; exact hroot _))
      (H.inv_mem (hH hg))
  have hall : ∀ v t, transvection v t ∈ H := by
    intro v t
    by_cases hv : Q v ≠ 0
    · exact hnonsingular v hv t
    push Not at hv
    by_cases hz : v = 0
    · subst v; simp
    obtain ⟨w,hw⟩ := exists_form_left hz 1
    let w' := w + (a-Q w) • v
    have hqw : Q w' = a := by
      change Q (w + (a-Q w) • v) = a
      rw [ClassicalOrthogonal.Quadratic.add_smul,hp,hv,hw,mul_zero,add_zero,mul_one]
      ring
    have hwp : form w' v = 1 := by simp only [w',map_add,map_smul,
      LinearMap.add_apply,LinearMap.smul_apply,form_self,smul_zero,add_zero,hw]
    have hqwv : Q (w'+v) = a+1 := by
      rw [QuadraticMap.map_add Q]
      change Q w'+Q v+Q.polarBilin w' v=a+1
      rw [hqw,hv,hp,hwp,add_zero]
    have han : a+1 ≠ 0 := by
      intro hh
      exact ha1 (by simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh)
    have hm : transvection w' 1 • (w'+v) = v := by
      rw [transvection_apply]
      have hb : form (w'+v) w' = 1 := by
        rw [map_add (form (n := 2) (F := F)) w' v,LinearMap.add_apply,form_self,form_swap v w',hwp]
        simp only [CharTwo.neg_eq,zero_add]
      rw [hb,mul_one,one_smul,add_right_comm,show w'+w'=0 by ext i; exact CharTwo.add_self_eq_zero _,zero_add]
    rw [←hm,←transvection_conjugate]
    exact H.mul_mem (H.mul_mem (hnonsingular w' (hqw.symm ▸ ha0) 1)
      (hnonsingular (w'+v) (hqwv.symm ▸ han) t))
      (H.inv_mem (hnonsingular w' (hqw.symm ▸ ha0) 1))
  apply top_unique
  rw [←transvectionGroup_eq_top (n := 2) (F := F)]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨v,t,rfl⟩
  exact hall v t
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalMaximality

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalMaximality
universe u
variable {F W : Type u} [Field F] [CharP F 2] [AddCommGroup W] [Module F W]

omit [CharP F 2] in
private theorem polar_second_difference (Q : QuadraticForm F W) (x y z : W) :
    Q.polarBilin y z = Q (x+y+z) - Q (x+y) - Q (x+z) + Q x := by
  simp only [QuadraticMap.map_add Q]
  change Q.polarBilin y z =
    (Q x+Q y+Q.polarBilin x y)+Q z+Q.polarBilin (x+y) z-
      (Q x+Q y+Q.polarBilin x y)-(Q x+Q z+Q.polarBilin x z)+Q x
  rw [map_add Q.polarBilin,LinearMap.add_apply]
  ring

/-- A nonzero affine hyperplane cannot have only binary quadratic values
in a nondegenerate four-space over a field larger than F2. -/
theorem exists_distinct_nonzero_values [FiniteDimensional F W]
    (Q R : QuadraticForm F W) (hnd : Q.polarBilin.Nondegenerate)
    (hd : Module.finrank F W = 4) (l : W →ₗ[F] F) (hl : l ≠ 0)
    (hR : ∀ x, R x = Q x + (l x)^2)
    (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ∃ v, Q v ≠ 0 ∧ R v ≠ 0 ∧ Q v ≠ R v := by
  by_contra! hn
  obtain ⟨x,hx⟩ := LinearMap.surjective hl 1
  have htrace : ∀ v, l v = 1 → (Q v)^2 = Q v := by
    intro v hv
    have hRv : R v = Q v + 1 := by rw [hR,hv,one_pow]
    by_cases hq : Q v = 0
    · rw [hq,zero_pow (by decide)]
    by_cases hr : R v = 0
    · have hq1 : Q v = 1 := by
        have hh : Q v + 1 = 0 := hRv.symm.trans hr
        simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh
      rw [hq1,one_pow]
    · have hh := hn v hq hr
      rw [hRv] at hh
      exact False.elim (one_ne_zero (add_eq_left.mp hh.symm))
  have hbtrace : ∀ y z, l y = 0 → l z = 0 →
      (Q.polarBilin y z)^2 = Q.polarBilin y z := by
    intro y z hy hz
    rw [polar_second_difference Q x y z]
    simp only [CharTwo.sub_eq_add,CharTwo.add_sq,
      htrace (x+y+z) (by simp only [map_add,hx,hy,hz,add_zero]),
      htrace (x+y) (by simp only [map_add,hx,hy,add_zero]),
      htrace (x+z) (by simp only [map_add,hx,hz,add_zero]),htrace x hx]
  have horth : l.ker ≤ LinearMap.BilinForm.orthogonal Q.polarBilin l.ker := by
    intro z hz y hy
    by_contra hne
    have h1 := hbtrace y z hy hz
    have h2 := hbtrace (a • y) z (by rw [map_smul,show l y = 0 from hy,smul_zero]) hz
    rw [map_smul,LinearMap.smul_apply,smul_eq_mul,mul_pow,h1] at h2
    have hs : a^2 = a := mul_right_cancel₀ hne h2
    exact (eq_zero_or_one_of_sq_eq_self hs).elim ha0 ha1
  have he := Module.Dual.finrank_ker_add_one_of_ne_zero hl
  have hm := Submodule.finrank_mono horth
  rw [LinearMap.BilinForm.finrank_orthogonal hnd,hd] at hm
  rw [hd] at he
  omega
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalMaximality

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalMaximality
open Matrix.PSp4Three
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] in
private theorem exists_nonbinary_scalar (hF : Nat.card F = 4) :
    ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
  classical
  let := Fintype.ofFinite F
  have hh : ({0,1} : Finset F).card < (Finset.univ : Finset F).card := by
    rw [Finset.card_univ,←Nat.card_eq_fintype_card,hF]
    have := Finset.card_le_two (a := (0 : F)) (b := 1)
    omega
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hh
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ha
  exact ⟨a,ha⟩

private theorem defect (Q : QuadraticForm F (Vector 2 F))
    (hp : Q.polarBilin = form) (g : Sp 2 F) :
    ∃ l : Vector 2 F →ₗ[F] F, ∀ x, Q (g • x) = Q x + (l x)^2 := by
  let sqr := frobeniusEquiv F 2
  let l : Vector 2 F →ₗ[F] F := {
    toFun := fun x => sqr.symm (Q (g • x)-Q x)
    map_add' := by
      intro x y
      apply sqr.injective
      have hsm : g • (x+y) = g • x+g • y := map_add (toLinear g) x y
      simp only [map_add,sqr.apply_symm_apply]
      rw [hsm,QuadraticMap.map_add Q,QuadraticMap.map_add Q]
      change Q (g • x)+Q (g • y)+Q.polarBilin (g • x) (g • y)-
        (Q x+Q y+Q.polarBilin x y) = _
      rw [hp,show form (g • x) (g • y) = form x y from preserves g x y]
      ring
    map_smul' := by
      intro c x
      apply sqr.injective
      have hsm : g • (c • x) = c • (g • x) := map_smul (toLinear g) c x
      simp only [smul_eq_mul,map_mul,sqr.apply_symm_apply]
      rw [hsm,Q.map_smul,Q.map_smul]
      change c*c*Q (g • x)-c*c*Q x=c^2*(Q (g • x)-Q x)
      ring }
  refine ⟨l,?_⟩
  intro x
  have hh : (l x)^2 = Q (g • x)-Q x := sqr.apply_symm_apply _
  rw [hh]
  ring

private theorem full_root_of_two (hF : Nat.card F = 4)
    (H : Subgroup (Sp 2 F)) (v : Vector 2 F) {a b : F}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hva : transvection v a ∈ H) (hvb : transvection v b ∈ H) :
    ∀ t, transvection v t ∈ H := by
  classical
  let := Fintype.ofFinite F
  have hab0 : a+b ≠ 0 := by
    intro hh
    exact hab (by simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh)
  have hc : ({0,a,b,a+b} : Finset F).card = 4 := by
    simp [ha,hb,hab,Ne.symm ha,Ne.symm hb,Ne.symm hab0]
  have hcover : ({0,a,b,a+b} : Finset F) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hc,←Nat.card_eq_fintype_card,hF]
  intro t
  have ht : t ∈ ({0,a,b,a+b} : Finset F) := hcover.symm ▸ Finset.mem_univ t
  simp only [Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · simp
  · exact hva
  · exact hvb
  · rw [transvection_add]; exact H.mul_mem hva hvb

/-- The full isometry stabilizer of any polar-compatible four-form over F4
is a maximal proper subgroup of the literal symplectic matrix group. -/
theorem quadraticStabilizer_isCoatom (hF : Nat.card F = 4)
    (Q : QuadraticForm F (Vector 2 F)) (hp : Q.polarBilin = form) :
    IsCoatom (quadraticStabilizer Q) := by
  classical
  obtain ⟨a,ha0,ha1⟩ := exists_nonbinary_scalar hF
  have hnd : Q.polarBilin.Nondegenerate := hp.symm ▸ form_nondegenerate
  have hproper : quadraticStabilizer Q ≠ ⊤ := by
    intro ht
    let v : Vector 2 F := e 0
    have hv : v ≠ 0 := by
      intro hz
      have hh : form v (f 0) = (1 : F) := by simp [v,Matrix.PSp4Three.e]
      rw [hz,map_zero,LinearMap.zero_apply] at hh
      exact zero_ne_one hh
    obtain ⟨x,hx⟩ := exists_form_left hv 1
    have he (t : F) : t^2*Q v+t = 0 := by
      have hh := (show transvection v t ∈ quadraticStabilizer Q from ht ▸ Subgroup.mem_top _) x
      rw [transvection_apply,ClassicalOrthogonal.Quadratic.add_smul,hp,hx,mul_one] at hh
      exact add_eq_left.mp (by simpa only [add_assoc,mul_one] using hh)
    have hq : Q v = 1 := by
      have hh := he 1
      simp only [one_pow,one_mul] at hh
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh
    have hs : a^2 = a := by
      have hh := he a
      rw [hq,mul_one] at hh
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh
    exact (eq_zero_or_one_of_sq_eq_self hs).elim ha0 ha1
  refine ⟨hproper,?_⟩
  intro H hH
  obtain ⟨g,hg,hgQ⟩ := SetLike.exists_of_lt hH
  obtain ⟨l,hl⟩ := defect Q hp g
  have hl0 : l ≠ 0 := by
    intro he
    apply hgQ
    intro x
    rw [hl,he,LinearMap.zero_apply,zero_pow (by decide),add_zero]
  let R := Q.comp (toLinear g).toLinearMap
  obtain ⟨v,hv,hvg,hne⟩ := exists_distinct_nonzero_values Q R hnd
    (by simp [Matrix.PSp4Three.Vector,Index]) l hl0 hl a ha0 ha1
  let u := g • v
  have hu : Q u ≠ 0 := hvg
  have hfirst : transvection u (Q u)⁻¹ ∈ H := hH.le (reflection_mem Q hp hu)
  have hsecond : transvection u (Q v)⁻¹ ∈ H := by
    rw [←transvection_conjugate]
    exact H.mul_mem (H.mul_mem hg (hH.le (reflection_mem Q hp hv))) (H.inv_mem hg)
  exact eq_top_of_full_root Q hp a ha0 ha1 H hH.le u hu
    (full_root_of_two hF H u (inv_ne_zero hu) (inv_ne_zero hv)
      (fun hh => hne (inv_injective hh).symm) hfirst hsecond)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalMaximality
