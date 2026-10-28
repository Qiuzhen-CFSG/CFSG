module
public import Theory.SpecificGroups.SymplecticFour.RootPresentation.TorusCoordinates
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-!
# Bruhat collection for the explicit characteristic-two C₂ presentation

Simple Weyl words transport all eight roots with unit parameters. Factoring
positive U along either simple root, and applying rank-one exchange when
its transported root is negative, proves G = U N U by word induction.
Only the explicit root relations and generation are used; no presentation
faithfulness or unknown-model map is assumed. This includes fields two and four.

Source: Steinberg, Lectures on Chevalley Groups, §§3 and 6, Lemma 37 and
Theorem 8, printed pp.32–33 and 69–71. The word induction adapts the checked
PSL3/UniversalProjection/Faithfulness/Bruhat/Coverage proof to C₂.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.RootPresentation
open PositiveRelations
variable {F E : Type*} [Field F] [Group E] [Finite F] [CharP F 2]

def weylSubgroup (x : Fin 8 → F → E) : Subgroup E :=
  closure {g | ∃ (i : Fin 2) (t : Fˣ), simpleWord x i t = g}

omit [Finite F] [CharP F 2] in
theorem simpleWord_mem_weyl (x : Fin 8 → F → E) (i : Fin 2) (t : Fˣ) :
    simpleWord x i t ∈ weylSubgroup x := subset_closure ⟨i,t,rfl⟩

namespace Relations
variable {x : Fin 8 → F → E} (h : Relations x)
include h

/-- Every product of simple Weyl words transports each root by a unit and
one of the eight literal Weyl permutations. -/
theorem weyl_transport {w : E} (hw : w ∈ weylSubgroup x) :
    ∃ σ ∈ weyl, ∀ r : Fin 8, ∃ c : Fˣ, ∀ a : F,
      MulAut.conj w (x r a) = x (σ r) ((c : F)*a) := by
  have step (w : E)
      (ih : ∃ σ ∈ weyl, ∀ r : Fin 8, ∃ c : Fˣ, ∀ a : F,
        MulAut.conj w (x r a) = x (σ r) ((c : F)*a)) (i : Fin 2) (t : Fˣ) :
      ∃ σ ∈ weyl, ∀ r : Fin 8, ∃ c : Fˣ, ∀ a : F,
        MulAut.conj (w * simpleWord x i t) (x r a) = x (σ r) ((c : F)*a) := by
    obtain ⟨σ,hσ,hs⟩ := ih
    refine ⟨σ * simpleReflection i, weyl.mul_mem hσ ?_, ?_⟩
    · fin_cases i <;> exact subset_closure (by simp [simpleReflection])
    · intro r
      obtain ⟨c,hc⟩ := hs (simpleReflection i r)
      refine ⟨c * simpleFactor i t r, ?_⟩
      intro a
      rw [map_mul, MulAut.mul_apply, h.simpleWord_conj, hc]
      simp only [Units.val_mul, mul_assoc, Equiv.Perm.mul_apply]
  induction hw using Subgroup.closure_induction_right with
  | one => exact ⟨1,weyl.one_mem,fun r => ⟨1,by intro a; simp⟩⟩
  | mul_right w _ y hy ih =>
    obtain ⟨i,t,rfl⟩ := hy
    exact step w ih i t
  | mul_inv_cancel w _ y hy ih =>
    obtain ⟨i,t,rfl⟩ := hy
    rw [h.simpleWord_inv]
    exact step w ih i t

theorem rank_one_exchange (i : Fin 2) (a t : Fˣ) :
    x (simpleRoot i) (a : F) * simpleWord x i t =
      x (oppositeSimpleRoot i) ((a⁻¹ : Fˣ) : F) *
        (simpleWord x i a * simpleWord x i t) *
          x (simpleRoot i) ((t : F)^2 * ((a⁻¹ : Fˣ) : F)) := by
  have hc : MulAut.conj (simpleWord x i a) (x (simpleRoot i) (a : F)) =
      x (oppositeSimpleRoot i) ((a⁻¹ : Fˣ) : F) := by
    rw [h.simpleWord_conj]
    fin_cases i <;> simp [simpleFactor, simpleReflection, simpleRoot, oppositeSimpleRoot,
      shortFactor, longFactor, shortReflection, longReflection, Equiv.Perm.mul_apply,
      Equiv.swap_apply_def, pow_two, mul_assoc]
  have hx : x (simpleRoot i) (a : F) =
      x (oppositeSimpleRoot i) ((a⁻¹ : Fˣ) : F) * simpleWord x i a *
        x (oppositeSimpleRoot i) ((a⁻¹ : Fˣ) : F) := by
    have hm := mul_inv_eq_iff_eq_mul.mp hc
    rw [← hm, simpleWord]
    have sq (r : Fin 8) (u : F) : x r u * x r u = 1 := by
      rw [h.positive.add, CharTwo.add_self_eq_zero, h.positive.zero]
    simp only [mul_assoc]
    rw [← mul_assoc (x (simpleRoot i) (a : F)) (x (simpleRoot i) (a : F)), sq, one_mul,
      sq, mul_one]
  have ht : MulAut.conj (simpleWord x i t)⁻¹
      (x (oppositeSimpleRoot i) ((a⁻¹ : Fˣ) : F)) =
      x (simpleRoot i) ((t : F)^2 * ((a⁻¹ : Fˣ) : F)) := by
    rw [h.simpleWord_inv, h.simpleWord_conj]
    fin_cases i <;> simp [simpleFactor, simpleReflection, simpleRoot, oppositeSimpleRoot,
      shortFactor, longFactor, shortReflection, longReflection, Equiv.Perm.mul_apply,
      Equiv.swap_apply_def]
  calc
    _ = (x (oppositeSimpleRoot i) ((a⁻¹ : Fˣ) : F) * simpleWord x i a *
        x (oppositeSimpleRoot i) ((a⁻¹ : Fˣ) : F)) * simpleWord x i t :=
      congrArg (fun z => z * _) hx
    _ = _ := by rw [← ht]; simp only [MulAut.conj_apply, inv_inv]; group

private def complement (x : Fin 8 → F → E) (i : Fin 2) : Subgroup E :=
  rootSpan x {r | r ∈ ({6,0,4,2} : Set (Fin 8)) ∧ r ≠ simpleRoot i}

private theorem factor_simple (i : Fin 2) {v : E} (hv : v ∈ positiveSubgroup x) :
    ∃ (a : F) (c : complement x i), v = x (simpleRoot i) a * c.val := by
  obtain ⟨b,k,w,a,rfl⟩ := h.positive.positive_normal_form v hv
  fin_cases i
  · refine ⟨b,⟨x 0 k * x 4 w * x 2 a,?_⟩,by simp [product,simpleRoot,mul_assoc]⟩
    exact mul_mem (mul_mem (root_mem_span x (by simp [simpleRoot]) k)
      (root_mem_span x (by simp [simpleRoot]) w)) (root_mem_span x (by simp [simpleRoot]) a)
  · have he : complement x 1 = rootSpan x {6,0,4} := by
      change rootSpan x _ = rootSpan x _
      apply congrArg (rootSpan x)
      ext r
      fin_cases r <;> decide
    have hc : x 6 b * x 0 k * x 4 w ∈ rootSpan x {6,0,4} :=
      mul_mem (mul_mem (root_mem_span x (by simp) b) (root_mem_span x (by simp) k))
        (root_mem_span x (by simp) w)
    refine ⟨a,⟨MulAut.conj (x 2 a) (x 6 b * x 0 k * x 4 w),?_⟩,?_⟩
    · change MulAut.conj (x 2 a) (x 6 b * x 0 k * x 4 w) ∈ complement x 1
      rw [he]
      exact (mem_normalizer_iff.mp (h.positive.long_normalizes a) _).mp hc
    · change product x b k w a = x 2 a * (x 2 a * (x 6 b * x 0 k * x 4 w) * (x 2 a)⁻¹)
      have hs : x 2 a * x 2 a = 1 := by
        rw [h.positive.add, CharTwo.add_self_eq_zero, h.positive.zero]
      rw [mul_assoc (x 2 a) (x 6 b * x 0 k * x 4 w), ← mul_assoc, hs, one_mul,
        h.positive.inv]
      rfl

private theorem simple_conj_complement (i : Fin 2) (t : Fˣ) {v : E}
    (hv : v ∈ complement x i) : MulAut.conj (simpleWord x i t) v ∈ positiveSubgroup x := by
  induction hv using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨r,⟨hr,hne⟩,a,rfl⟩ := hg
    rw [h.simpleWord_conj]
    apply root_mem_span
    revert hr hne
    fin_cases i <;> fin_cases r <;> decide
  | one => simpa only [map_one] using (positiveSubgroup x).one_mem
  | mul g k _ _ hg hk => simpa only [map_mul] using mul_mem hg hk
  | inv g _ hg => simpa only [map_inv] using inv_mem hg

private def collectionGenerators (x : Fin 8 → F → E) : Set E :=
  {g | ∃ r ∈ ({6,0,4,2} : Set (Fin 8)), ∃ a, x r a = g} ∪
  {g | ∃ (i : Fin 2) (t : Fˣ), simpleWord x i t = g}

private theorem closure_collectionGenerators
    (hgen : closure {g | ∃ r t, x r t = g} = ⊤) :
    closure (collectionGenerators x) = ⊤ := by
  let H := closure (collectionGenerators x)
  have hp (r : Fin 8) (hr : r ∈ ({6,0,4,2} : Set (Fin 8))) (t : F) : x r t ∈ H :=
    subset_closure (Or.inl ⟨r,hr,t,rfl⟩)
  have hw (i : Fin 2) : simpleWord x i (1 : Fˣ) ∈ H := subset_closure (Or.inr ⟨i,1,rfl⟩)
  have hs (r : Fin 8) (t : F) (hr : x r t ∈ H) : x (shortReflection r) t ∈ H := by
    have he := h.shortWord_one_conj r t
    rw [← he]
    have hw0 : shortWord x 1 ∈ H := by simpa [simpleWord,shortWord,simpleRoot,oppositeSimpleRoot] using hw 0
    exact mul_mem (mul_mem hw0 hr) (inv_mem hw0)
  have hl (r : Fin 8) (t : F) (hr : x r t ∈ H) : x (longReflection r) t ∈ H := by
    rw [← h.longWord_one_conj r t]
    have hw1 : longWord x 1 ∈ H := by simpa [simpleWord,longWord,simpleRoot,oppositeSimpleRoot] using hw 1
    exact mul_mem (mul_mem hw1 hr) (inv_mem hw1)
  apply top_unique
  rw [← hgen]
  apply (closure_le _).mpr
  rintro g ⟨r,t,rfl⟩
  fin_cases r
  · exact hp 0 (by simp) t
  · exact hs 3 t (hl 2 t (hp 2 (by simp) t))
  · exact hp 2 (by simp) t
  · exact hl 2 t (hp 2 (by simp) t)
  · exact hp 4 (by simp) t
  · exact hl 7 t (hs 6 t (hp 6 (by simp) t))
  · exact hp 6 (by simp) t
  · exact hs 6 t (hp 6 (by simp) t)

private def InBruhat (x : Fin 8 → F → E) (g : E) : Prop :=
  ∃ (u : positiveSubgroup x) (w : weylSubgroup x) (v : positiveSubgroup x),
    g = u.val * w.val * v.val

omit [Finite F] [CharP F 2] h in
private theorem inBruhat_mul_positive {g t : E}
    (hg : InBruhat x g) (ht : t ∈ positiveSubgroup x) : InBruhat x (g*t) := by
  obtain ⟨u,w,v,rfl⟩ := hg
  exact ⟨u,w,⟨v.val*t,mul_mem v.property ht⟩,mul_assoc _ _ _⟩

private theorem inBruhat_mul_simple {g : E} (hg : InBruhat x g) (i : Fin 2) (t : Fˣ) :
    InBruhat x (g * simpleWord x i t) := by
  obtain ⟨u,w,v,hg⟩ := hg
  obtain ⟨a,c,hc⟩ := h.factor_simple i v.property
  let s : weylSubgroup x := ⟨simpleWord x i t,simpleWord_mem_weyl x i t⟩
  let d : positiveSubgroup x := ⟨MulAut.conj s.val⁻¹ c.val,by
    change MulAut.conj (simpleWord x i t)⁻¹ c.val ∈ _
    rw [h.simpleWord_inv]
    exact h.simple_conj_complement i t c.property⟩
  have hcs : c.val * s.val = s.val * d.val := by dsimp [d]; group
  have hred : g * s.val = u.val * (w.val * x (simpleRoot i) a * s.val) * d.val := by
    rw [hg,hc]
    simp only [mul_assoc,hcs]
  change InBruhat x (g*s.val)
  by_cases ha : a = 0
  · refine ⟨u,w*s,d,?_⟩
    simpa only [ha,h.positive.zero,mul_one,Subgroup.coe_mul] using hred
  obtain ⟨σ,hσ,hs⟩ := h.weyl_transport w.property
  obtain ⟨b,hb⟩ := hs (simpleRoot i)
  by_cases hp : σ (simpleRoot i) ∈ ({6,0,4,2} : Set (Fin 8))
  · let z : positiveSubgroup x := ⟨x (σ (simpleRoot i)) ((b : F)*a),root_mem_span x hp _⟩
    have hz : w.val * x (simpleRoot i) a = z.val * w.val := mul_inv_eq_iff_eq_mul.mp (hb a)
    refine ⟨u*z,w*s,d,?_⟩
    rw [hred,hz]
    simp only [Subgroup.coe_mul,mul_assoc]
  · have hq : σ (oppositeSimpleRoot i) ∈ ({6,0,4,2} : Set (Fin 8)) := by
      rcases weyl_cases σ hσ with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        fin_cases i <;> (revert hp; decide)
    let aU : Fˣ := Units.mk0 a ha
    obtain ⟨b',hb'⟩ := hs (oppositeSimpleRoot i)
    let z : positiveSubgroup x := ⟨x (σ (oppositeSimpleRoot i)) ((b' : F)*(aU⁻¹ : Fˣ)),
      root_mem_span x hq _⟩
    let n : weylSubgroup x := ⟨simpleWord x i aU,simpleWord_mem_weyl x i aU⟩
    let v' : positiveSubgroup x := ⟨x (simpleRoot i) ((t : F)^2 * (aU⁻¹ : Fˣ)),
      root_mem_span x (by fin_cases i <;> simp [simpleRoot]) _⟩
    have hz : w.val * x (oppositeSimpleRoot i) ((aU⁻¹ : Fˣ) : F) = z.val * w.val :=
      mul_inv_eq_iff_eq_mul.mp (hb' _)
    have hex : x (simpleRoot i) a * s.val =
        x (oppositeSimpleRoot i) ((aU⁻¹ : Fˣ) : F) * (n.val*s.val) * v'.val :=
      h.rank_one_exchange i aU t
    refine ⟨u*z,w*n*s,v'*d,?_⟩
    rw [hred,mul_assoc w.val,hex]
    rw [← mul_assoc w.val,← mul_assoc w.val,hz]
    simp only [Subgroup.coe_mul,mul_assoc]

/-- The explicit eight-root relations and generation imply the full UNU
Bruhat coverage, without assuming global matrix faithfulness. -/
theorem bruhat (hgen : closure {g | ∃ r t, x r t = g} = ⊤) (g : E) :
    ∃ (u : positiveSubgroup x) (w : weylSubgroup x) (v : positiveSubgroup x),
      g = u.val * w.val * v.val := by
  have hg : g ∈ closure (collectionGenerators x) := by rw [h.closure_collectionGenerators hgen]; trivial
  change InBruhat x g
  have step (g y : E) (hg : InBruhat x g) (hy : y ∈ collectionGenerators x) :
      InBruhat x (g*y) := by
    rcases hy with ⟨r,hr,a,rfl⟩ | ⟨i,t,rfl⟩
    · exact inBruhat_mul_positive hg (root_mem_span x hr a)
    · exact h.inBruhat_mul_simple hg i t
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨1,1,1,by simp⟩
  | mul_right g _ y hy ih => exact step g y ih hy
  | mul_inv_cancel g _ y hy ih =>
    rcases hy with ⟨r,hr,a,rfl⟩ | ⟨i,t,rfl⟩
    · rw [h.positive.inv]
      exact inBruhat_mul_positive ih (root_mem_span x hr a)
    · rw [h.simpleWord_inv]
      exact h.inBruhat_mul_simple ih i t
end Relations
end Theory.SpecificGroups.SymplecticFour.RootPresentation
