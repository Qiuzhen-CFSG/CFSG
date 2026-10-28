module
public import Theory.SpecificGroups.SymplecticFour.RootPresentation.Bruhat
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-!
# Eight-word collection in the C₂ Weyl subgroup

The root conjugation equations give the literal four-term braid relation
for the parameter-one simple lifts. Their action on coroot words preserves
the proved two-dimensional torus. Induction then collects every Weyl word
into a torus element followed by one of eight fixed representatives.
This takes place in the abstract presentation, before evaluation faithfulness.

Source: Steinberg, Lectures on Chevalley Groups, §§3 and 6, Lemmas 22 and
37–38, printed pp.32–33 and 69–71.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.RootPresentation
variable {F E : Type*} [Field F] [Group E] [Finite F] [CharP F 2]

def weylRepresentative (x : Fin 8 → F → E) (k : Fin 8) : E :=
  let a := simpleWord x 0 1
  let b := simpleWord x 1 1
  ![1,a,b,a*b,b*a,a*b*a,b*a*b,a*b*a*b] k

namespace Relations
variable {x : Fin 8 → F → E} (h : Relations x)
include h

private theorem torus_conj_word (i j : Fin 2) (s t : Fˣ) :
    MulAut.conj (torusWord x i s) (simpleWord x j t) =
      simpleWord x j (t * simpleFactor i s (simpleReflection i (simpleRoot j))) := by
  have ho : simpleFactor i s (simpleReflection i (oppositeSimpleRoot j)) =
      (simpleFactor i s (simpleReflection i (simpleRoot j)))⁻¹ := by
    fin_cases i <;> fin_cases j <;>
      simp [simpleFactor,simpleReflection,oppositeSimpleRoot,simpleRoot,shortFactor,longFactor,
        shortReflection,longReflection,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
  simp only [simpleWord,map_mul,h.torusWord_conj,ho,Units.val_mul,mul_inv_rev,
    Units.val_inv_eq_inv_val]
  congr 2 <;> simp [mul_comm]

/-- The simple Weyl action preserves the actual two-coroot torus. -/
theorem simpleWord_one_conj_torus (i j : Fin 2) (s : Fˣ) :
    MulAut.conj (simpleWord x j 1) (torusWord x i s) =
      (torusWord x j (simpleFactor i s (simpleReflection i (simpleRoot j))))⁻¹ *
        torusWord x i s := by
  have he : torusWord x i s *
      (MulAut.conj (simpleWord x j 1) (torusWord x i s))⁻¹ =
      torusWord x j (simpleFactor i s (simpleReflection i (simpleRoot j))) := by
    calc
      _ = MulAut.conj (torusWord x i s) (simpleWord x j 1) * (simpleWord x j 1)⁻¹ := by
        simp [MulAut.conj_apply,mul_assoc]
      _ = _ := by rw [h.torus_conj_word,one_mul,h.simpleWord_inv]; rfl
  calc
    _ = (torusWord x i s *
        (MulAut.conj (simpleWord x j 1) (torusWord x i s))⁻¹)⁻¹ * torusWord x i s := by group
    _ = _ := by rw [he]

private theorem coroot_mem (i : Fin 2) (s : Fˣ) : torusWord x i s ∈ h.torusPairHom.range := by
  rw [h.torusPairHom_range]
  fin_cases i
  · exact (show (h.torusHom 0).range ≤ (h.torusHom 0).range ⊔ (h.torusHom 1).range from le_sup_left) (show torusWord x 0 s ∈ (h.torusHom 0).range from ⟨s,rfl⟩)
  · exact (show (h.torusHom 1).range ≤ (h.torusHom 0).range ⊔ (h.torusHom 1).range from le_sup_right) (show torusWord x 1 s ∈ (h.torusHom 1).range from ⟨s,rfl⟩)

private theorem simple_conj_torus_mem (j : Fin 2) {g : E} (hg : g ∈ h.torusPairHom.range) :
    MulAut.conj (simpleWord x j 1) g ∈ h.torusPairHom.range := by
  obtain ⟨⟨s,t⟩,rfl⟩ := hg
  rw [h.torusPairHom_apply,map_mul,h.simpleWord_one_conj_torus,h.simpleWord_one_conj_torus]
  exact mul_mem (mul_mem (inv_mem (h.coroot_mem j _)) (h.coroot_mem 0 _))
    (mul_mem (inv_mem (h.coroot_mem j _)) (h.coroot_mem 1 _))

/-- In characteristic two the simple lifts satisfy the literal C₂ braid. -/
theorem simpleWord_braid :
    simpleWord x 0 1 * simpleWord x 1 1 * simpleWord x 0 1 * simpleWord x 1 1 =
      simpleWord x 1 1 * simpleWord x 0 1 * simpleWord x 1 1 * simpleWord x 0 1 := by
  let a := simpleWord x 0 (1 : Fˣ)
  let b := simpleWord x 1 (1 : Fˣ)
  have ha : a⁻¹ = a := h.simpleWord_inv 0 1
  have hb : b⁻¹ = b := h.simpleWord_inv 1 1
  have hc : MulAut.conj a b = x 0 1 * x 1 1 * x 0 1 := by
    change MulAut.conj (simpleWord x 0 1) (x 2 1 * x 3 1 * x 2 1) = _
    simp only [map_mul,h.simpleWord_conj]
    simp [simpleFactor,simpleReflection,shortFactor,shortReflection,
      Equiv.Perm.mul_apply,Equiv.swap_apply_def]
  have hd : MulAut.conj b (MulAut.conj a b) = MulAut.conj a b := by
    rw [hc]
    change MulAut.conj (simpleWord x 1 1) (x 0 1 * x 1 1 * x 0 1) = _
    simp only [map_mul,h.simpleWord_conj]
    simp [simpleFactor,simpleReflection,longFactor,longReflection,
      Equiv.Perm.mul_apply,Equiv.swap_apply_def]
  have hcomm := mul_inv_eq_iff_eq_mul.mp hd
  simp only [MulAut.conj_apply,ha] at hcomm
  change a*b*a*b = b*a*b*a
  simpa only [mul_assoc] using hcomm.symm

omit [Finite F] [CharP F 2] h in
private theorem eight_words_step {G : Type*} [Group G] (a b : G)
    (ha : a⁻¹ = a) (hb : b⁻¹ = b) (hab : a*b*a*b = b*a*b*a) (i : Fin 2) (k : Fin 8) :
    ∃ l : Fin 8, ![a,b] i * ![1,a,b,a*b,b*a,a*b*a,b*a*b,a*b*a*b] k =
      ![1,a,b,a*b,b*a,a*b*a,b*a*b,a*b*a*b] l := by
  have aa : a*a = 1 := by simpa only [ha] using inv_mul_cancel a
  have bb : b*b = 1 := by simpa only [hb] using inv_mul_cancel b
  fin_cases i <;> fin_cases k
  · exact ⟨1,mul_one a⟩
  · exact ⟨0,aa⟩
  · exact ⟨3,rfl⟩
  · exact ⟨2,by change a*(a*b)=b; rw [← mul_assoc,aa,one_mul]⟩
  · exact ⟨5,(mul_assoc _ _ _).symm⟩
  · exact ⟨4,by change a*(a*b*a)=b*a; rw [← mul_assoc,← mul_assoc,aa,one_mul]⟩
  · exact ⟨7,by change a*(b*a*b)=a*b*a*b; simp only [mul_assoc]⟩
  · exact ⟨6,by change a*(a*b*a*b)=b*a*b; rw [← mul_assoc,← mul_assoc,← mul_assoc,aa,one_mul]⟩
  · exact ⟨2,mul_one b⟩
  · exact ⟨4,rfl⟩
  · exact ⟨0,bb⟩
  · exact ⟨6,(mul_assoc _ _ _).symm⟩
  · exact ⟨1,by change b*(b*a)=a; rw [← mul_assoc,bb,one_mul]⟩
  · exact ⟨7,by change b*(a*b*a)=a*b*a*b; simpa only [mul_assoc] using hab.symm⟩
  · exact ⟨3,by change b*(b*a*b)=a*b; rw [← mul_assoc,← mul_assoc,bb,one_mul]⟩
  · exact ⟨5,by change b*(a*b*a*b)=a*b*a; rw [hab,← mul_assoc,← mul_assoc,← mul_assoc,bb,one_mul]⟩

/-- Every word in the Weyl subgroup is a literal two-coroot torus element
followed by one of eight fixed representatives. -/
theorem weyl_normal_form {g : E} (hg : g ∈ weylSubgroup x) :
    ∃ (p : Fˣ × Fˣ) (k : Fin 8), g = h.torusPairHom p * weylRepresentative x k := by
  let T := h.torusPairHom.range
  have step (i : Fin 2) (t : Fˣ) (g : E)
      (hg : ∃ p k, g = h.torusPairHom p * weylRepresentative x k) :
      ∃ p k, simpleWord x i t * g = h.torusPairHom p * weylRepresentative x k := by
    obtain ⟨p,k,rfl⟩ := hg
    have hc : MulAut.conj (simpleWord x i 1) (h.torusPairHom p) ∈ T :=
      h.simple_conj_torus_mem i ⟨p,rfl⟩
    obtain ⟨q,hq⟩ := T.mul_mem (h.coroot_mem i t) hc
    obtain ⟨l,hl⟩ := eight_words_step (simpleWord x 0 (1 : Fˣ)) (simpleWord x 1 1)
      (h.simpleWord_inv 0 1) (h.simpleWord_inv 1 1) h.simpleWord_braid i k
    have hl' : simpleWord x i 1 * weylRepresentative x k = weylRepresentative x l := by
      simpa only [weylRepresentative,show ![simpleWord x 0 1,simpleWord x 1 1] i = simpleWord x i 1 from by fin_cases i <;> rfl] using hl
    refine ⟨q,l,?_⟩
    rw [hq,← hl']
    simp only [torusWord,MulAut.conj_apply]
    have hs : simpleWord x i 1 * simpleWord x i 1 = 1 := by
      simpa only [h.simpleWord_inv] using inv_mul_cancel (simpleWord x i 1)
    simp only [mul_assoc,inv_mul_cancel_left,← mul_assoc (simpleWord x i 1) (simpleWord x i 1),hs,one_mul]
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨1,0,by simp [weylRepresentative]⟩
  | mul_left y hy g _ ih =>
    obtain ⟨i,t,rfl⟩ := hy
    exact step i t g ih
  | inv_mul_cancel y hy g _ ih =>
    obtain ⟨i,t,rfl⟩ := hy
    rw [h.simpleWord_inv]
    exact step i t g ih
end Relations
end Theory.SpecificGroups.SymplecticFour.RootPresentation
