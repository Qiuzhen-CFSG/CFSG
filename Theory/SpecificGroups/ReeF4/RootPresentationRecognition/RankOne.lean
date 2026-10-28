module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Rank-one collection from local Gauss relations

If a torus normalizes a root group and an involution normalizes that torus,
the local relation `n u n = a t n b` for each nonidentity root element
collects arbitrary words into `u t` or `u t n v`. Closure induction proves
existence; no normal-form uniqueness, finiteness, or faithfulness is an input.
The identity cell has no redundant right root factor.

This is the rank-one descent step in the Ree presentation argument of
Steinberg, §11, Lemmas 62–64 (`refs/KGroup/GLS3/Chapter2St1.tex`), with the
type V Gauss relation of GLS3 §2.4. It is independent of native matrix
uniqueness, which will be used only after abstract rank-two collection.
-/
@[expose] public section
namespace ReeF4.RootPresentationRecognition.RankOne
open Subgroup
variable {G : Type*} [Group G]

/-- The two restricted Bruhat cells, with no right root factor in the identity cell. -/
def NormalForm (U T : Subgroup G) (n g : G) : Prop :=
  (∃ u ∈ U, ∃ t ∈ T, g = u * t) ∨
  ∃ u ∈ U, ∃ t ∈ T, ∃ v ∈ U, g = u * t * n * v

variable (U T : Subgroup G) (n : G)
  (hTU : T ≤ normalizer (U : Set G))
  (hnT : n ∈ normalizer (T : Set G)) (hn : n * n = 1)
  (hGauss : ∀ u ∈ U, u ≠ 1 →
    ∃ a ∈ U, ∃ t ∈ T, ∃ b ∈ U, n * u * n = a * t * n * b)

include hTU in
private theorem torus_conj {t u : G} (ht : t ∈ T) (hu : u ∈ U) :
    t * u * t⁻¹ ∈ U := (mem_normalizer_iff.mp (hTU ht) u).mp hu

include hnT hn in
private theorem weyl_conj {t : G} (ht : t ∈ T) : n * t * n ∈ T := by
  have hi : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn
  simpa only [hi] using (mem_normalizer_iff.mp hnT t).mp ht

private theorem left_root {u g : G} (hu : u ∈ U) (hg : NormalForm U T n g) :
    NormalForm U T n (u * g) := by
  rcases hg with ⟨a, ha, t, ht, rfl⟩ | ⟨a, ha, t, ht, b, hb, rfl⟩
  · exact Or.inl ⟨u*a, mul_mem hu ha, t, ht, by group⟩
  · exact Or.inr ⟨u*a, mul_mem hu ha, t, ht, b, hb, by group⟩

include hTU in
private theorem left_torus {t g : G} (ht : t ∈ T) (hg : NormalForm U T n g) :
    NormalForm U T n (t * g) := by
  rcases hg with ⟨a, ha, s, hs, rfl⟩ | ⟨a, ha, s, hs, b, hb, rfl⟩
  · exact Or.inl ⟨t*a*t⁻¹, torus_conj U T hTU ht ha,
      t*s, mul_mem ht hs, by group⟩
  · exact Or.inr ⟨t*a*t⁻¹, torus_conj U T hTU ht ha,
      t*s, mul_mem ht hs, b, hb, by group⟩

include hTU hnT hn hGauss in
private theorem left_weyl {g : G} (hg : NormalForm U T n g) :
    NormalForm U T n (n * g) := by
  have hi : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn
  have hnleft (x : G) : n * (n * x) = x := by rw [← mul_assoc, hn, one_mul]
  rcases hg with ⟨a, ha, t, ht, rfl⟩ | ⟨a, ha, t, ht, b, hb, rfl⟩
  · refine Or.inr ⟨1, one_mem _, n*t*n, weyl_conj T n hnT hn ht,
      t⁻¹*a*t, ?_, ?_⟩
    · simpa only [inv_inv] using torus_conj U T hTU (inv_mem ht) ha
    · simp only [one_mul, mul_assoc, hnleft, mul_inv_cancel_left]
  · by_cases ha1 : a = 1
    · subst a
      refine Or.inl ⟨(n*t*n)*b*(n*t*n)⁻¹,
        torus_conj U T hTU (weyl_conj T n hnT hn ht) hb,
        n*t*n, weyl_conj T n hnT hn ht, ?_⟩
      group
    · obtain ⟨c, hc, s, hs, d, hd, he⟩ := hGauss a ha ha1
      let t' := n*t*n
      have ht' : t' ∈ T := weyl_conj T n hnT hn ht
      refine Or.inr ⟨c, hc, s*t, mul_mem hs ht,
        (t'⁻¹*d*t')*b, mul_mem ?_ hb, ?_⟩
      · simpa only [inv_inv] using torus_conj U T hTU (inv_mem ht') hd
      · calc
          n * (a*t*n*b) = (n*a*n)*t'*b := by
            dsimp [t']
            simp only [mul_assoc, hnleft]
          _ = (c*s*n*d)*t'*b := by rw [he]
          _ = c*(s*t)*n*((t'⁻¹*d*t')*b) := by
            dsimp [t']
            simp only [mul_inv_rev, hi]
            simp only [mul_assoc, hnleft, mul_inv_cancel_left]

include hTU hnT hn hGauss in
/-- Local torus and Gauss equations collect every word in the rank-one generators.
No finiteness, simplicity, injectivity, or prior normal form is assumed. -/
theorem normalForm_of_mem {g : G}
    (hg : g ∈ U ⊔ T ⊔ zpowers n) : NormalForm U T n g := by
  have hclosure : U ⊔ T ⊔ zpowers n = closure ((U : Set G) ∪ T ∪ {n}) := by
    rw [closure_union, closure_union, closure_eq, closure_eq, ← zpowers_eq_closure]
  rw [hclosure] at hg
  have step (x : G) (hx : x ∈ (U : Set G) ∪ T ∪ {n})
      (g : G) (hg : NormalForm U T n g) : NormalForm U T n (x*g) := by
    rcases hx with (hx | hx) | hx
    · exact left_root U T n hx hg
    · exact left_torus U T n hTU hx hg
    · rw [Set.mem_singleton_iff.mp hx]
      exact left_weyl U T n hTU hnT hn hGauss hg
  induction hg using Subgroup.closure_induction_left with
  | one => exact Or.inl ⟨1, one_mem _, 1, one_mem _, (mul_one _).symm⟩
  | mul_left x hx y _ ih => exact step x hx y ih
  | inv_mul_cancel x hx y _ ih =>
    apply step x⁻¹ _ y ih
    rcases hx with (hx | hx) | hx
    · exact Or.inl (Or.inl (inv_mem hx))
    · exact Or.inl (Or.inr (inv_mem hx))
    · rw [Set.mem_singleton_iff.mp hx]
      exact Or.inr (Set.mem_singleton_iff.mpr (inv_eq_of_mul_eq_one_right hn))

/-- Every displayed factor belongs to the subgroup generated by the local data. -/
theorem mem_of_normalForm {g : G} (hg : NormalForm U T n g) :
    g ∈ U ⊔ T ⊔ zpowers n := by
  have hU : U ≤ U ⊔ T ⊔ zpowers n := le_sup_left.trans le_sup_left
  have hT : T ≤ U ⊔ T ⊔ zpowers n := le_sup_right.trans le_sup_left
  have hN : n ∈ U ⊔ T ⊔ zpowers n := mem_sup_right (mem_zpowers n)
  rcases hg with ⟨u, hu, t, ht, rfl⟩ | ⟨u, hu, t, ht, v, hv, rfl⟩
  · exact mul_mem (hU hu) (hT ht)
  · exact mul_mem (mul_mem (mul_mem (hU hu) (hT ht)) hN) (hU hv)

include hTU hnT hn hGauss in
/-- The local equations give exact two-cell coverage of the generated subgroup. -/
theorem mem_iff_normalForm {g : G} :
    g ∈ U ⊔ T ⊔ zpowers n ↔ NormalForm U T n g :=
  ⟨normalForm_of_mem U T n hTU hnT hn hGauss, mem_of_normalForm U T n⟩

end ReeF4.RootPresentationRecognition.RankOne
