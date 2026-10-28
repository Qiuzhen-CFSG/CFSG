module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Models
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Chief series under a quotient with fixed kernel

Map every term of a complete invariant chief series through an intertwiner.
The image of each cover is a cover or an equality. On a chief section the
intersection with the fixed kernel either vanishes or fills the section;
therefore the section is noncentral exactly when its image is noncentral.
Deleting repeated terms constructs a complete target chief series and preserves
the number of genuinely nontrivial section actions.

This proves the transfer needed between Aschbacher–Smith 13.7.6(3a), printed
pp.938–939, and 13.8.5(2a), printed p.947 (1 March 2004 manuscript). The argument
works for any pointwise fixed kernel, without a dimension restriction.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.ChiefQuotient

private theorem compress_chain {α β : Type*} [PartialOrder α] [PartialOrder β]
    (f : α → β) (w : β → β → ℕ) (hw : ∀ a, w a a = 0)
    (hf : ∀ {a b}, a ⋖ b → f a ⩿ f b) :
    ∀ {n : ℕ} (c : Fin (n + 1) → α), (∀ i : Fin n, c i.castSucc ⋖ c i.succ) →
      ∃ m : ℕ, ∃ d : Fin (m + 1) → β,
        d 0 = f (c 0) ∧ d (Fin.last m) = f (c (Fin.last n)) ∧
        (∀ i : Fin m, d i.castSucc ⋖ d i.succ) ∧
        (∑ i : Fin m, w (d i.castSucc) (d i.succ)) =
          ∑ i : Fin n, w (f (c i.castSucc)) (f (c i.succ)) := by
  intro n
  induction n with
  | zero =>
    intro c hc
    exact ⟨0, fun _ => f (c 0), rfl, rfl, Fin.elim0, by simp⟩
  | succ n ih =>
    intro c hc
    obtain ⟨m, d, hd0, hdl, hdc, hds⟩ :=
      ih (fun i => c i.succ) (fun i => hc i.succ)
    rcases (hf (hc 0)).eq_or_covBy with he | he
    · change f (c 0) = f (c (Fin.succ 0)) at he
      refine ⟨m, d, hd0.trans he.symm, hdl, hdc, ?_⟩
      rw [Fin.sum_univ_succ]
      simpa only [Fin.castSucc_zero, he, hw, zero_add, ← Fin.succ_castSucc] using hds
    · refine ⟨m + 1, Fin.cons (f (c 0)) d, by simp, ?_, ?_, ?_⟩
      · simpa using hdl
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one,
            Fin.cons_one, hd0] using he
        · simpa only [← Fin.succ_castSucc, Fin.cons_succ] using hdc j
      · rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
        simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hd0,
          ← Fin.succ_castSucc] using congrArg (w (f (c 0)) (f (c (Fin.succ 0))) + ·) hds

variable {J E F : Type*} [Group J] [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup F] [Module (ZMod 2) F]
    {τ : Representation (ZMod 2) J E} {σ : Representation (ZMod 2) J F}

private def image (p : τ.IntertwiningMap σ) (A : Subrepresentation τ) :
    Subrepresentation σ where
  toSubmodule := A.toSubmodule.map p.toLinearMap
  apply_mem_toSubmodule g := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨τ g a, A.apply_mem_toSubmodule g ha, ?_⟩
    exact IntertwiningMap.isIntertwining τ σ p g a

private def preimage (p : τ.IntertwiningMap σ) (A : Subrepresentation σ) :
    Subrepresentation τ where
  toSubmodule := A.toSubmodule.comap p.toLinearMap
  apply_mem_toSubmodule g := by
    intro a ha
    change p (τ g a) ∈ A
    rw [IntertwiningMap.isIntertwining τ σ p]
    exact A.apply_mem_toSubmodule g ha

private theorem image_mono (p : τ.IntertwiningMap σ) : Monotone (image p) :=
  fun _ _ h => Submodule.map_mono h

private theorem image_wcovBy (p : τ.IntertwiningMap σ) {A B : Subrepresentation τ}
    (h : A ⋖ B) : image p A ⩿ image p B := by
  apply wcovBy_of_eq_or_eq (image_mono p h.le)
  intro D hAD hDB
  let C := B ⊓ preimage p D
  have hAC : A ≤ C := fun x hx => ⟨h.le hx, hAD ⟨x, hx, rfl⟩⟩
  have hCD : image p C = D := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hDB hy
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  rcases h.eq_or_eq hAC inf_le_left with he | he
  · left
    rw [← hCD, he]
  · right
    rw [← hCD, he]

private def noncentral (ρ : Representation (ZMod 2) J E) (A B : Subrepresentation ρ) : Prop :=
  ∃ g : J, ∃ v, sectionRepresentation ρ A B g v ≠ v

private theorem not_noncentral_iff (A B : Subrepresentation τ) :
    ¬ noncentral τ A B ↔ ∀ g x, x ∈ B → τ g x - x ∈ A := by
  simp only [noncentral, not_exists, not_not]
  exact forall_congr' fun g => sectionRepresentation_trivial_iff τ A B g

private theorem noncentral_image_iff (p : τ.IntertwiningMap σ)
    (hk : ∀ g x, p x = 0 → τ g x = x) {A B : Subrepresentation τ}
    (h : A ⋖ B) : noncentral σ (image p A) (image p B) ↔ noncentral τ A B := by
  apply not_iff_not.mp
  rw [not_noncentral_iff, not_noncentral_iff]
  constructor
  · intro ht
    let C := A ⊔ (B ⊓ p.ker)
    have hCB : C ≤ B := sup_le h.le inf_le_left
    rcases h.eq_or_eq le_sup_left hCB with he | he
    · intro g x hx
      obtain ⟨a, ha, hpa⟩ := ht g (p x) ⟨x, hx, rfl⟩
      change p a = σ g (p x) - p x at hpa
      have hd : τ g x - x - a ∈ B ⊓ p.ker := by
        refine ⟨B.toSubmodule.sub_mem
          (B.toSubmodule.sub_mem (B.apply_mem_toSubmodule g hx) hx) (h.le ha), ?_⟩
        change p (τ g x - x - a) = 0
        simp only [map_sub, IntertwiningMap.isIntertwining τ σ p, hpa, sub_self]
      have hdA : τ g x - x - a ∈ A := by
        rw [← he]
        exact (show B ⊓ p.ker ≤ A ⊔ (B ⊓ p.ker) from le_sup_right) hd
      change τ g x - x ∈ A.toSubmodule
      simpa only [sub_add_cancel] using A.toSubmodule.add_mem hdA ha
    · intro g x hx
      have hxC : x ∈ C := by change x ∈ A ⊔ (B ⊓ p.ker); rw [he]; exact hx
      obtain ⟨a, ha, k, hkB, rfl⟩ := Submodule.mem_sup.mp hxC
      have heq := hk g k hkB.2
      change τ g (a + k) - (a + k) ∈ A.toSubmodule
      simpa only [map_add, heq, add_sub_add_right_eq_sub] using
        A.toSubmodule.sub_mem (A.apply_mem_toSubmodule g ha) ha
  · intro ht g y hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨τ g x - x, ht g x hx, ?_⟩
    change p (τ g x - x) = σ g (p x) - p x
    simp only [map_sub, IntertwiningMap.isIntertwining τ σ p]

private noncomputable def weight (ρ : Representation (ZMod 2) J E)
    (A B : Subrepresentation ρ) : ℕ := by
  classical
  exact if noncentral ρ A B then 1 else 0

private theorem weight_self (A : Subrepresentation τ) : weight τ A A = 0 := by
  classical
  have h : ¬ noncentral τ A A := not_noncentral_iff A A |>.mpr
    (fun g x hx => A.toSubmodule.sub_mem (A.apply_mem_toSubmodule g hx) hx)
  simp [weight, h]

private theorem sum_weight {n : ℕ} (c : Fin (n + 1) → Subrepresentation τ) :
    (∑ i : Fin n, weight τ (c i.castSucc) (c i.succ)) =
      Nat.card {i : Fin n // noncentral τ (c i.castSucc) (c i.succ)} := by
  classical
  simp only [weight, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole,
    Nat.cast_id]

/-- A surjective intertwiner with pointwise fixed kernel preserves the exact
number of noncentral chief factors, by mapping and compressing a complete chief series. -/
theorem twoNoncentralChiefFactors_of_surjective_fixed_kernel
    (p : τ.IntertwiningMap σ) (hp : Function.Surjective p)
    (hk : ∀ g x, p x = 0 → τ g x = x)
    (hτ : CriticalGeometry.Reorientation.TwoNoncentralChiefFactors τ) :
    CriticalGeometry.Reorientation.TwoNoncentralChiefFactors σ := by
  classical
  obtain ⟨n, c, hc0, hcl, hcc, hcn⟩ := hτ
  obtain ⟨m, d, hd0, hdl, hdc, hds⟩ :=
    compress_chain (image p) (weight σ) weight_self (image_wcovBy p) c hcc
  refine ⟨m, d, ?_, ?_, hdc, ?_⟩
  · rw [hd0, hc0]
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.map_bot _
  · rw [hdl, hcl]
    apply Subrepresentation.toSubmodule_injective
    exact (Submodule.map_top _).trans (LinearMap.range_eq_top.mpr hp)
  · change Nat.card {i : Fin m // noncentral σ (d i.castSucc) (d i.succ)} = 2
    rw [← sum_weight, hds]
    have hw : ∀ i : Fin n, weight σ (image p (c i.castSucc)) (image p (c i.succ)) =
        weight τ (c i.castSucc) (c i.succ) := by
      intro i
      simp only [weight, noncentral_image_iff p hk (hcc i)]
    simp_rw [hw]
    rw [sum_weight]
    exact hcn

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.ChiefQuotient

end
