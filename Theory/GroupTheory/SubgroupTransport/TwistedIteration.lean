module
public import Theory.GroupTheory.SubgroupTransport.Restriction

/-!
# Comparing a conjugacy twist with its underlying automorphism

On an ambient-normal layer C centralized modulo V, a conjugacy twist differs
from the underlying subgroup automorphism only by V. Iteration accumulates
its actual shifted error subgroups. Applying this comparison to the two
central layers N/V and Q/M proves the twice-power-twist escape in source 6.4
from the original diagram shift and interval containments.

No automorphism extension of the partial isomorphism S→T is assumed. Every
shift uses the literal subgroup transport, and the path stays in its domain
exactly where the supplied interval containments say it does.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 6.4, pp.53–54.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory.SubgroupTransport
variable {H : Type*} [Group H]

private theorem conj_le_sup (g : H) (A C E : Subgroup H) (hAC : A ≤ C)
    (hcomm : ⁅(⊤ : Subgroup H), C⁆ ≤ E) :
    A.map (MulAut.conj g).toMonoidHom ≤ A ⊔ E := by
  rintro _ ⟨a, ha, rfl⟩
  change MulAut.conj g a ∈ A ⊔ E
  rw [conj_eq_commutatorElement_mul]
  exact (A ⊔ E).mul_mem ((show E ≤ A ⊔ E from le_sup_right) (hcomm
    (commutator_mem_commutator (mem_top g) (hAC ha)))) ((show A ≤ A ⊔ E from le_sup_left) ha)

/-- A conjugacy twist and its underlying automorphism agree modulo the
commutator error on a normal layer. -/
theorem twisted_image_comparison
    (S : Subgroup H) (α : MulAut S) (g : H)
    (A C E : Subgroup H) [C.Normal]
    (hC : image (α.trans ((MulAut.conj g).subgroupMap S)) A ≤ C)
    (hcomm : ⁅(⊤ : Subgroup H), C⁆ ≤ E) :
    image α A ≤ image (α.trans ((MulAut.conj g).subgroupMap S)) A ⊔ E ∧
    image (α.trans ((MulAut.conj g).subgroupMap S)) A ≤ image α A ⊔ E := by
  have he : image (α.trans ((MulAut.conj g).subgroupMap S)) A =
      (image α A).map (MulAut.conj g).toMonoidHom := by
    rw [image, image, map_map]
    rfl
  have hinv : (image (α.trans ((MulAut.conj g).subgroupMap S)) A).map
      (MulAut.conj g⁻¹).toMonoidHom = image α A := by
    rw [he, map_map]
    have hh : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id H := by ext x; simp [mul_assoc]
    rw [hh, Subgroup.map_id]
  have hAC : image α A ≤ C := by
    rw [← hinv]
    exact (map_mono hC).trans_eq (Normal.map_conj_eq C g⁻¹)
  constructor
  · rw [← hinv]
    exact conj_le_sup g⁻¹ _ C E hC hcomm
  · rw [he]
    exact conj_le_sup g _ C E hAC hcomm

/-- Iterating a conjugacy twist accumulates only the specified shifted error
subgroups. Both inclusions are retained, so later escape is preserved. -/
theorem iterate_twisted_comparison
    (S : Subgroup H) (α : MulAut S) (g : H)
    (A C V : Subgroup H) [C.Normal] (hCS : C ≤ S)
    (hcomm : ⁅(⊤ : Subgroup H), C⁆ ≤ V)
    (E : ℕ → Subgroup H) (hEzero : E 0 = ⊥)
    (n : ℕ)
    (hE : ∀ i ≤ n, E i ≤ C)
    (hstep : ∀ i < n,
      image (α.trans ((MulAut.conj g).subgroupMap S)) (E i) ⊔ V ≤ E (i + 1))
    (hA : ∀ i ≤ n, (image (α.trans ((MulAut.conj g).subgroupMap S)))^[i] A ≤ C) :
    (image α)^[n] A ≤
      (image (α.trans ((MulAut.conj g).subgroupMap S)))^[n] A ⊔ E n ∧
    (image (α.trans ((MulAut.conj g).subgroupMap S)))^[n] A ≤
      (image α)^[n] A ⊔ E n := by
  let φ := α.trans ((MulAut.conj g).subgroupMap S)
  have hαS : ∀ i, (image α)^[i] A ≤ S := by
    intro i
    cases i with
    | zero => exact (hA 0 (Nat.zero_le n)).trans hCS
    | succ i => rw [Function.iterate_succ_apply']; exact image_le _ _
  induction n with
  | zero => simp [hEzero]
  | succ n ih =>
    have hh := ih (fun i hi => hE i (hi.trans (Nat.le_succ n)))
      (fun i hi => hstep i (hi.trans (Nat.lt_succ_self n)))
      (fun i hi => hA i (hi.trans (Nat.le_succ n)))
    have hstepn := hstep n (Nat.lt_succ_self n)
    have hφ : image φ ((image α)^[n] A) ≤ C := by
      have hm := image_mono φ hh.1
      rw [image_sup φ _ _ ((hA n (Nat.le_succ n)).trans hCS)
        ((hE n (Nat.le_succ n)).trans hCS)] at hm
      exact hm.trans (sup_le (by simpa [φ, Function.iterate_succ_apply'] using hA (n+1) le_rfl)
        ((le_sup_left.trans hstepn).trans (hE (n+1) le_rfl)))
    obtain ⟨hforward,hback⟩ := twisted_image_comparison S α g
      ((image α)^[n] A) C V hφ hcomm
    have hEV : V ≤ E (n+1) := (le_sup_right : V ≤ image φ (E n) ⊔ V).trans hstepn
    have hEE : image φ (E n) ≤ E (n+1) := (le_sup_left : image φ (E n) ≤ image φ (E n) ⊔ V).trans hstepn
    have hφA := image_mono φ hh.1
    rw [image_sup φ _ _ ((hA n (Nat.le_succ n)).trans hCS)
      ((hE n (Nat.le_succ n)).trans hCS)] at hφA
    have hφB := image_mono φ hh.2
    rw [image_sup φ _ _ (hαS n) ((hE n (Nat.le_succ n)).trans hCS)] at hφB
    change (image α)^[n+1] A ≤ (image φ)^[n+1] A ⊔ E (n+1) ∧
      (image φ)^[n+1] A ≤ (image α)^[n+1] A ⊔ E (n+1)
    simp only [Function.iterate_succ_apply']
    constructor
    · apply hforward.trans
      apply sup_le
      · exact hφA.trans (sup_le_sup_left hEE _)
      · exact hEV.trans le_sup_right
    · apply hφB.trans
      apply sup_le
      · exact hback.trans (sup_le_sup_left hEV _)
      · exact hEE.trans le_sup_right


end Theory.GroupTheory.SubgroupTransport

namespace Theory.GroupTheory.SubgroupTransport
open Subgroup
variable {H : Type*} [Group H] {S T : Subgroup H}

private theorem image_trans_aut (α : MulAut S) (φ : S ≃* T) (A : Subgroup H) :
    image φ (image α A) = image (α.trans φ) A := by
  rw [image, image_subgroupOf, map_map]
  rfl

private theorem image_pow_aut (α : MulAut S) (A : Subgroup H) (hAS : A ≤ S) (n : ℕ) :
    image (α ^ n) A = (image α)^[n] A := by
  induction n with
  | zero =>
    change (A.subgroupOf S).map S.subtype = A
    exact map_subgroupOf_eq_of_le hAS
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih, image_trans_aut]
    congr 1
    ext x
    change ((α ^ (n+1)) x : H) = ((α * α ^ n) x : H)
    rw [pow_succ']

/-- Replace a block of successive diagram shifts by the power twist. The
error is the actual shifted error subgroup, not an assumed congruence. -/
theorem power_twist_comparison
    (S : Subgroup H) (α : MulAut S) (g : H)
    (A C V Efinal : Subgroup H) [C.Normal] (hCS : C ≤ S)
    (hcomm : ⁅(⊤ : Subgroup H), C⁆ ≤ V)
    (E : ℕ → Subgroup H) (hEzero : E 0 = ⊥) (n : ℕ)
    (hE : ∀ i ≤ n, E i ≤ C)
    (hstep : ∀ i < n,
      image (α.trans ((MulAut.conj g).subgroupMap S)) (E i) ⊔ V ≤ E (i + 1))
    (hA : ∀ i ≤ n, (image (α.trans ((MulAut.conj g).subgroupMap S)))^[i] A ≤ C)
    (hfinal : image (α.trans ((MulAut.conj g).subgroupMap S)) (E n) ≤ Efinal) :
    image ((α ^ (n+1)).trans ((MulAut.conj g).subgroupMap S)) A ≤
      (image (α.trans ((MulAut.conj g).subgroupMap S)))^[n+1] A ⊔ Efinal ∧
    (image (α.trans ((MulAut.conj g).subgroupMap S)))^[n+1] A ≤
      image ((α ^ (n+1)).trans ((MulAut.conj g).subgroupMap S)) A ⊔ Efinal := by
  let φ := α.trans ((MulAut.conj g).subgroupMap S)
  obtain ⟨h₁,h₂⟩ := iterate_twisted_comparison S α g A C V hCS hcomm E hEzero n hE hstep hA
  have hAS : A ≤ S := (hA 0 (Nat.zero_le n)).trans hCS
  have hαS : (image α)^[n] A ≤ S := by
    rw [← image_pow_aut α A hAS n]
    exact image_le _ _
  have he : image φ ((image α)^[n] A) =
      image ((α ^ (n+1)).trans ((MulAut.conj g).subgroupMap S)) A := by
    rw [← image_pow_aut α A hAS n, image_trans_aut]
    congr 1
    ext x
    change g * α ((α ^ n) x) * g⁻¹ = g * (α ^ (n+1)) x * g⁻¹
    rw [pow_succ']
    rfl
  have hm₁ := image_mono φ h₁
  have hm₂ := image_mono φ h₂
  rw [image_sup φ _ _ ((hA n le_rfl).trans hCS) ((hE n le_rfl).trans hCS), he] at hm₁
  rw [image_sup φ _ _ hαS ((hE n le_rfl).trans hCS), he] at hm₂
  simp only [Function.iterate_succ_apply']
  exact ⟨hm₁.trans (sup_le_sup_left hfinal _), hm₂.trans (sup_le_sup_left hfinal _)⟩

end Theory.GroupTheory.SubgroupTransport

namespace Theory.GroupTheory.SubgroupTransport
open Subgroup
variable {H : Type*} [Group H]

/-- The two chief-filtration blocks in source 6.4. Each power twist is
compared with actual diagram shifts; the shifted middle layer is absorbed
in Q. Escape of the final diagram shift therefore proves escape of the
second power twist. -/
theorem twice_power_twist_escape
    (S : Subgroup H) (α : MulAut S) (g : H)
    (Z N Q V M : Subgroup H) [N.Normal] [Q.Normal]
    (hNQ : N ≤ Q) (hQS : Q ≤ S)
    (hNV : ⁅(⊤ : Subgroup H), N⁆ ≤ V)
    (hQM : ⁅(⊤ : Subgroup H), Q⁆ ≤ M)
    (E₁ E₂ : ℕ → Subgroup H) (hE₁zero : E₁ 0 = ⊥) (hE₂zero : E₂ 0 = ⊥)
    (n : ℕ)
    (hE₁ : ∀ i ≤ n, E₁ i ≤ N)
    (hE₂ : ∀ i ≤ n, E₂ i ≤ Q)
    (hstep₁ : ∀ i < n,
      image (α.trans ((MulAut.conj g).subgroupMap S)) (E₁ i) ⊔ V ≤ E₁ (i + 1))
    (hstep₂ : ∀ i < n,
      image (α.trans ((MulAut.conj g).subgroupMap S)) (E₂ i) ⊔ M ≤ E₂ (i + 1))
    (hfinal₁ : image (α.trans ((MulAut.conj g).subgroupMap S)) (E₁ n) ≤ N)
    (hfinal₂ : image (α.trans ((MulAut.conj g).subgroupMap S)) (E₂ n) ≤ Q)
    (hZ : ∀ i ≤ n, (image (α.trans ((MulAut.conj g).subgroupMap S)))^[i] Z ≤ N)
    (hB : ∀ i ≤ n, (image (α.trans ((MulAut.conj g).subgroupMap S)))^[i]
      ((image (α.trans ((MulAut.conj g).subgroupMap S)))^[n+1] Z) ≤ Q)
    (hN : ∀ i ≤ n+1, (image (α.trans ((MulAut.conj g).subgroupMap S)))^[i] N ≤ Q)
    (hescape : ¬ (image (α.trans ((MulAut.conj g).subgroupMap S)))^[n+1]
      ((image (α.trans ((MulAut.conj g).subgroupMap S)))^[n+1] Z) ≤ Q) :
    ¬ (image ((α ^ (n+1)).trans ((MulAut.conj g).subgroupMap S)))^[2] Z ≤ Q := by
  let φ := α.trans ((MulAut.conj g).subgroupMap S)
  let ψ := (α ^ (n+1)).trans ((MulAut.conj g).subgroupMap S)
  let B := (image φ)^[n+1] Z
  obtain ⟨hz₁,hz₂⟩ := power_twist_comparison S α g Z N V N (hNQ.trans hQS)
    hNV E₁ hE₁zero n hE₁ hstep₁ hZ hfinal₁
  obtain ⟨_,hb₂⟩ := power_twist_comparison S α g B Q M Q hQS
    hQM E₂ hE₂zero n hE₂ hstep₂ hB hfinal₂
  obtain ⟨hn₁,_⟩ := power_twist_comparison S α g N Q M Q hQS
    hQM E₂ hE₂zero n hE₂ hstep₂ (fun i hi => hN i (hi.trans (Nat.le_succ n))) hfinal₂
  have hψN : image ψ N ≤ Q := hn₁.trans (sup_le (hN (n+1) le_rfl) le_rfl)
  have hBQ : B ≤ Q := hB 0 (Nat.zero_le n)
  have hψZS : image ψ Z ≤ S := (hz₁.trans (sup_le hBQ hNQ)).trans hQS
  have hm := image_mono ψ hz₂
  rw [image_sup ψ _ _ hψZS (hNQ.trans hQS)] at hm
  intro hbad
  have hh : image ψ (image ψ Z) ≤ Q := by simpa [Function.iterate_succ_apply'] using hbad
  have hψB : image ψ B ≤ Q := hm.trans (sup_le hh hψN)
  exact hescape (hb₂.trans (sup_le hψB le_rfl))

end Theory.GroupTheory.SubgroupTransport
