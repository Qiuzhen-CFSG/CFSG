module

public import Theory.GroupTheory.PerfectNormalizerLift
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Lifting finite conjugate generation through a perfect central quotient

For a perfect normal subgroup L containing its centralizer, its conjugation
image on an identified quotient L/Z(L) detects subgroup containments in L.
Restricting to L makes the kernel central; perfectness then removes it.
Thus a finite tuple of inner conjugators in the projective group lifts to
literal ambient conjugators whose conjugates generate a subgroup containing
all of L. The acting element itself need not belong to L.

This is the central-cover step for the generation estimates in
Guralnick–Malle, *Classification of 2F-modules I*, §2 and Proposition 4.3,
as used in Aschbacher–Smith K.2, printed p.453. The model generation estimate
is an explicit premise, not a conclusion of this module.
-/

public section
open Subgroup

namespace Subgroup
variable {G D : Type*} [Group G] [Group D]

/-- A kernel lying in the center of the perfect subgroup can be removed from image containment. -/
theorem le_of_map_le_of_perfect_relative_kernel
    (f : G →* D) (L H : Subgroup G) [Group.IsPerfect L]
    (hker : f.ker ≤ (center L).map L.subtype)
    (h : L.map f ≤ H.map f) : L ≤ H := by
  let fL := f.comp L.subtype
  have hkerL : f.ker ≤ L := hker.trans (map_subtype_le _)
  have hc : fL.ker ≤ center L := by
    intro x hx
    obtain ⟨z, hz, he⟩ := hker hx
    exact (Subtype.ext he : z = x) ▸ hz
  have hm : (⊤ : Subgroup L).map fL ≤ (H.subgroupOf L).map fL := by
    rintro _ ⟨x, _, rfl⟩
    obtain ⟨y, hy, he⟩ := h (mem_map_of_mem f x.property)
    have hk : y * (x : G)⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    have hyL : y ∈ L := by
      simpa only [inv_mul_cancel_right] using L.mul_mem (hkerL hk) x.property
    exact ⟨⟨y, hyL⟩, hy, he⟩
  have htop := le_of_map_le_of_perfect fL hc ⊤ (H.subgroupOf L) hm
  intro x hx
  exact htop (show (⟨x, hx⟩ : L) ∈ (⊤ : Subgroup L) from mem_top _)

end Subgroup

namespace MulAut

/-- Inner conjugators whose conjugates of the actor contain the whole inner automorphism group. -/
@[expose] def HasInnerConjugateCover {S : Type*} [Group S] (a : MulAut S) (n : ℕ) : Prop :=
  ∃ s : Fin n → S, (conj : S →* MulAut S).range ≤
    closure (Set.range fun i => conj (s i) * a * (conj (s i))⁻¹)

/-- A tuple can be extended by identity conjugators without losing generation. -/
theorem HasInnerConjugateCover.mono {S : Type*} [Group S] {a : MulAut S}
    {n m : ℕ} (h : HasInnerConjugateCover a n) (hnm : n ≤ m) :
    HasInnerConjugateCover a m := by
  classical
  obtain ⟨s, hs⟩ := h
  let r : Fin m → S := fun i => if hi : (i : ℕ) < n then s ⟨i, hi⟩ else 1
  refine ⟨r, hs.trans (closure_mono ?_)⟩
  rintro _ ⟨i, rfl⟩
  refine ⟨i.castLE hnm, ?_⟩
  simp [r, i.isLt]

variable {G S : Type*} [Group G] [Group S]
    (L : Subgroup G) [L.Normal] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* S)

/-- The actual ambient conjugation action on a specified central quotient. -/
@[expose] def centralQuotientConjugation : G →* MulAut S :=
  (centralQuotientAction e).comp (conjNormal : G →* MulAut L)

/-- Perfectness makes the kernel exactly the centralizer of the original subgroup. -/
theorem centralQuotientConjugation_ker :
    (centralQuotientConjugation L e).ker = centralizer (L : Set G) := by
  rw [← conjNormal_ker_eq_centralizer L]
  ext x
  change centralQuotientAction e (conjNormal x) = 1 ↔ conjNormal x = 1
  rw [← map_one (centralQuotientAction e), (centralQuotientAction_injective e).eq_iff]

omit [Group.IsPerfect L] in
/-- Component elements act by the corresponding inner automorphism of the model. -/
theorem centralQuotientConjugation_coe (x : L) :
    centralQuotientConjugation L e x = conj (e (QuotientGroup.mk' (center L) x)) := by
  change centralQuotientAction e (conjNormal (x : G)) = _
  rw [conjNormal_val, centralQuotientAction_conj]

/-- Lift the full generated containment, including the center, with the same number of conjugates. -/
theorem lift_conjugate_generation
    (hc : centralizer (L : Set G) ≤ L) (t : G) {n : ℕ}
    (s : Fin n → S)
    (hs : (conj : S →* MulAut S).range ≤ closure (Set.range fun i =>
      conj (s i) * centralQuotientConjugation L e t * (conj (s i))⁻¹)) :
    ∃ g : Fin n → G, L ≤ closure (Set.range fun i => g i * t * (g i)⁻¹) := by
  have hlift : ∀ i, ∃ x : L, e (QuotientGroup.mk' (center L) x) = s i :=
    fun i => (e.surjective.comp (QuotientGroup.mk'_surjective (center L))) (s i)
  choose x hx using hlift
  refine ⟨fun i => (x i : G), ?_⟩
  let f := centralQuotientConjugation L e
  have hker : f.ker ≤ (center L).map L.subtype := by
    rw [centralQuotientConjugation_ker]
    intro z hz
    refine ⟨⟨z, hc hz⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext (mem_centralizer_iff.mp hz l l.property)
  apply le_of_map_le_of_perfect_relative_kernel f L _ hker
  rw [MonoidHom.map_closure, ← Set.range_comp]
  change L.map f ≤ closure (Set.range fun i => f ((x i : G) * t * (x i : G)⁻¹))
  have he : (fun i => f ((x i : G) * t * (x i : G)⁻¹)) =
      (fun i => conj (s i) * f t * (conj (s i))⁻¹) := by
    funext i
    simp only [map_mul, map_inv, f, centralQuotientConjugation_coe, hx]
  rw [he]
  apply le_trans _ hs
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨e (QuotientGroup.mk' (center L) ⟨a, ha⟩),
    (centralQuotientConjugation_coe L e ⟨a, ha⟩).symm⟩

end MulAut
