module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Kernel factorization in the five-dimensional-cover branch

Equality of images under H→H/O₂(H) gives the actual subgroup factorization
W=B(W∩O₂(H)). A kernel commutator bounded by a disjoint central line is
trivial. The factorization then identifies [W,V₃] with [B,V₃], contradicting
a strict lower bound from the four-dimensional symplectic calculation.

These are conditional subgroup deductions in the last paragraph of
Aschbacher–Smith 13.8.7, p.949. They do not assume the factorization as an
input: it is derived from equality of the literal star images. Proving that
image equality in the S₆ augmentation module remains a separate obligation.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
variable {G : Type*} [Group G]

/-- Equal images of nested subgroups give a product with the actual kernel. -/
theorem eq_sup_inf_ker_of_map_eq {J : Type*} [Group J]
    (f : G →* J) (B W : Subgroup G) (hBW : B ≤ W) (he : B.map f = W.map f) :
    W = B ⊔ (W ⊓ f.ker) := by
  apply le_antisymm _ (sup_le hBW inf_le_left)
  intro w hw
  obtain ⟨b, hb, hbw⟩ := (he ▸ mem_map_of_mem f hw : f w ∈ B.map f)
  have hk : b⁻¹ * w ∈ W ⊓ f.ker := by
    refine ⟨W.mul_mem (W.inv_mem (hBW hb)) hw, ?_⟩
    change f (b⁻¹ * w) = 1
    rw [map_mul, map_inv, hbw, inv_mul_cancel]
  have hmem := (B ⊔ (W ⊓ f.ker)).mul_mem ((show B ≤ B ⊔ (W ⊓ f.ker) from le_sup_left) hb)
    ((show W ⊓ f.ker ≤ B ⊔ (W ⊓ f.ker) from le_sup_right) hk)
  simpa only [mul_inv_cancel_left] using hmem

/-- The factorization uses Source.starImage and Source.QH, with both subgroup
containments in H retained. -/
theorem eq_sup_inf_QH_of_starImage_eq (H B W : Subgroup G)
    (hBW : B ≤ W) (hWH : W ≤ H)
    (he : Source.starImage H B = Source.starImage H W) :
    W = B ⊔ (W ⊓ Source.QH H) := by
  have hh := eq_sup_inf_ker_of_map_eq (QuotientGroup.mk' (pCore 2 H))
    (B.subgroupOf H) (W.subgroupOf H) (subgroupOf_mono H hBW) he
  rw [QuotientGroup.ker_mk'] at hh
  have hi := congrArg (fun X : Subgroup H => X.map H.subtype) hh
  rwa [Subgroup.map_sup, map_inf _ _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le hWH, map_subgroupOf_eq_of_le (hBW.trans hWH)] at hi

/-- A disjoint kernel bound makes the kernel factor centralize the seed. -/
theorem kernel_factor_centralizes (W Q B Z : Subgroup G)
    (hn : B ≤ normalizer (W : Set G)) (hb : ⁅Q, B⁆ ≤ Z)
    (hd : W ⊓ Z = ⊥) : ⁅W ⊓ Q, B⁆ = ⊥ := by
  apply le_bot_iff.mp
  rw [← hd]
  exact le_inf
    ((commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hn))
    ((commutator_mono inf_le_right le_rfl).trans hb)

/-- The source noncommuting seeds force the whole conjugates to have trivial
intersection, using the earlier commuting-intersection theorem. -/
theorem disjoint_of_noncommuting_seeds (V W B C : Subgroup G)
    (hBV : B ≤ V) (hCW : C ≤ W) (hn : ⁅B, C⁆ ≠ ⊥)
    (hinter : V ⊓ W ≠ ⊥ → ⁅V, W⁆ = ⊥) : V ⊓ W = ⊥ := by
  by_contra hi
  apply hn
  exact le_bot_iff.mp ((commutator_mono hBV hCW).trans (hinter hi).le)

/-- A centralizing factor adds nothing to the commutator when the whole group
normalizes the proposed commutator line. This requires no normalization of
B by C and no ambient normality. -/
theorem commutator_eq_of_kernel_factor
    (W B K C A : Subgroup G) (hgen : W = B ⊔ K)
    (hWK : W ≤ normalizer (A : Set G))
    (hBC : ⁅B, C⁆ = A) (hKC : ⁅K, C⁆ = ⊥) : ⁅W, C⁆ = A := by
  have hle : W ≤ commutatorPreimage W C A := by
    rw [hgen]
    apply sup_le
    · exact le_commutatorPreimage le_sup_left hBC.le
    · exact le_commutatorPreimage le_sup_right (hKC ▸ bot_le)
  apply le_antisymm
  · exact (commutator_mono hle le_rfl).trans
      (commutator_commutatorPreimage_le W C A hWK)
  · rw [← hBC]
    exact commutator_mono (hgen ▸ le_sup_left) le_rfl

/-- Terminal cover contradiction after the concrete model has supplied image
equality and the strict unipotent-radical displacement. -/
theorem cover_contradiction_of_starImage_eq
    (H W B C Z A : Subgroup G) (hBW : B ≤ W) (hWH : W ≤ H)
    (he : Source.starImage H B = Source.starImage H W)
    (hCW : C ≤ normalizer (W : Set G))
    (hQ : ⁅Source.QH H, C⁆ ≤ Z) (hd : W ⊓ Z = ⊥)
    (hWA : W ≤ normalizer (A : Set G)) (hBC : ⁅B, C⁆ = A)
    (hstrict : A < ⁅W, C⁆) : False := by
  have hgen := eq_sup_inf_QH_of_starImage_eq H B W hBW hWH he
  have hker := kernel_factor_centralizes W (Source.QH H) C Z hCW hQ hd
  have heq := commutator_eq_of_kernel_factor W B (W ⊓ Source.QH H) C A
    hgen hWA hBC hker
  exact hstrict.ne heq.symm

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
end
