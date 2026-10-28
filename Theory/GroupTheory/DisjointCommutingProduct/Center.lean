module
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The center of a product with a central factor

For P = E D with E central in P, the center is E Z(D). If E and D are
disjoint and Z(D) has order two, E has index two in Z(P). All factors and
relative indices retain their original ambient embeddings.

Source application: Aschbacher–Smith C.6.4, printed p.168, where E is the
fixed elementary factor and D is the initial dihedral group.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem center_eq_sup_of_central_factor (P E D : Subgroup G)
    (hprod : P = E ⊔ D) (hc : E ≤ centralizer (P : Set G)) :
    P ⊓ centralizer (P : Set G) = E ⊔ (D ⊓ centralizer (D : Set G)) := by
  have hEP : E ≤ P := hprod ▸ le_sup_left
  have hDP : D ≤ P := hprod ▸ le_sup_right
  have hED : E ≤ centralizer (D : Set G) := hc.trans (centralizer_le hDP)
  have hDE : D ≤ centralizer (E : Set G) := le_centralizer_iff.mp hED
  apply le_antisymm
  · intro a ha
    have ha' : a ∈ E ⊔ D := hprod ▸ ha.1
    obtain ⟨e,he,b,hb,rfl⟩ := (show ∃ e ∈ E, ∃ b ∈ D, e*b=a from by
      change a ∈ ((E ⊔ D : Subgroup G) : Set G) at ha'
      rwa [coe_mul_of_right_le_normalizer_left E D
        (hDE.trans (centralizer_le_normalizer _))] at ha')
    have hbC : b ∈ centralizer (P : Set G) :=
      (centralizer (P : Set G)).mul_mem_cancel_left (hc he) |>.mp ha.2
    exact mul_mem_sup he ⟨hb,centralizer_le hDP hbC⟩
  · refine sup_le (le_inf hEP hc) (le_inf (inf_le_left.trans hDP) ?_)
    apply le_centralizer_iff.mpr
    rw [hprod]
    exact sup_le (hED.trans (centralizer_le inf_le_left))
      (le_centralizer_iff.mp (show D ⊓ centralizer (D : Set G) ≤ centralizer (D : Set G) from inf_le_right))

theorem central_factor_relIndex_center (P E D Z : Subgroup G)
    (hprod : P = E ⊔ D) (hc : E ≤ centralizer (P : Set G)) (hd : Disjoint E D)
    (hZ : D ⊓ centralizer (D : Set G) = Z) (hcard : Nat.card Z = 2) :
    E.relIndex (P ⊓ centralizer (P : Set G)) = 2 := by
  rw [center_eq_sup_of_central_factor P E D hprod hc,hZ]
  have hZD : Z ≤ D := hZ ▸ inf_le_left
  have hZE : Z ≤ centralizer (E : Set G) := hZD.trans
    (le_centralizer_iff.mp (hc.trans (centralizer_le (show D ≤ P from hprod ▸ (le_sup_right : D ≤ E ⊔ D)))))
  have hcprod := card_sup_eq_mul_of_normalizes_of_disjoint E Z
    (hZE.trans (centralizer_le_normalizer _)) (hd.mono_right hZD)
  rw [hcard] at hcprod
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) E (E ⊔ Z) bot_le le_sup_left
  simp only [relIndex_bot_left] at hi
  rw [hcprod] at hi
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hi
end Subgroup
