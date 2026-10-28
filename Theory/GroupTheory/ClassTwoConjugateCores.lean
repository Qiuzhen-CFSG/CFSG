module
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Class-two cores and their nonabelian conjugate intersections

Suppose S=QB, B is normalized by X, and S normalizes Q. Assume every
nontrivial S-normal subgroup contains Z. If Q has class at most two and
all Q∩Qˣ, for x∈X, are nonabelian, then Q centralizes ⟨Zˣ : x∈X⟩.

Indeed D=[Q∩Qˣ,Q∩Qˣ] is nontrivial. The subgroup B normalizes D,
while Q centralizes it, so S normalizes D and Z≤D. Conjugating the
corresponding inclusion for x⁻¹ puts Zˣ in [Q,Q]≤C_G(Q).

In a finite two-group with a unique central involution the normal-subgroup
condition follows from the center-intersection theorem. The original
quintic consumer uses this to exclude class two without knowing the core
order or its center. Source: the crossing-core argument for
Aschbacher--Smith F.1.12 and14.2.21, printed pp.263,988--989.
-/

public section
namespace Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- Nonabelian crossing intersections force a class-two core to centralize
the conjugate span of the common normal line. -/
theorem class_two_centralizes_span_of_nonabelian_crossings
    (X S B Q Z : Subgroup G)
    (hBS : B ≤ S) (hSQ : S ≤ normalizer (Q : Set G))
    (hXB : X ≤ normalizer (B : Set G)) (hsplit : Q ⊔ B = S)
    (hdetect : ∀ D : Subgroup G, D ≤ S → S ≤ normalizer (D : Set G) →
      D ≠ ⊥ → Z ≤ D)
    (hcross : ∀ x ∈ X, ¬ IsMulCommutative (Q ⊓ Q.conjBy x : Subgroup G))
    (hclass : ⁅⁅Q,Q⁆,Q⁆ = ⊥) :
    Q ≤ centralizer (conjugateSpanBy Z X : Set G) := by
  have hcentral : ⁅Q,Q⁆ ≤ centralizer (Q : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hclass
  have hpoint (x : G) (hx : x ∈ X) : Z ≤ ⁅Q.conjBy x,Q.conjBy x⁆ := by
    let K := Q ⊓ Q.conjBy x
    let D := ⁅K,K⁆
    have hBconj : B.conjBy x = B := mem_normalizer_iff_map_conj_eq.mp (hXB hx)
    have hBQ : B ≤ normalizer (Q : Set G) := hBS.trans hSQ
    have hBQx : B ≤ normalizer (Q.conjBy x : Set G) := by
      rw [show Q.conjBy x = Q.map (MulAut.conj x).toMonoidHom from rfl,
        ← map_equiv_normalizer_eq]
      exact hBconj ▸ map_mono hBQ
    have hBK : B ≤ normalizer (K : Set G) :=
      (le_inf hBQ hBQx).trans inf_normalizer_le_normalizer_inf
    have hBD : B ≤ normalizer (D : Set G) := by
      intro b hb
      apply mem_normalizer_iff_map_conj_eq.mpr
      change (⁅K,K⁆).map (MulAut.conj b).toMonoidHom = ⁅K,K⁆
      have he : K.map (MulAut.conj b).toMonoidHom = K :=
        mem_normalizer_iff_map_conj_eq.mp (hBK hb)
      rw [map_commutator,he]
    have hDQ : D ≤ ⁅Q,Q⁆ := commutator_mono inf_le_left inf_le_left
    have hQD : Q ≤ normalizer (D : Set G) :=
      (le_centralizer_iff.mp (hDQ.trans hcentral)).trans (centralizer_le_normalizer _)
    have hSD : S ≤ normalizer (D : Set G) := hsplit ▸ sup_le hQD hBD
    have hDS : D ≤ S :=
      ((commutator_le_sup K K).trans (sup_le inf_le_left inf_le_left)).trans
        (hsplit ▸ le_sup_left)
    have hne : D ≠ ⊥ := fun he => hcross x hx (commutator_self_eq_bot_iff.mp he)
    exact (hdetect D hDS hSD hne).trans (commutator_mono inf_le_right inf_le_right)
  apply le_centralizer_iff.mpr
  rw [conjugateSpanBy_eq_iSup_conj]
  apply iSup_le
  intro x
  have hh := map_mono (f := (MulAut.conj (x : G)).toMonoidHom)
    (hpoint (x : G)⁻¹ (X.inv_mem x.property))
  rw [map_commutator] at hh
  change Z.conjBy (x : G) ≤ ⁅(Q.conjBy (x : G)⁻¹).conjBy (x : G),
    (Q.conjBy (x : G)⁻¹).conjBy (x : G)⁆ at hh
  rw [conjBy_inv'] at hh
  exact hh.trans hcentral

end Subgroup
