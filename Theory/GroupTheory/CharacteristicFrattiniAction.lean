module
public import Theory.GroupTheory.CharacteristicRestrictionInnerSquares
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.Frattini.PGroup

/-!
# Quotient-trivial automorphisms centralize the inner Frattini action

Let N be a characteristic finite p-subgroup of G. The inner action of G on
N/Φ(N) factors through G/N. Every automorphism of G that is trivial on
G/N therefore centralizes this inner action after restriction to N/Φ(N).
All actions use the same characteristic restriction and quotient maps.

The proof first kills inner N on its abelian Frattini quotient. Restriction
intertwines conjugation by g with conjugation by α(g). Since g and α(g)
have the same image in G/N, their induced inner actions coincide.

This elementary characteristic-section argument supplies the module-centralizer
containment in the covered G₂(4) calculation of Aschbacher–Smith, Lemma16.5.13,
printed p.1202. It does not assume any particular structure or representation
of that cover.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] (N : Subgroup G) [N.Characteristic]

/-- The automorphism action on the actual Frattini section of N. -/
def characteristicFrattiniAction : MulAut G →* MulAut (N ⧸ frattini N) :=
  (quotientAut (frattini N)).comp (MulAut.characteristic N)

/-- The inner action on the same Frattini section. -/
def frattiniConjugation : G →* MulAut (N ⧸ frattini N) :=
  (quotientAut (frattini N)).comp (MulAut.conjNormal : G →* MulAut N)

variable [Finite N] {p : ℕ} [Fact p.Prime] (hp : IsPGroup p N)
include hp

/-- Inner elements of a p-group act trivially on its abelian Frattini section. -/
theorem le_ker_frattiniConjugation : N ≤ (frattiniConjugation N).ker := by
  let _ : Fact (IsPGroup p N) := ⟨hp⟩
  let _ : IsElementaryAbelian p (N ⧸ frattini N) :=
    isElementaryAbelian_quotient_frattini (p := p)
  intro g hg
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro v
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (frattini N) v
  change quotientAut (frattini N) (MulAut.conjNormal g)
    (QuotientGroup.mk' (frattini N) q) = QuotientGroup.mk' (frattini N) q
  rw [quotientAut_apply_mk]
  change QuotientGroup.mk' (frattini N)
    ((⟨g, hg⟩ : N) * q * (⟨g, hg⟩ : N)⁻¹) = QuotientGroup.mk' (frattini N) q
  rw [map_mul, map_mul, map_inv,
    mul_comm (QuotientGroup.mk' (frattini N) (⟨g, hg⟩ : N))
      (QuotientGroup.mk' (frattini N) q), mul_inv_cancel_right]

/-- Automorphisms trivial on G/N centralize the induced inner action on N/Φ(N). -/
theorem quotient_kernel_frattiniImage_le_centralizer :
    (quotientAut N).ker.map (characteristicFrattiniAction N) ≤
      centralizer ((frattiniConjugation N).range : Set _) := by
  rintro a ⟨α, hα, rfl⟩
  apply mem_centralizer_iff.mpr
  rintro b ⟨g, rfl⟩
  let φ := frattiniConjugation N
  let lift := QuotientGroup.lift N φ (le_ker_frattiniConjugation N hp)
  have heq : QuotientGroup.mk' N (α g) = QuotientGroup.mk' N g := by
    have h := DFunLike.congr_fun (show quotientAut N α = 1 from hα)
      (QuotientGroup.mk' N g)
    rw [quotientAut_apply_mk] at h
    exact h
  have hsame : φ (α g) = φ g := congrArg lift heq
  have hconj := congrArg (quotientAut (frattini N))
    (characteristic_conjNormal_equivariant N α g)
  simp only [map_mul, map_inv] at hconj
  change characteristicFrattiniAction N α * φ g *
    (characteristicFrattiniAction N α)⁻¹ = φ (α g) at hconj
  rw [hsame] at hconj
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
end Subgroup
