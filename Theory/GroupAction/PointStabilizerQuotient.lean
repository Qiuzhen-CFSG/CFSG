module

public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Conjugation
public import Theory.LinearAlgebra.BinaryFivePointStabilizer

/-!
# The actual action on a core quotient

A faithful representation of M/F in a point stabilizer identifies Q/F with
its translation kernel. Conjugation on those translations descends to a
faithful action of M/Q. The explicit equivalence and conjugation identity
retain the literal maps from Q and the actual quotient by F inside Q.

Application: the Ree and Tits residual argument, Aschbacher--Smith 14.2.21,
printed p.989. The caller supplies the representation and its core image.
-/

@[expose] public section
open Subgroup Theory.LinearAlgebra.BinaryFivePointStabilizer
noncomputable section
namespace Theory.GroupAction.PointStabilizerQuotient
variable {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
  (z : E) (hz : z ≠ 0) (F Q : Subgroup M) [F.Normal]
  (hFQ : F ≤ Q) (ρ : M ⧸ F →* stabilizer z) (hρ : Function.Injective ρ)
  (hQN : Q.map (ρ.comp (QuotientGroup.mk' F)) = kernel z)

/-- The core map to the displacement kernel. -/
def translations : Q →* kernel z :=
  ((ρ.comp (QuotientGroup.mk' F)).comp Q.subtype).codRestrict (kernel z)
    (fun x => hQN ▸ mem_map_of_mem _ x.property)

include hρ in
/-- The denominator is exactly F restricted to Q. -/
theorem translations_ker : (translations z F Q ρ hQN).ker = F.subgroupOf Q := by
  ext x
  change (⟨ρ (QuotientGroup.mk' F x), _⟩ : kernel z) = 1 ↔ (x : M) ∈ F
  rw [Subtype.ext_iff]
  change ρ (QuotientGroup.mk' F x) = 1 ↔ _
  rw [← ρ.map_one, hρ.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

/-- Every displacement is the image of a core element. -/
theorem translations_surjective : Function.Surjective (translations z F Q ρ hQN) := by
  intro n
  have hn := hQN.ge n.property
  obtain ⟨x, hx, he⟩ := hn
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

/-- The actual core quotient is identified with translations. -/
def translationsEquiv : (Q ⧸ F.subgroupOf Q) ≃* kernel z :=
  (QuotientGroup.quotientMulEquivOfEq (translations_ker z F Q ρ hρ hQN).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (translations z F Q ρ hQN)
      (translations_surjective z F Q ρ hQN))

include hz hFQ hρ hQN in
/-- The kernel of conjugation on translations is exactly Q. -/
theorem action_ker :
    ((MulAut.conjNormal : stabilizer z →* MulAut (kernel z)).comp
      (ρ.comp (QuotientGroup.mk' F))).ker = Q := by
  rw [← MonoidHom.comap_ker, conjugation_kernel z hz, ← hQN]
  apply comap_map_eq_self
  rw [MonoidHom.ker_comp_of_injective _ ρ hρ, QuotientGroup.ker_mk']
  exact hFQ

variable [Q.Normal]

/-- The ambient quotient action induced by conjugation on the core quotient. -/
def action : M ⧸ Q →* MulAut (kernel z) :=
  QuotientGroup.lift Q ((MulAut.conjNormal : stabilizer z →* MulAut (kernel z)).comp
    (ρ.comp (QuotientGroup.mk' F))) (le_of_eq (action_ker z hz F Q hFQ ρ hρ hQN).symm)

/-- The ambient quotient acts faithfully on the actual core quotient. -/
theorem action_injective : Function.Injective (action z hz F Q hFQ ρ hρ hQN) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (action_ker z hz F Q hFQ ρ hρ hQN).symm

/-- The descended action agrees with conjugation of every actual core element. -/
theorem compatibility (g : M) (x : Q) :
    action z hz F Q hFQ ρ hρ hQN (QuotientGroup.mk' Q g)
      (translations z F Q ρ hQN x) =
        translations z F Q ρ hQN (MulAut.conjNormal g x) := by
  apply Subtype.ext
  change ρ (QuotientGroup.mk' F g) * ρ (QuotientGroup.mk' F (x : M)) *
    (ρ (QuotientGroup.mk' F g))⁻¹ =
      ρ (QuotientGroup.mk' F (g * (x : M) * g⁻¹))
  simp only [map_mul, map_inv]
end Theory.GroupAction.PointStabilizerQuotient
