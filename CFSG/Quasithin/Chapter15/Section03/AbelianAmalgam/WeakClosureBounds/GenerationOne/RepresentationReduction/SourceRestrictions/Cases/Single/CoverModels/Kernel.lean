module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CoverModels.Preparation
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.CoveringKernelCard

/-!
# Reducing the local cover to concrete multiplier prime support

The canonical component covering composed with any actual source model
is dominated by the genuine universal perfect central cover. Perfectness
makes the comparison map surjective, so the actor center order divides
that universal kernel order. Prime support contained in {2,3} is enough:
Preparation excludes two using O₂(A)=1, and three using |M∩H|.

The model-specific support results remain explicit premises. This does
not identify a universal covering with SL or SU, assume splitting, or
ignore the exceptional Suzuki two-cover.

Source: Aschbacher--Smith, I.1.1--4, pp.407--408, used in the single
component argument of E.2.2, pp.215--216, and 15.3.65, p.1152.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
open BorelReduction
namespace CoverModels
universe u
variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {H M K T Z ZS : Subgroup G} {f : ℕ}
variable [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
variable {a : LocalQuotientAction H (conjugateSpanBy ZS H) Z}
variable {I : Submodule (ZMod 2)
  (Additive ((conjugateSpanBy ZS H) ⧸ Z.subgroupOf (conjugateSpanBy ZS H)))}
variable (h : LocalInput 𝒦 H M K T Z ZS f a I)
include h

/-- A comparison from the genuine universal cover bounds the center of the
actual actor. The lift is surjective because the actor is perfect. -/
theorem center_order_dvd_universalKernel {X : Type*} [Group X]
    (e : sourceImage H M K ≃* X) :
    Nat.card (center (actorImage H K)) ∣ Nat.card (universalProjection X).ker := by
  let c := modelCover h e
  let := c.isPerfect
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective c.surjective
  obtain ⟨j, hj, _⟩ := universalProjection_existsUnique_lift c.toMonoidHom
    c.surjective c.ker_le_center
  have hsurj : Function.Surjective j :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect c.toMonoidHom j
      (hj ▸ universalProjection_surjective X) c.ker_le_center
  rw [← modelCover_ker h e]
  exact kernel_card_dvd_of_surjective_factor (universalProjection X) c.toMonoidHom j hsurj hj

/-- Only prime support of the actual universal kernel is consumed. This
allows a Suzuki two-cover and a unitary three-center before the local
hypotheses exclude them. It does not postulate a split cover. -/
theorem center_eq_bot_of_universalKernel_prime_support {X : Type*} [Group X]
    (e : sourceImage H M K ≃* X)
    (hmult : ∀ p : ℕ, p.Prime → p ∣ Nat.card (universalProjection X).ker → p = 2 ∨ p = 3) :
    center (actorImage H K) = ⊥ :=
  center_eq_bot_of_prime_support h
    (fun p hp hd => hmult p hp (hd.trans (center_order_dvd_universalKernel h e)))

end CoverModels
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
