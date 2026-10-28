module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition.Alternatives
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.NormalCubicProduct
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder

/-!
# Joint centralizers of the external component and cubic factor

Self-centralization of the intrinsic generalized Fitting subgroup puts the
joint centralizer inside KX. Commutation then puts its K-coordinate in Z(K),
so centerlessness puts the whole joint centralizer in X. Neither the full
conjugation image nor an S₃ complement is needed; the result also applies to
the compatible direct-product branch.

Source: Aschbacher–Smith 13.8.21(1), printed pp.956–957, and the finite-group
self-centralization theorem imported through the B.1 group-theory bridge.
-/

public section

open Subgroup
open Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
variable {H : Type*} [Group H] [Finite H]
/-- The joint centralizer is contained in the external factor. Only the
commuting product structure and centerlessness of K are used. -/
theorem joint_centralizer_le_external (K X : Subgroup H) [X.Normal]
    (hc : ∀ k : K, ∀ x : X, Commute (k : H) (x : H))
    (hF : generalizedFitting H = K ⊔ X) (hZ : center K = ⊥) :
    centralizer (K : Set H) ⊓ centralizer (X : Set H) ≤ X := by
  intro a ha
  have hCa : a ∈ centralizer (generalizedFitting H : Set H) := by
    intro y hy
    rw [hF] at hy
    obtain ⟨k, hk, x, hx, rfl⟩ := mem_sup_of_normal_right.mp hy
    exact (Commute.mul_left (ha.1 k hk) (ha.2 x hx)).eq
  have haF : a ∈ K ⊔ X := by
    rw [← hF]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le hCa
  obtain ⟨k, hk, x, hx, rfl⟩ := mem_sup_of_normal_right.mp haF
  have hxC : x ∈ centralizer (K : Set H) := fun y hy => (hc ⟨y, hy⟩ ⟨x, hx⟩).eq
  have hkC : k ∈ centralizer (K : Set H) := by
    exact (mul_mem_cancel_right hxC).mp ha.1
  have hkZ : (⟨k, hk⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (hkC y y.property)
  have hk1 : k = 1 := congrArg Subtype.val (mem_bot.mp (hZ.le hkZ))
  simpa [hk1] using hx
/-- The marked SL₃(2) component supplies the centerlessness required by the
joint-centralizer bound. Full conjugation image is not a hypothesis. -/
theorem joint_centralizer_le_external_of_linearThree
    (K X : Subgroup H) [X.Normal] (eK : K ≃* BinaryLinearThree.Group)
    (hc : ∀ k : K, ∀ x : X, Commute (k : H) (x : H))
    (hF : generalizedFitting H = K ⊔ X) :
    centralizer (K : Set H) ⊓ centralizer (X : Set H) ≤ X := by
  apply joint_centralizer_le_external K X hc hF
  apply (center K).eq_bot_iff_forall.mpr
  intro k hk
  have he : eK k ∈ center BinaryLinearThree.Group :=
    ((centerCongr eK) ⟨k, hk⟩).property
  exact eK.map_eq_one_iff.mp (mem_bot.mp (Matrix.PSL3Two.center_eq_bot.le he))

/-- The genuine generalized-Fitting product has two-group quotient. This
uses the actual outer group of the marked SL₃(2), without a splitting or a
full conjugation-image hypothesis. -/
theorem quotient_external_isTwoGroup
    (K X : Subgroup H) [K.Normal] [X.Normal] (eK : K ≃* BinaryLinearThree.Group)
    (hcard : Nat.card X = 3)
    (hc : ∀ k : K, ∀ x : X, Commute (k : H) (x : H))
    (hF : generalizedFitting H = K ⊔ X) : IsPGroup 2 (H ⧸ (K ⊔ X)) := by
  apply NormalCubicProduct.quotient_isTwoGroup K X hcard hc
    (joint_centralizer_le_external_of_linearThree K X eK hc hF)
  exact Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv
    (MulAut.outerCongr eK).symm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
