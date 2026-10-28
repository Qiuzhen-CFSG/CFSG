module

public import Theory.GroupTheory.QuaternionCentralProductInvertingAction
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The local configuration needed by G₂(3) recognition

The structure below records precisely (G1) and (G2) of Section I.4, printed
p.417, including normality inside H, the ambient centralizer identity, the
generalized Fitting subgroup of M, and actual matrix-group isomorphisms.
Commutation of the two factors is retained for the Chapter 14 consumer.

The construction proves the last factor step of Theorem 14.4.3, printed
p.1008, from a quaternion core and an inverting order-eighteen quotient.
The hypotheses about the two local subgroups are explicit: their derivation
from Hypothesis 14.3.10, via Lemmas 14.4.4 and 14.4.5, is still required.
This module does not claim either of those lemmas.
-/

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour

/-- The genuine local configuration (G1)–(G2) preceding I.4.5.
The groups H₁ and H₂ are subgroups of H, not normal subgroups of the ambient G. -/
public structure G2ThreeConfiguration (G : Type*) [Group G] where
  H : Subgroup G
  M : Subgroup G
  H₁ : Subgroup H
  H₂ : Subgroup H
  H₁_normal : H₁.Normal
  H₂_normal : H₂.Normal
  H₁_model : Nonempty (H₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
  H₂_model : Nonempty (H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
  commute : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x
  index : (H₁ ⊔ H₂).index = 2
  intersection_model : Nonempty ((H₁ ⊓ H₂ : Subgroup H) ≃* Multiplicative (ZMod 2))
  centralizer : H = Subgroup.centralizer (((H₁ ⊓ H₂).map H.subtype : Subgroup G) : Set G)
  V : Subgroup M
  V_normal : V.Normal
  fitting : V = generalizedFitting M
  V_model : Nonempty (V ≃* Multiplicative (Fin 3 → ZMod 2))
  quotient_model : letI := V_normal
    Nonempty ((M ⧸ V) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))

/-- Construct every recognition field from the local quaternion calculation.
No SL₂(3) factor or recognition witness is an input. The order-eighteen
quotient and local M hypotheses must be derived in the source assembly. -/
public theorem configuration_of_quaternion_inverting_quotient
    {G : Type*} [Group G] [Finite G]
    (H M : Subgroup G) (Q : Subgroup H) [Q.Normal]
    (d : QuaternionCentralProductData Q)
    (hcentral : centralizer (Q : Set H) ≤ Q) (hindex : Q.index = 18)
    (s : H) (hgen : pResidual 2 H ⊔ zpowers s = ⊤)
    (hinv : ∀ k : pResidual 2 H,
      QuotientGroup.mk' Q (s * k * s⁻¹) = (QuotientGroup.mk' Q k)⁻¹)
    (hH : H = centralizer
      ((((center Q).map Q.subtype).map H.subtype : Subgroup G) : Set G))
    (V : Subgroup M) [V.Normal]
    (hVcore : V = pCore 2 M) (hVcentral : centralizer (V : Set M) ≤ V)
    (hVmodel : Nonempty (V ≃* Multiplicative (Fin 3 → ZMod 2)))
    (hMquotient : Nonempty ((M ⧸ V) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) :
    Nonempty (G2ThreeConfiguration G) := by
  obtain ⟨c, hn₁, hn₂, hi⟩ := normal_residual_factors_of_quaternion_inverting_quotient
    Q d hcentral hindex s hgen hinv
  have hI : Nat.card (c.left ⊓ c.right : Subgroup H) = 2 := by
    rw [c.intersection, card_map_of_injective Q.subtype_injective, d.center_card]
  refine ⟨{
    H := H, M := M, H₁ := c.left, H₂ := c.right
    H₁_normal := hn₁, H₂_normal := hn₂
    H₁_model := c.left_model, H₂_model := c.right_model
    commute := c.commute, index := hi
    intersection_model := ⟨mulEquivOfPrimeCardEq hI (by simp)⟩
    centralizer := ?_
    V := V, V_normal := inferInstance, fitting := ?_
    V_model := hVmodel, quotient_model := hMquotient }⟩
  · rw [c.intersection]
    exact hH
  · rw [hVcore]
    exact (generalizedFitting_eq_pCore_of_selfCentralizing 2
      (by simpa only [← hVcore] using hVcentral)).symm

end CFSG.Quasithin.Chapter14.Section04.DimensionFour
