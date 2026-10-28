module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Interfaces
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Bounds
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Cardinality
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ElementaryBranch
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Complements.Coordinates
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Complements.ElementaryQuotient
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Complements.TorusAction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Complements.CoprimeBranch

/-!
# Source steps for the Suzuki complement argument

The actual commutator coordinates identify S/T with M° equivariantly under K.
The torus action thus discharges the transitivity premise in both branches of
GLS4, Chapter 2, Lemma 14.7. Coprime centralizer generation constructs the
invariant elementary complement. Suzuki square fibers and an involution outside
T make the literal image of S in M/M° elementary abelian.

The complement branch retains the permitted cyclicity, order-divisibility and
fixed-point restrictions on Y; the enclosing WeakClosure assembly must supply
them from the Suzuki model restrictions. The elementary-quotient branch needs
no additional model premise and includes both source omega formulations. Its
application to an elementary complement supplies the opening step of Lemma 14.8.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemma 14.7 and the start of Lemma 14.8.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The invariant complement of Lemma 14.7(a), with only the permitted Suzuki
model restrictions explicit. The torus action is constructed from the source
geometry, including its equivariant identification of the actual quotient. -/
public theorem Context.invariantElementaryComplement (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (s : SylowGeometry g)
    (Y : Subgroup G) (hY : Y ≤ centralizer (residualGenerated M z t : Set G))
    (hYne : Y ≠ ⊥) (hYodd : Odd (Nat.card Y))
    (hproduct : (centralizer (residualGenerated M z t : Set G) : Set G) =
      (g.U : Set G) * (Y : Set G))
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal)
    (hYcyc : IsCyclic Y) (hYdvd : Nat.card Y ∣ 2 ^ (2 * m + 1) - 1)
    (hfree : ∀ y ∈ Y, y ≠ 1 → ∀ u ∈ g.U, Commute u y → u = 1) :
    InvariantElementaryComplement g Y :=
  invariantElementaryComplement_of_torusQuotientAction d g hsemi f hf s Y hY
    hYne hYodd hproduct hU hYcyc hYdvd hfree (d.torusQuotientAction g s hsemi)

/-- The literal exterior-involution form of Lemma 14.7(b), with no additional
model or torus-action premise. -/
public theorem Context.elementaryQuotient_of_involution (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hsemi : TorusSemiregular M t)
    (hinv : ∃ a ∈ g.S, a ^ 2 = 1 ∧ a ∉ g.T) : ElementaryQuotient d g :=
  elementaryQuotient_of_torusQuotientAction d g s (d.torusQuotientAction g s hsemi) hinv

/-- Source Lemma 14.7(b) in the form Ω₁(T) < Ω₁(S). -/
public theorem Context.elementaryQuotient_of_omega_lt (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hsemi : TorusSemiregular M t)
    (hOmega : omegaOneAmbient g.T < omegaOneAmbient g.S) : ElementaryQuotient d g :=
  d.elementaryQuotient_of_involution g s hsemi (g.exists_involution_of_omega_lt hOmega)

/-- Source Lemma 14.7(b), with the proved identification Ω₁(T) = M°U. -/
public theorem Context.elementaryQuotient_of_omega_product_lt (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hsemi : TorusSemiregular M t)
    (hOmega : closure (Z ∩ (M : Set G)) ⊔ g.U < omegaOneAmbient g.S) :
    ElementaryQuotient d g := by
  apply d.elementaryQuotient_of_omega_lt g s hsemi
  rwa [g.omega_T_eq]

/-- The application at the start of Lemma 14.8: an elementary complement
supplies the exterior involution required by Lemma 14.7(b). -/
public theorem Context.elementaryQuotient_of_invariantElementaryComplement
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hsemi : TorusSemiregular M t) {Y : Subgroup G}
    (hcomp : InvariantElementaryComplement g Y) : ElementaryQuotient d g := by
  obtain ⟨A, hAS, hAe, _, hproduct, _⟩ := hcomp
  let := hAe
  apply d.elementaryQuotient_of_involution g s hsemi
  by_contra hnone
  apply g.T_lt_S.not_ge
  intro x hx
  obtain ⟨v, hv, a, ha, rfl⟩ := (Set.ext_iff.mp hproduct x).mp hx
  have haT : a ∈ g.T := by
    by_contra haT
    exact hnone ⟨a, hAS ha, elemPow_eq_one_of_isElementaryAbelian a ha, haT⟩
  exact g.T.mul_mem hv haT

end BenderSuzuki.ZD.SuzukiExclusion
