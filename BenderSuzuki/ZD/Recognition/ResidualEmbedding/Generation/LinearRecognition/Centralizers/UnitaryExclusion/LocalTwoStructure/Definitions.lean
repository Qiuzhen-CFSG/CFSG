module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.Inputs
public import Theory.GroupTheory.PGroup.Homocyclic

/-!+# The literal subgroups in the local unitary argument

These definitions retain the two-cores of the intersections with M and the
normalizer defining U. `HomocyclicLocalData` separates the remaining model
and placement facts from the A×B, Frattini and product arguments. It contains
neither commutativity of T with U nor the rank or order of their product.

`FixedCentralizerRigidity` is the intrinsic automorphism statement in
Chapter 4, 3.4(d1), including centralization of the involutory automorphism.
It is a proof obligation, not an assertion that this model fact is available.

Source: GLS, volume 4, Chapter 2, Lemmas 13.3–13.4 and the following
construction; Chapter 4, Lemmas 3.4(d) and 3.5(c).
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The ambient image of O₂(M ∩ H), with normality relative to M ∩ H. -/
@[expose] public def localTwoCore (M H : Subgroup G) : Subgroup G :=
  (pCore 2 (M ⊓ H : Subgroup G)).map (M ⊓ H).subtype

/-- T = O₂(M ∩ Lᵤ). -/
@[expose] public def localT (Z : Set G) (M : Subgroup G) (u : G) : Subgroup G :=
  localTwoCore M (centralizerClosure Z u)

/-- V = O₂(M ∩ L_B), for the source's cyclic odd subgroup B. -/
@[expose] public def localV (Z : Set G) (M B : Subgroup G) : Subgroup G :=
  localTwoCore M (distinguishedCentralizer Z B)

/-- U = N_V(A⟨u⟩), where A is the distinguished subgroup in M. -/
@[expose] public def localU (Z : Set G) (M B : Subgroup G) (u : G) : Subgroup G :=
  localV Z M B ⊓ normalizer (closure (Z ∩ (M : Set G)) ⊔ zpowers u : Set G)

/-- The conjugation action of u on the second distinguished centralizer. -/
@[expose] public def secondInvolution {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}
    (d : SecondCentralizerData Z M z t u n) :
    MulAut (distinguishedCentralizer Z d.torus) :=
  (distinguishedCentralizer Z d.torus).normalizerMonoidHom ⟨u, d.normalizes⟩

/-- The automorphisms fixing the fixed subgroup pointwise and commuting
with the involution are precisely candidates 1 and the involution. -/
@[expose] public def FixedCentralizerRigidity
    {H : Type*} [Group H] (a : MulAut H) : Prop :=
  ∀ b : MulAut H, Commute b a → (∀ x : H, a x = x → b x = x) → b = 1 ∨ b = a

/-- The remaining source placement and intrinsic local-action inputs.
The producer must establish these for the specified two-cores and normalizer,
including the homocyclic subgroups and their common involutions. -/
public structure HomocyclicLocalData
    (Z : Set G) (M : Subgroup G) (z t u : G) (n : ℕ)
    (d : SecondCentralizerData Z M z t u n) where
  sylow_T : ∃ S : Sylow 2 (centralizerClosure Z u),
    (S : Subgroup (centralizerClosure Z u)).map (centralizerClosure Z u).subtype = localT Z M u
  sylow_V : ∃ S : Sylow 2 (distinguishedCentralizer Z d.torus),
    (S : Subgroup (distinguishedCentralizer Z d.torus)).map
      (distinguishedCentralizer Z d.torus).subtype = localV Z M d.torus
  U_normalizes_T : localU Z M d.torus u ≤ normalizer (localT Z M u : Set G)
  torus_moves_T : ⁅localT Z M u, d.torus⁆ ≠ ⊥
  torus_fixes_frattini : (frattini (localT Z M u)).map (localT Z M u).subtype ≤
    centralizer (d.torus : Set G)
  pair_normalizes_U : residualPairStabilizer M t ⊓ centralizerClosure Z u ≤
    normalizer (localU Z M d.torus u : Set G)
  irreducible : ∀ W : Subgroup G, W ≤ localT Z M u →
    residualPairStabilizer M t ⊓ centralizerClosure Z u ≤ normalizer (W : Set G) →
    W ≤ (frattini (localT Z M u)).map (localT Z M u).subtype ∨
      W ⊔ (frattini (localT Z M u)).map (localT Z M u).subtype = localT Z M u
  U_homocyclic : Nonempty (localU Z M d.torus u ≃* StandardHomocyclicCover (Fin n) 4)
  T₀ : Subgroup G
  T₀_le : T₀ ≤ localT Z M u
  T₀_homocyclic : Nonempty (T₀ ≃* StandardHomocyclicCover (Fin n) 4)
  intersection : T₀ ⊓ localU Z M d.torus u = closure (Z ∩ (M : Set G))
  T₀_involutions : ∀ x : T₀, (x : G) ∈ closure (Z ∩ (M : Set G)) ↔ x ^ 2 = 1
  U_involutions : ∀ x : localU Z M d.torus u,
    (x : G) ∈ closure (Z ∩ (M : Set G)) ↔ x ^ 2 = 1

end BenderSuzuki.ZD.UnitaryExclusion
