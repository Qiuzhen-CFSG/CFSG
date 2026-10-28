module
public import Theory.SpecificGroups.SymplecticFour.SmallNaturalCommutator
public import Theory.SpecificGroups.SymplecticFour.SmallMoverKernel

/-!
# Small displacement in the full semilinear natural action

An actor with fixed index at most four on the field-four natural module
lies in the actual symplectic component. Orthogonality identifies its
fixed codimension and displacement dimension. The equivariant embedding
therefore gives equality of the actual commutator order and centralizer
index, without an elementary-abelian assumption on the actor.

Source: MS93 (5.9), printed p.920. The original T0 application is in
Sp4Four.SourceComparison.OriginalSmallDisplacement and
GenerationTwoSymplecticStrictKernel.
-/

public noncomputable section
open Subgroup Representation
open Theory.SpecificGroups.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour
variable {F G J : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G] [Group J] [Finite J]

/-- Small fixed codimension forces an inner action, and symplectic duality
identifies its full commutator order with its fixed index. -/
theorem small_natural_commutator_card_eq_index
    (hF : Nat.card F = 4) (B : Subgroup J) [B.Normal]
    (hcent : centralizer (B : Set J) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) J (Vector F))
    (hB : ∀ b : B, ∀ v, ρ (b:J) v = symplecticNatural 2 (e b) v)
    (N A : Subgroup G) (j : Multiplicative (Vector F) →* G)
    (hj : Function.Injective j) (hjr : j.range = N) (α : A →* J)
    (hact : ∀ (a : A) v,
      j (Multiplicative.ofAdd (ρ (α a) v)) = a.val*j (Multiplicative.ofAdd v)*a.val⁻¹)
    (hsmall : (centralizer (A : Set G)).relIndex N ≤ 4) :
    Nat.card (⁅A,N⁆ : Subgroup G) = (centralizer (A : Set G)).relIndex N := by
  have hi := Representation.BinaryOffender.embedded_centralizer_index ρ N A j hj hjr α hact
  have hquot : Nat.card (Vector F ⧸ Representation.BinaryOffender.fixedSpace ρ α.range) ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact hi ▸ hsmall
  have hinner := Representation.small_actor_le_symplectic_component hF B hcent e ρ hB α.range hquot
  let f : A →* Sp F := e.toMonoidHom.comp (α.codRestrict B (fun a => hinner ⟨a,rfl⟩))
  have hact' (a : A) v : j (Multiplicative.ofAdd (f a • v)) =
      a.val*j (Multiplicative.ofAdd v)*a.val⁻¹ := by
    rw [←hact]
    congr 2
    exact (hB ⟨α a,hinner ⟨a,rfl⟩⟩ v).symm
  have he := RootHyperplaneComparison.commutator_eq_displacement_image A N j hjr f hact'
  rw [he,card_map_of_injective hj]
  let σ := Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  have hi' := Representation.BinaryOffender.embedded_centralizer_index σ N A j hj hjr f hact'
  have hquot' : 2 ^ Representation.BinaryOffender.fixedCodim σ f.range =
      Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace f.range) := by
    let C := TwoLocalCover.fixedSpace f.range
    have hfixed : Representation.BinaryOffender.fixedSpace σ f.range = C.restrictScalars (ZMod 2) := by
      ext v
      exact ⟨fun h g hg => h ⟨g,hg⟩,fun h g => h g.val g.property⟩
    change 2 ^ Module.finrank (ZMod 2) (Vector F ⧸ Representation.BinaryOffender.fixedSpace σ f.range) = _
    rw [hfixed]
    have hc := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) C).toEquiv
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
    exact hc
  rw [hi',hquot',fixed_quotient_card]
  change Nat.card (displacementSpace f.range) = _
  exact Module.natCard_eq_pow_finrank (K := F) (V := displacementSpace f.range)
end Theory.SpecificGroups.SymplecticFour
