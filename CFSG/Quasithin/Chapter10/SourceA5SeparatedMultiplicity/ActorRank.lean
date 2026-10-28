module
public import Theory.Representation.AlternatingFive.SeparatedActorRank
public import Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
public import CFSG.Quasithin.ChapterD.Section02.Defs

/-!
# The separated-support multiplicity bound for the original cubic actor

Choose an actual starred cubic actor. Its faithful conjugation action on the
marked A₅ square is transported through the proved S₅ wreath isomorphism.
If it preserves the two support blocks, the homogeneous module estimates
bound each projected rank. If it exchanges the blocks, its rank is at most
three and the displacement of an entire block forces multiplicity at most one.
Thus the original cubic ratio bound gives multiplicity at most two.

This specializes the multiplicity step of Aschbacher–Smith D.3.9 and D.3.21,
pp.199–201 and 204–207, for the full/local module passage in Chapter 10.
The homogeneous coordinates and concrete intertwiner displacement estimates
are supplied by the separated-coordinate and amplified-module owners; the
faithfulness of the starred conjugation action is the independent D.2.13
input. These data are retained explicitly, not inferred from the ratio alone.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
open Representation.AlternatingFive.SeparatedActorRank
open Theory.SpecificGroups.SymmetricFive.ProjectedElementaryRank
open Theory.GroupTheory.WreathTwoElementaryRank
namespace CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity
open Theory.SpecificGroups.Alternating
variable {A V : Type*} [Group A] [Finite A]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Literal invariant blocks and their amplified displacement bounds, using
exactly the two permutation coordinates of the given wreath action. -/
structure PreservedBlocks (τ : Representation (ZMod 2) A V)
    (f : A →* W Sym) (k : ℕ) (hb : ∀ a, (f a).right = 1) where
  first : Subrepresentation τ
  second : Subrepresentation τ
  coordinates : V ≃ₗ[ZMod 2] first.toSubmodule × second.toSubmodule
  intertwines : ∀ a v, coordinates (τ a v) =
    (first.toRepresentation a (coordinates v).1,
      second.toRepresentation a (coordinates v).2)
  first_nontrivial : ∀ a, (f a).left 1 ≠ 1 →
    k ≤ operatorFixedCodim (first.toRepresentation a)
  first_inner : ∀ a, (f a).left 1 ≠ 1 → (f a).left 1 ∈ Alt →
    2 * k ≤ operatorFixedCodim (first.toRepresentation a)
  second_nontrivial : ∀ a, (f a).left turn ≠ 1 →
    k ≤ operatorFixedCodim (second.toRepresentation a)
  second_inner : ∀ a, (f a).left turn ≠ 1 → (f a).left turn ∈ Alt →
    2 * k ≤ operatorFixedCodim (second.toRepresentation a)

/-- The group homomorphism is the marked action on A₅², rather than a new
faithful action invented from the module coordinates. -/
structure SeparatedActorData (τ : Representation (ZMod 2) A V) (k : ℕ) where
  conjugation : A →* MulAut FiveSquareAutomorphisms.Pair
  faithful : Function.Injective conjugation
  preserved : ∀ hb : ∀ a, (FiveSquareAutomorphisms.wreathEquiv.symm (conjugation a)).right = 1,
    Nonempty (PreservedBlocks τ
      (FiveSquareAutomorphisms.wreathEquiv.symm.toMonoidHom.comp conjugation) k hb)
  exchanged : ∀ a : A, (FiveSquareAutomorphisms.wreathEquiv.symm (conjugation a)).right ≠ 1 →
    ∃ B : Submodule (ZMod 2) V, Module.finrank (ZMod 2) B = 4 * k ∧
      Disjoint B (B.map (τ a))

variable [IsElementaryAbelian 2 A] [Nontrivial A]

/-- The faithful marked actor and literal block data discharge the multiplicity
bound as soon as its actual fixed-codimension inequality is available. -/
theorem multiplicity_le_two_of_actor_data
    (τ : Representation (ZMod 2) A V) (k : ℕ) (d : SeparatedActorData τ k)
    (hsmall : fixedCodim τ ⊤ ≤ 2 * primeRank 2 A) : k ≤ 2 := by
  classical
  let f := FiveSquareAutomorphisms.wreathEquiv.symm.toMonoidHom.comp d.conjugation
  have hf : Function.Injective f := FiveSquareAutomorphisms.wreathEquiv.symm.injective.comp d.faithful
  by_cases hb : ∀ a, (f a).right = 1
  · obtain ⟨b⟩ := d.preserved hb
    let p := preservedPairHom f hb
    let f₁ := (MonoidHom.fst Sym Sym).comp p
    let f₂ := (MonoidHom.snd Sym Sym).comp p
    have hp : Function.Injective (f₁.prod f₂) := by
      exact preservedPairHom_injective f hf hb
    have hp₁ (a : A) : f₁ a = (f a).left 1 :=
      congrArg Prod.fst (preservedPairHom_apply f hb a)
    have hp₂ (a : A) : f₂ a = (f a).left turn :=
      congrArg Prod.snd (preservedPairHom_apply f hb a)
    apply multiplicity_le_two_of_coordinates τ b.first.toRepresentation
      b.second.toRepresentation b.coordinates b.intertwines f₁ f₂ hp k
      (fun a ha => b.first_nontrivial a (hp₁ a ▸ ha))
      (fun a ha he => b.first_inner a (hp₁ a ▸ ha) (hp₁ a ▸ he))
      (fun a ha => b.second_nontrivial a (hp₂ a ▸ ha))
      (fun a ha he => b.second_inner a (hp₂ a ▸ ha) (hp₂ a ▸ he)) hsmall
  · push Not at hb
    obtain ⟨a, ha⟩ := hb
    obtain ⟨B, hd, hB⟩ := d.exchanged a ha
    have hh := multiplicity_le_one_of_swapping τ f hf k B hd a ha hB hsmall
    omega

variable {Q : Type*} [Group Q] [Finite Q]

/-- Apply the estimate to the exact starred actor in the full quotient module. -/
theorem source_separated_multiplicity_le_two_of_starred_actor
    (ρ : Representation (ZMod 2) Q V) {E : Subgroup Q}
    (hE : E ∈ ChapterD.QhatStar ρ) (k : ℕ)
    (d : SeparatedActorData (ρ.comp E.subtype) k) : k ≤ 2 := by
  have he : IsElementaryTwo E := hE.1.2.1
  let : IsElementaryAbelian 2 E := he.2
  let : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).mpr he.1
  have hsmall : fixedCodim ρ E ≤ 2 * rank E :=
    (actionRatio_le_nat_iff ρ he 2).mp (hE.1.2.2.2.trans_le hE.1.1)
  have hc : fixedCodim (ρ.comp E.subtype) ⊤ = fixedCodim ρ E := by
    unfold fixedCodim
    rw [fixedSpace_comp_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hr : rank E = primeRank 2 E :=
    IsElementaryAbelian.log_card_eq_primeRank (p := 2) E
  apply multiplicity_le_two_of_actor_data (ρ.comp E.subtype) k d
  rwa [hc, ← hr]

/-- The finite minimum supplies the starred actor; all independent geometric
inputs remain attached to that same actor. -/
theorem source_separated_multiplicity_le_two_of_cubicRatio
    (ρ : Representation (ZMod 2) Q V) (k : ℕ) (hq : cubicRatio ρ ≤ 2)
    (hdata : ∀ E, E ∈ ChapterD.QhatStar ρ →
      Nonempty (SeparatedActorData (ρ.comp E.subtype) k)) : k ≤ 2 := by
  obtain ⟨E, hE⟩ := (ChapterD.QhatStar_nonempty_iff ρ).mpr hq
  obtain ⟨d⟩ := hdata E hE
  exact source_separated_multiplicity_le_two_of_starred_actor ρ hE k d

end CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity
