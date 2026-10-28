module

public import Theory.Representation.SymplecticConjugatePair
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The actual binary normalizer of the derived symplectic pair

The ambient model is the normalizer, inside the binary general linear group,
of the image of the genuine derived symplectic group. Its tautological action
is faithful. This definition includes possible coefficient scalars and keeps
the binary full group distinct from its derived subgroup.

The two predicates describe preservation or interchange of the actual two
coordinate summands. No assertion that every normalizer element permutes them,
and no numerical bound, is built into this model.

Source: the paired-module setup of Aschbacher–Smith H.7, printed pp.388–389,
and before Table 7.1.1 on p.696 of `refs/quasithin.pdf`.
-/

@[expose] public section

namespace SymplecticConjugatePair.Ambient
open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Express the representation by its actual invertible linear operators. -/
noncomputable def linearAction (ρ : Representation (ZMod 2) G V) :
    G →* (V ≃ₗ[ZMod 2] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
    ρ.asGroupHom

@[simp] lemma linearAction_apply (ρ : Representation (ZMod 2) G V) (g : G) (v : V) :
    linearAction ρ g v = ρ g v := rfl

lemma linearAction_injective (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) : Function.Injective (linearAction ρ) := by
  intro g h he
  apply hρ
  ext v
  exact congrArg (fun e : V ≃ₗ[ZMod 2] V => e v) he

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

/-- The literal image of the genuine derived matrix group. -/
noncomputable def derivedImage (τ : MulAut (Sp F)) :
    Subgroup (Space F ≃ₗ[ZMod 2] Space F) := (linearAction (derivedPair τ)).range

/-- All binary linear operators normalizing that actual image. -/
noncomputable def pairedNormalizer (τ : MulAut (Sp F)) :
    Subgroup (Space F ≃ₗ[ZMod 2] Space F) := Subgroup.normalizer (derivedImage τ)

/-- Evaluation on the paired space, with the normalizer as acting group. -/
noncomputable def normalizerAction (τ : MulAut (Sp F)) :
    Representation (ZMod 2) (pairedNormalizer τ) (Space F) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (pairedNormalizer τ).subtype

lemma normalizerAction_injective (τ : MulAut (Sp F)) :
    Function.Injective (normalizerAction τ) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact LinearMap.congr_fun he v

@[simp] lemma mem_firstSummand (v : Space F) : v ∈ firstSummand ↔ v.2 = 0 := by
  constructor
  · rintro ⟨u, rfl⟩; rfl
  · intro h; exact ⟨v.1, Prod.ext rfl h.symm⟩

@[simp] lemma mem_secondSummand (v : Space F) : v ∈ secondSummand ↔ v.1 = 0 := by
  constructor
  · rintro ⟨u, rfl⟩; rfl
  · intro h; exact ⟨v.2, Prod.ext h.symm rfl⟩

lemma firstSummand_ne_bot : firstSummand (F := F) ≠ ⊥ := by
  intro h
  have hv : ((fun _ => (1 : F)), (0 : Vector F)) ∈ firstSummand :=
    (mem_firstSummand _).mpr rfl
  rw [h, Submodule.mem_bot] at hv
  have := congrArg (fun v : Space F => v.1 (Sum.inl 0)) hv
  exact one_ne_zero this

/-- The actual first-summand stabilizer. -/
noncomputable abbrev summandStabilizer (ρ : Representation (ZMod 2) G (Space F)) :=
  subspaceStabilizer ρ firstSummand

/-- The operator interchanges both actual coordinate summands. -/
def SwapsSummands (ρ : Representation (ZMod 2) G (Space F)) (g : G) : Prop :=
  (∀ v ∈ firstSummand, ρ g v ∈ secondSummand) ∧
  (∀ v ∈ secondSummand, ρ g v ∈ firstSummand)

/-- The action preserves the unordered pair of coordinate summands. -/
def PermutesSummands (ρ : Representation (ZMod 2) G (Space F)) : Prop :=
  ∀ g, (g ∈ summandStabilizer ρ ∧ g ∈ subspaceStabilizer ρ secondSummand) ∨
    SwapsSummands ρ g

end SymplecticConjugatePair.Ambient
