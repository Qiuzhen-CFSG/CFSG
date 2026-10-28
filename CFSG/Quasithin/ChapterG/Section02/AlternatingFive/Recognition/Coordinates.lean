module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.Action
public import Theory.GroupAction.CommonFixedNormalizer

/-!
# From genuine binary recognition to the shared natural-layer output

Canonical quotient coordinates identify the actual subgroup images with
binary subspaces. Equivariance on representatives uniquely determines
the full quotient action. A genuine equivariant linear isomorphism to s
natural planes therefore produces the shared NaturalLayer, with its
representative-level identity and its original starred model.

The fixed-space bridge converts a fixed-space theorem on U* to the common
fixed subgroup of the original U-action. These are transport results;
the projective-map construction and the G.1.3 implication must supply
the linear coordinates and fixed-space premise before source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.1.3, G.1.5(2), and G.2.4(6), printed pp.327–328 and 334.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
variable {G : Type*} [Group G] {D : Setup G} {g : G}
  [((S₂ D g).subgroupOf (D.S g)).Normal]
  [IsElementaryAbelian 2 (UpperQuotient D g)]

/-- The literal subgroup image viewed as a binary subspace. -/
def upperSubspace (D : Setup G) (g : G)
    [((S₂ D g).subgroupOf (D.S g)).Normal]
    [IsElementaryAbelian 2 (UpperQuotient D g)] (A : Subgroup G) :
    Submodule (ZMod 2) (Additive (UpperQuotient D g)) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (upperImage D g A))

theorem upper_imageSpace_eq
    (hILT : D.I g ≤ D.LT) (hstar : D.star (D.I g) = D.star D.L)
    (σ : Representation (ZMod 2) (D.star D.L) (Additive (UpperQuotient D g)))
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
      (σ.comp (upperStarProjection D g hILT hstar)))
    (hq : ∀ a : D.S g, (c.coordinates a).toAdd =
      Additive.ofMul (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) a))
    (A : Subgroup G) : c.imageSpace A = upperSubspace D g A := by
  ext v
  rw [c.mem_imageSpace_iff]
  change (∃ a : D.S g, (a : G) ∈ A ∧ (c.coordinates a).toAdd = v) ↔
    ∃ a : D.S g, (a : G) ∈ A ∧
      QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) a = v.toMul
  simp only [hq]
  rfl

/-- Representative-level compatibility uniquely determines the action on
the quotient and identifies it with the descended binary representation. -/
theorem upper_action_eq_binary
    (hILT : D.I g ≤ D.LT) (hstar : D.star (D.I g) = D.star D.L)
    (σ : Representation (ZMod 2) (D.star D.L) (Additive (UpperQuotient D g)))
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
      (σ.comp (upperStarProjection D g hILT hstar)))
    (hq : ∀ a : D.S g, (c.coordinates a).toAdd =
      Additive.ofMul (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) a))
    (α : D.I g →* MulAut (UpperQuotient D g))
    (hα : ∀ i : D.I g, ∀ a : D.S g,
      α i (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) a) =
        QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) (coreConjugate D g i a))
    (i : D.I g) (x : UpperQuotient D g) :
    Additive.ofMul (α i x) =
      σ (upperStarProjection D g hILT hstar i) (Additive.ofMul x) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [hα, ← hq]
  exact (c.equivariant i a).trans (congrArg (σ (upperStarProjection D g hILT hstar i)) (hq a))

/-- Genuine equivariant binary coordinates are converted to the shared
NaturalLayer specification, with the original action on representatives. -/
theorem naturalLayer_of_equivariant [Finite G] (d : Hypothesis D g)
    (hLI : D.L ≤ D.I g)
    (hILT : D.I g ≤ D.LT) (hstar : D.star (D.I g) = D.star D.L)
    (σ : Representation (ZMod 2) (D.star D.L) (Additive (UpperQuotient D g)))
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
      (σ.comp (upperStarProjection D g hILT hstar)))
    (hq : ∀ a : D.S g, (c.coordinates a).toAdd =
      Additive.ofMul (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) a))
    {F : Type*} [Field F] [Module (ZMod 2) F] (hF : Nat.card F = 4)
    (model : D.star D.L ≃* SL(2, F)) (s : ℕ)
    (e : Additive (UpperQuotient D g) ≃ₗ[ZMod 2] (Fin s → Fin 2 → F))
    (he : ∀ a v j, e (σ a v) j = (model a).val *ᵥ (e v j)) :
    Nonempty (NaturalLayer D g F s hLI) := by
  obtain ⟨α, hα⟩ := exists_quotient_conjugation_action (D.I g) (D.S g) (S₂ D g)
    (I_normalizes_core D g)
    (le_normalizer_iff_commutator_le_left.mpr ((d.second_commutator hLI).trans le_sup_left))
    inferInstance
  refine ⟨{
    field_card := hF
    model := model
    coordinates := e.toAddEquiv.toMultiplicativeRight
    action := α
    action_mk := hα
    equivariant := ?_ }⟩
  intro l x
  change e (Additive.ofMul (α ⟨l, hLI l.property⟩ x)) =
    fun j => (model (starProjection D l)).val *ᵥ e (Additive.ofMul x) j
  rw [upper_action_eq_binary hILT hstar σ c hq α hα]
  change e (σ (upperStarProjection D g hILT hstar (inclusion hLI l)) (Additive.ofMul x)) = _
  rw [upperStarProjection_on_L]
  exact funext (he (starProjection D l) (Additive.ofMul x))

/-- The starred fixed-space conclusion is the common fixed subgroup of the
original U-action, with its original lifts and literal quotient image. -/
theorem upperImage_eq_fixed_of_binary
    (hILT : D.I g ≤ D.LT) (hstar : D.star (D.I g) = D.star D.L)
    (σ : Representation (ZMod 2) (D.star D.L) (Additive (UpperQuotient D g)))
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
      (σ.comp (upperStarProjection D g hILT hstar)))
    (hq : ∀ a : D.S g, (c.coordinates a).toAdd =
      Additive.ofMul (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) a))
    (hfixed : ∀ v, v ∈ c.imageSpace (D.W g) ↔
      ∀ a ∈ (D.star D.U).subgroupOf (D.star D.L), σ a v = v)
    (α : D.I g →* MulAut (UpperQuotient D g))
    (hα : ∀ i : D.I g, ∀ a : D.S g,
      α i (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) a) =
        QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) (coreConjugate D g i a)) :
    upperImage D g (D.W g) = α.commonFixed (D.U.subgroupOf (D.I g)) := by
  ext x
  have hi : x ∈ upperImage D g (D.W g) ↔
      Additive.ofMul x ∈ c.imageSpace (D.W g) := by
    rw [upper_imageSpace_eq hILT hstar σ c hq]
    rfl
  rw [hi, hfixed, MonoidHom.mem_commonFixed]
  constructor
  · intro hx u hu
    apply Additive.ofMul.injective
    rw [upper_action_eq_binary hILT hstar σ c hq α hα]
    apply hx
    rw [← upperStarProjection_map D g hILT hstar D.U le_sup_left]
    exact mem_map_of_mem _ hu
  · intro hx a ha
    rw [← upperStarProjection_map D g hILT hstar D.U le_sup_left] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    rw [← upper_action_eq_binary hILT hstar σ c hq α hα, hx u hu]

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
