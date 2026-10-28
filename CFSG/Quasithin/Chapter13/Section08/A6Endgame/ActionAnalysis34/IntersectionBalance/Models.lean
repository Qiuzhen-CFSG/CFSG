module
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.IntersectionBalance.Spaces
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.MarkedQuotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Marked.ChiefFactors
import Mathlib.Tactic

/-!
# Marked natural and augmentation coordinates for the source product

An equivariant equivalence carries the source fixed space and commutator
image to their coordinate counterparts. The actual image of V₃ marks the
canonical plane (or the augmentation weight-four plane). Thus U₁V₃ has
pointwise fixer D and codimension two. The corrected radical displacement
identities then give equality with the image of [UH,Uα].

All subgroup images use the literal quotient UH/V₁. The kernel line lies in
U₁ by its fixed-space preimage definition, so quotienting by that line
preserves the codimension of U₁V₃. No ambient normality is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.8.34, printed p.968 (PDF p.985), second paragraph.
-/

public section
open Subgroup Module Representation BinaryPermutation
open Representation.SixLetterRadicalDisplacement
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.IntersectionBalance
open scoped IsMulCommutative

private theorem map_fixed {A B X Y : Type*} [Group A] [Group B]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) A X) (τ : Representation (ZMod 2) B Y)
    (e : A ≃* B) (c : X ≃ₗ[ZMod 2] Y)
    (he : ∀ g v, c (ρ g v) = τ (e g) (c v)) :
    ρ.invariants.map c.toLinearMap = τ.invariants := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ g
    change τ g (c x) = c x
    simpa only [e.apply_symm_apply] using (he (e.symm g) x).symm.trans (congrArg c (hx _))
  · intro hy
    refine ⟨c.symm y, ?_, c.apply_symm_apply y⟩
    intro g
    apply c.injective
    rw [he, c.apply_symm_apply, hy]

private theorem map_displacement {A B X Y : Type*} [Group A] [Group B]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) A X) (τ : Representation (ZMod 2) B Y)
    (e : A ≃* B) (c : X ≃ₗ[ZMod 2] Y)
    (he : ∀ g v, c (ρ g v) = τ (e g) (c v)) (E : Subgroup A) :
    (Coinvariants.ker (ρ.comp E.subtype)).map c.toLinearMap =
      Coinvariants.ker (τ.comp (E.map e.toMonoidHom).subtype) := by
  rw [Coinvariants.ker, Submodule.map_span, Coinvariants.ker]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨⟨g, x⟩, rfl⟩, rfl⟩
    refine ⟨(⟨e g, mem_map_of_mem _ g.property⟩, c x), ?_⟩
    exact (map_sub c _ _).trans (congrArg (fun z => z - c x) (he g x)) |>.symm
  · rintro ⟨⟨g, y⟩, rfl⟩
    obtain ⟨a, ha, hg⟩ := g.property
    refine ⟨ρ a (c.symm y) - c.symm y, ⟨(⟨a, ha⟩, c.symm y), rfl⟩, ?_⟩
    change c (ρ a (c.symm y) - c.symm y) = _
    rw [map_sub, he, c.apply_symm_apply]
    exact congrArg (fun z => τ z y - y) hg

private theorem quotient_dim_map {X Y : Type*}
    [AddCommGroup X] [Module (ZMod 2) X] [Module.Finite (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] [Module.Finite (ZMod 2) Y]
    (c : X ≃ₗ[ZMod 2] Y) (K : Submodule (ZMod 2) X) :
    finrank (ZMod 2) (X ⧸ K) = finrank (ZMod 2) (Y ⧸ K.map c.toLinearMap) := by
  have hX := K.finrank_quotient_add_finrank
  have hY := (K.map c.toLinearMap).finrank_quotient_add_finrank
  rw [c.finrank_map_eq, ← c.finrank_eq] at hY
  omega

private theorem natural_fixed : (naturalRepresentation (Fin 6)).invariants = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  change v = 0
  exact ComponentSieve.SixAndG2.NaturalSix.Marked.residual_fixed_eq_zero (fun g _ => hv g)

variable {G : Type*} [Group G]

/-- The linear commutator of the actual tilde action is the image of the ambient commutator. -/
theorem tilde_displacement (H UH V₁ B : Subgroup G) [IsElementaryAbelian 2 UH]
    (a : SolvableExclusion.Five.StarAction H UH V₁) (hB : B ≤ H) :
    Coinvariants.ker ((tildeRepresentation H UH V₁ a).comp (Source.starImage H B).subtype) =
      quotientSpace UH V₁ ⁅UH, B⁆ := by
  rw [quotientSpace, ← a.commutatorAction_eq_tildeImage B hB]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change (a.action g v.toMul) / v.toMul ∈ commutatorAction (a.actors B) _
    have hm : v.toMul⁻¹ * a.action g v.toMul ∈ commutatorAction (a.actors B) _ :=
      Subgroup.subset_closure
        ⟨⟨a.action g, mem_map_of_mem _ g.property⟩, v.toMul, trivial, rfl⟩
    simpa only [div_eq_mul_inv, mul_comm] using hm
  · change commutatorAction (a.actors B) _ ≤
      (Coinvariants.ker ((tildeRepresentation H UH V₁ a).comp
        (Source.starImage H B).subtype)).toAddSubgroup.toSubgroup'
    rw [commutatorAction, commutatorSubgroup, Subgroup.closure_le]
    rintro _ ⟨g, v, _, rfl⟩
    obtain ⟨b, hb, he⟩ := g.property
    have hm := Coinvariants.sub_mem_ker
      (ρ := (tildeRepresentation H UH V₁ a).comp (Source.starImage H B).subtype)
      ⟨b, hb⟩ (Additive.ofMul v)
    change (a.action b v) / v ∈ _ at hm
    change v⁻¹ * (g : MulAut _) v ∈ _
    rw [← he]
    change Additive.ofMul (v⁻¹ * a.action b v) ∈ Coinvariants.ker _
    change Additive.ofMul ((a.action b v) / v) ∈ Coinvariants.ker _ at hm
    convert hm using 1
    congr 1
    simp only [div_eq_mul_inv, mul_comm]

/-- Products of actual subgroups inside UH become sums in its quotient. -/
theorem quotientSpace_sup (UH V₁ X Y : Subgroup G) [IsElementaryAbelian 2 UH]
    (hX : X ≤ UH) (hY : Y ≤ UH) :
    quotientSpace UH V₁ (X ⊔ Y) = quotientSpace UH V₁ X ⊔ quotientSpace UH V₁ Y := by
  unfold quotientSpace SolvableExclusion.tildeImage
  rw [subgroupOf_sup hX hY, Subgroup.map_sup, (binarySpace (K := UH ⧸ V₁.subgroupOf UH)).map_sup]

/-- Factoring out V₁ does not alter the remaining codimension when V₁ is contained in K. -/
theorem quotient_codimension [Finite G] (UH V₁ K : Subgroup G) [IsElementaryAbelian 2 UH]
    (hK : K ≤ UH) (hV : V₁ ≤ K) :
    finrank (ZMod 2) (Additive UH ⧸ inside UH K) =
      finrank (ZMod 2) (Additive (UH ⧸ V₁.subgroupOf UH) ⧸ quotientSpace UH V₁ K) := by
  have h := (quotientSpace UH V₁ K).finrank_quotient_add_finrank
  rw [finrank_quotientSpace, inf_eq_left.mpr hK, finrank_additive] at h
  have hc : Nat.card (UH ⧸ V₁.subgroupOf UH) = V₁.relIndex UH := rfl
  rw [hc] at h
  rw [finrank_quotient_inside UH K hK]
  have hm := relIndex_mul_relIndex V₁ K UH hV hK
  have hp : V₁.relIndex K = 2 ^ Nat.log 2 (V₁.relIndex K) := by
    let : IsElementaryAbelian 2 K := IsElementaryAbelian.of_le hK
    rw [log_relIndex_eq_quotient_finrank K V₁, ← relIndex_eq_two_pow_quotient_finrank]
  have hq : K.relIndex UH = 2 ^ Nat.log 2 (K.relIndex UH) := by
    rw [log_relIndex_eq_quotient_finrank UH K, ← relIndex_eq_two_pow_quotient_finrank]
  rw [hp, hq, ← pow_add] at hm
  have he := congrArg (Nat.log 2) hm
  rw [Nat.log_pow Nat.one_lt_two] at he
  omega

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.IntersectionBalance

namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.IntersectionBalance
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- Coordinates for the two source alternatives, with one actor marking and the actual V₃ image.
No commutator equality or dimension bound is part of these data. -/
def CompatibleModel (H V₃ V₁ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* S) : Prop :=
  (∃ c : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6),
    (∀ g v, c (tildeRepresentation H _ V₁ a g v) = naturalRepresentation (Fin 6) (e g) (c v)) ∧
    (quotientSpace (Source.UH H V₃) V₁ V₃).map c.toLinearMap = canonicalPlane) ∨
  (∃ c : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] U,
    (∀ g v, c (tildeRepresentation H _ V₁ a g v) = coreRepresentation (Fin 6) (e g) (c v)) ∧
    (quotientSpace (Source.UH H V₃) V₁ V₃).map c.toLinearMap = W)

/-- Construct the source coordinate input from the marked natural equivalence. -/
theorem CompatibleModel.of_natural (H V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* S)
    (c : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
    (he : ∀ g v, c (tildeRepresentation H _ V₁ a g v) =
      naturalRepresentation (Fin 6) (e g) (c v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map c.toLinearMap = canonicalPlane) :
    CompatibleModel H V₃ V₁ a e := Or.inl ⟨c, he, hp⟩

/-- Construct the source coordinate input from the marked augmentation equivalence. -/
theorem CompatibleModel.of_augmentation (H V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* S)
    (c : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] U)
    (he : ∀ g v, c (tildeRepresentation H _ V₁ a g v) =
      coreRepresentation (Fin 6) (e g) (c v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map c.toLinearMap = W) :
    CompatibleModel H V₃ V₁ a e := Or.inr ⟨c, he, hp⟩

/-- Forget the distinguished plane while preserving the actual actor and
equivariant module comparison. This is the public elimination interface used
to transport the same model to the endpoint in the line-containment proof. -/
theorem CompatibleModel.action_cases (H V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* S) (hm : CompatibleModel H V₃ V₁ a e) :
    (∃ c : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6),
      ∀ g v, c (tildeRepresentation H _ V₁ a g v) =
        naturalRepresentation (Fin 6) (e g) (c v)) ∨
    (∃ c : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] U,
      ∀ g v, c (tildeRepresentation H _ V₁ a g v) =
        coreRepresentation (Fin 6) (e g) (c v)) := by
  rcases hm with ⟨c, he, _⟩ | ⟨c, he, _⟩
  · exact Or.inl ⟨c, he⟩
  · exact Or.inr ⟨c, he⟩

private theorem map_Uone_sup {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (H V₃ V₁ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* S) (τ : Representation (ZMod 2) S Y)
    (c : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] Y)
    (he : ∀ g v, c (tildeRepresentation H _ V₁ a g v) = τ (e g) (c v)) :
    (quotientSpace (Source.UH H V₃) V₁ (Uone H _ V₁ a ⊔ V₃)).map c.toLinearMap =
      τ.invariants ⊔ (quotientSpace (Source.UH H V₃) V₁ V₃).map c.toLinearMap := by
  rw [quotientSpace_sup (Source.UH H V₃) V₁ _ V₃ (Uone_le H _ V₁ a) (le_conjugateSpanBy V₃ H),
    Submodule.map_sup, quotientSpace_Uone, map_fixed _ τ e c he]

private theorem fixes_transport {A B X Y : Type*} [Group A] [Group B]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) A X) (τ : Representation (ZMod 2) B Y)
    (e : A ≃* B) (c : X ≃ₗ[ZMod 2] Y)
    (he : ∀ g v, c (ρ g v) = τ (e g) (c v)) (K : Submodule (ZMod 2) X) (g : A) :
    (∀ v ∈ K, ρ g v = v) ↔ (∀ w ∈ K.map c.toLinearMap, τ (e g) w = w) := by
  constructor
  · rintro h _ ⟨v, hv, rfl⟩
    exact (he g v).symm.trans (congrArg c (h v hv))
  · intro h v hv
    apply c.injective
    exact (he g v).trans (h _ (Submodule.mem_map_of_mem hv))

/-- The fixed-space product has the source rank-two quotient and the radical D as pointwise fixer. -/
theorem model_geometry [Finite G] (H V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* S) (hm : CompatibleModel H V₃ V₁ a e)
    (hline : V₁ ≤ Source.UH H V₃) :
    (∀ g, (∀ v ∈ quotientSpace (Source.UH H V₃) V₁ (Uone H _ V₁ a ⊔ V₃),
      tildeRepresentation H _ V₁ a g v = v) ↔ e g ∈ D) ∧
    finrank (ZMod 2) (Additive (Source.UH H V₃) ⧸
      inside (Source.UH H V₃) (Uone H _ V₁ a ⊔ V₃)) = 2 := by
  have hK := sup_le (Uone_le H (Source.UH H V₃) V₁ a) (le_conjugateSpanBy V₃ H)
  have hV : V₁ ≤ Uone H (Source.UH H V₃) V₁ a ⊔ V₃ := (line_le_Uone H (Source.UH H V₃) V₁ a hline).trans le_sup_left
  rcases hm with ⟨c, he, hp⟩ | ⟨c, he, hp⟩
  · have hsum := map_Uone_sup H V₃ V₁ a e _ c he
    rw [hp, natural_fixed, bot_sup_eq] at hsum
    constructor
    · intro g
      rw [fixes_transport _ _ e c he, hsum, natural_plane_fixer]
    · rw [quotient_codimension _ _ _ hK hV, quotient_dim_map c, hsum]
      exact natural_quotient_finrank
  · have hsum := map_Uone_sup H V₃ V₁ a e _ c he
    rw [hp] at hsum
    constructor
    · intro g
      rw [fixes_transport _ _ e c he, hsum]
      exact augmentation_pair_fixer (e g)
    · rw [quotient_codimension _ _ _ hK hV, quotient_dim_map c, hsum]
      exact augmentation_quotient_finrank

/-- Both finite displacement equalities transport to the same actual source commutator image. -/
theorem model_displacement (H V₃ V₁ Uα : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* S) (hm : CompatibleModel H V₃ V₁ a e)
    (hα : Uα ≤ H)
    (hnat : naturalDisplacement ((Source.starImage H Uα).map e.toMonoidHom) = canonicalPlane)
    (haug : displacement ((Source.starImage H Uα).map e.toMonoidHom) = F ⊔ W) :
    quotientSpace (Source.UH H V₃) V₁ (Uone H _ V₁ a ⊔ V₃) =
      quotientSpace (Source.UH H V₃) V₁ ⁅Source.UH H V₃, Uα⁆ := by
  rw [← tilde_displacement H _ V₁ Uα a hα]
  rcases hm with ⟨c, he, hp⟩ | ⟨c, he, hp⟩
  · apply Submodule.map_injective_of_injective c.injective
    rw [map_displacement _ _ e c he, map_Uone_sup H V₃ V₁ a e _ c he,
      hp, natural_fixed, bot_sup_eq]
    exact hnat.symm
  · apply Submodule.map_injective_of_injective c.injective
    rw [map_displacement _ _ e c he, map_Uone_sup H V₃ V₁ a e _ c he, hp]
    exact haug.symm

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.IntersectionBalance
