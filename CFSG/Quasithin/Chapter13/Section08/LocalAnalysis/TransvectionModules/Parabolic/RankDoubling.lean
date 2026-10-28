module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.Actions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.SourceAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.MarkedOrbit
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Actor
public import Mathlib.FieldTheory.Finiteness

/-!
# Dimension doubling for the literal parabolic quotient

U₂ and K₂ retain their source definitions. The quotient and action modules
construct U₂/V₂ and its K₂-orbit W from ambient conjugation. The earlier local
identities in 13.5.4 and 13.7.3, together with compatible markings of I₂/O₂(I₂)
and V/V₂, construct the local S₃-action. Its cubic r and inverting involution
prove that the explicit map `(a,b) ↦ a + r(b)` identifies W × W with this
literal quotient. The index-two flag and the definition of U₂ discharge orbit
identification and generation. Adding the actual order-four denominator gives
`dim U₂ = 2 dim W + 2`.

The marking on U_H/V₁ transports the actual three-space orbit to the computed
natural or cover orbit. Thus the source quotient has dimension four or six,
and U₂ has dimension six or eight. The natural-branch interface retains
L̄T̄ ≃ S₆ using the actual image in N_G(V)/C_G(V).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.6, printed p.948 (PDF p.965).

This is the dimension ingredient of 13.8.6. Its source assembly owner supplies
the earlier identities, standing flag sizes and compatible markings explicitly
authorized by that ingredient's contract. The results ending in `of_source_data`
and the two numerical branches construct the action; no doubling, quotient
model, orbit dimension or final rank is among their premises. Construction of
the markings and the remaining module assertions of 13.8.6 stay with the parent.
-/

public section

open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling
variable {G : Type*} [Group G]
variable (H V V₂ V₃ : Subgroup G)
  [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]

/-- Conditional source decomposition, using the actual three-space orbit. -/
noncomputable def sourcePairEquiv (h₃ : V₃ ≤ V) (hindex : V₂.relIndex V₃ = 2)
    (a : V₃) (ha : (a : G) ∉ V₂) (d : LocalDoublingAction H V V₂ V₃ h₃ a) :
    (W H V V₂ V₃ h₃ × W H V V₂ V₃ h₃) ≃ₗ[F] Additive (Uhat H V V₂) :=
  let e := LinearEquiv.ofEq _ _ (W_eq_orbitSpan H V V₂ V₃ h₃ a
    (seed_direction H V V₂ V₃ h₃ hindex a ha))
  (e.prodCongr e).trans
    (orbitPairEquiv (representation H V V₂) d.symmetric
      (seedVector H V V₂ ⟨a,h₃ a.property⟩) d.commutes d.seed_polynomial d.fixes_orbit
      (orbit_pair_generates H V V₂ _ _ d.seed_plane))

/-- The decomposition sends the two coordinates to a + r(b) in the literal quotient. -/
theorem sourcePairEquiv_apply (h₃ : V₃ ≤ V) (hindex : V₂.relIndex V₃ = 2)
    (a : V₃) (ha : (a : G) ∉ V₂) (d : LocalDoublingAction H V V₂ V₃ h₃ a)
    (x y : W H V V₂ V₃ h₃) :
    sourcePairEquiv H V V₂ V₃ h₃ hindex a ha d (x,y) =
      x.val + d.symmetric InvertedCubicTensor.cubic y.val := by
  simp only [sourcePairEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    orbitPairEquiv_apply, LinearEquiv.coe_ofEq_apply]

/-- The flag validates the literal denominator, and the constructed equivalence doubles dimension. -/
theorem source_dimension_doubling [Finite G] (h₂ : V₂ ≤ V₃) (h₃ : V₃ ≤ V)
    (hindex : V₂.relIndex V₃ = 2)
    (a : V₃) (ha : (a : G) ∉ V₂) (d : LocalDoublingAction H V V₂ V₃ h₃ a) :
    V₂ ≤ Source.U2 H V V₂ ∧
      finrank F (Additive (Uhat H V V₂)) = 2 * finrank F (W H V V₂ V₃ h₃) := by
  refine ⟨V2_le_U2 H V V₂ (h₂.trans h₃), ?_⟩
  have h := (sourcePairEquiv H V V₂ V₃ h₃ hindex a ha d).finrank_eq
  rw [Module.finrank_prod] at h
  omega

/-- Adding the actual order-four denominator recovers the rank of U₂. -/
theorem finrank_U2_eq_quotient_add_two [Finite G] (h₂ : V₂ ≤ V)
    (hcard : Nat.card V₂ = 4) :
    finrank F (Additive (Source.U2 H V V₂)) =
      finrank F (Additive (Uhat H V V₂)) + 2 := by
  have h := (V₂.subgroupOf (Source.U2 H V V₂)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (V2_le_U2 H V V₂ h₂)).toEquiv,
    index_eq_card, hcard] at h
  have hU := Module.natCard_eq_pow_finrank (K := F)
    (V := Additive (Source.U2 H V V₂))
  have hQ := Module.natCard_eq_pow_finrank (K := F) (V := Additive (Uhat H V V₂))
  change Nat.card (Source.U2 H V V₂) = _ at hU
  change Nat.card (Uhat H V V₂) = _ at hQ
  rw [Nat.card_zmod] at hU hQ
  change 4 * Nat.card (Uhat H V V₂) = Nat.card (Source.U2 H V V₂) at h
  rw [hU, hQ, show 4 = 2 ^ 2 from rfl, ← pow_add] at h
  have he := Nat.pow_right_injective (by decide : 1 < 2) h
  omega

/-- Conditional rank reduction to the computed marked orbit; no final rank is an input. -/
theorem source_rank_reduction [Finite G] (h₂ : V₂ ≤ V₃) (h₃ : V₃ ≤ V)
    (hindex : V₂.relIndex V₃ = 2) (hcard : Nat.card V₂ = 4)
    (a : V₃) (ha : (a : G) ∉ V₂) (d : LocalDoublingAction H V V₂ V₃ h₃ a) :
    finrank F (Additive (Source.U2 H V V₂)) = 2 * finrank F (W H V V₂ V₃ h₃) + 2 := by
  rw [finrank_U2_eq_quotient_add_two H V V₂ (h₂.trans h₃) hcard,
    (source_dimension_doubling H V V₂ V₃ h₂ h₃ hindex a ha d).2]

variable [Finite G]
variable (V₁ I₂ L₂ : Subgroup G)

/-- Construct the local action from the earlier subgroup identities and the
compatible markings of I₂/O₂(I₂) and V/V₂. -/
noncomputable def sourceLocalAction
    (d : SourceAction.LocalData H V V₁ V₂ V₃ I₂ L₂)
    (m : SourceAction.CompatibleMarking H V V₁ V₂ V₃ I₂ L₂ d)
    (hVQ : ⁅V, Source.QH H⁆ ≤ V₃) (a : V₃) (ha : (a : G) ∉ V₂) :
    LocalDoublingAction H V V₂ V₃ d.flag3V a :=
  (SourceAction.of_source_data H V V₁ V₂ V₃ I₂ L₂ d m hVQ a ha).some

/-- The literal quotient is two copies of its actual three-space orbit.
The local action used here is constructed, rather than assumed. -/
noncomputable def sourcePairEquiv_of_source_data
    (d : SourceAction.LocalData H V V₁ V₂ V₃ I₂ L₂)
    (m : SourceAction.CompatibleMarking H V V₁ V₂ V₃ I₂ L₂ d)
    (hVQ : ⁅V, Source.QH H⁆ ≤ V₃) (hindex : V₂.relIndex V₃ = 2)
    (a : V₃) (ha : (a : G) ∉ V₂) :
    (W H V V₂ V₃ d.flag3V × W H V V₂ V₃ d.flag3V) ≃ₗ[F] Additive (Uhat H V V₂) :=
  sourcePairEquiv H V V₂ V₃ d.flag3V hindex a ha
    (sourceLocalAction H V V₂ V₃ V₁ I₂ L₂ d m hVQ a ha)

/-- Evaluation of the constructed decomposition at the two orbit coordinates. -/
theorem sourcePairEquiv_of_source_data_apply
    (d : SourceAction.LocalData H V V₁ V₂ V₃ I₂ L₂)
    (m : SourceAction.CompatibleMarking H V V₁ V₂ V₃ I₂ L₂ d)
    (hVQ : ⁅V, Source.QH H⁆ ≤ V₃) (hindex : V₂.relIndex V₃ = 2)
    (a : V₃) (ha : (a : G) ∉ V₂) (x y : W H V V₂ V₃ d.flag3V) :
    sourcePairEquiv_of_source_data H V V₂ V₃ V₁ I₂ L₂ d m hVQ hindex a ha (x,y) =
      x.val + (sourceLocalAction H V V₂ V₃ V₁ I₂ L₂ d m hVQ a ha).symmetric
        InvertedCubicTensor.cubic y.val :=
  sourcePairEquiv_apply H V V₂ V₃ d.flag3V hindex a ha _ x y

/-- The source dimension-doubling identity from the earlier local data.
The standing index-two flag supplies a nonzero seed. -/
theorem source_dimension_doubling_of_source_data
    (d : SourceAction.LocalData H V V₁ V₂ V₃ I₂ L₂)
    (m : SourceAction.CompatibleMarking H V V₁ V₂ V₃ I₂ L₂ d)
    (hVQ : ⁅V, Source.QH H⁆ ≤ V₃) (hindex : V₂.relIndex V₃ = 2) :
    V₂ ≤ Source.U2 H V V₂ ∧
      finrank F (Additive (Uhat H V V₂)) = 2 * finrank F (W H V V₂ V₃ d.flag3V) := by
  obtain ⟨a, ha, _⟩ := exists_seed_direction H V V₂ V₃ d.flag3V hindex
  exact source_dimension_doubling H V V₂ V₃ d.flag23 d.flag3V hindex a ha
    (sourceLocalAction H V V₂ V₃ V₁ I₂ L₂ d m hVQ a ha)

/-- Add the standing order-four denominator to the proved quotient dimension. -/
theorem source_rank_reduction_of_source_data
    (d : SourceAction.LocalData H V V₁ V₂ V₃ I₂ L₂)
    (m : SourceAction.CompatibleMarking H V V₁ V₂ V₃ I₂ L₂ d)
    (hVQ : ⁅V, Source.QH H⁆ ≤ V₃) (hindex : V₂.relIndex V₃ = 2)
    (hcard : Nat.card V₂ = 4) :
    finrank F (Additive (Source.U2 H V V₂)) =
      2 * finrank F (W H V V₂ V₃ d.flag3V) + 2 := by
  rw [finrank_U2_eq_quotient_add_two H V V₂ (d.flag23.trans d.flag3V) hcard,
    (source_dimension_doubling_of_source_data H V V₂ V₃ V₁ I₂ L₂ d m hVQ hindex).2]

variable [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The rank conclusion in 13.8.6(4), from the compatible source markings
and earlier local identities. The S₆ hypothesis is on the literal barred LT
image; the marking also certifies the four-dimensional source module. -/
theorem source_natural_dimensions
    (d : SourceAction.LocalData H V V₁ V₂ V₃ I₂ L₂)
    (m : SourceAction.CompatibleMarking H V V₁ V₂ V₃ I₂ L₂ d)
    (hVQ : ⁅V, Source.QH H⁆ ≤ V₃) (hindex : V₂.relIndex V₃ = 2)
    (hcard : Nat.card V₂ = 4) (n : MarkedOrbit.NaturalMarking H V₁ V₂ V₃)
    (L : Subgroup G) (hLT : L ⊔ (d.sylow : Subgroup G) ≤ normalizer (V : Set G))
    (_hS6 : Nonempty ((TransvectionQuotients.FiveSeed.toBar
      (L ⊔ (d.sylow : Subgroup G)) V hLT).range ≃* Equiv.Perm (Fin 6))) :
    finrank F (Additive (Source.Utilde H V₃ V₁)) = 4 ∧
      finrank F (W H V V₂ V₃ d.flag3V) = 2 ∧
      finrank F (Additive (Uhat H V V₂)) = 4 ∧
      finrank F (Additive (Source.U2 H V V₂)) = 6 := by
  have hW := MarkedOrbit.natural_finrank (V := V) d.flag12 d.flag23 d.flag3V n
  have hQ := (source_dimension_doubling_of_source_data H V V₂ V₃ V₁ I₂ L₂
    d m hVQ hindex).2
  have hU := source_rank_reduction_of_source_data H V V₂ V₃ V₁ I₂ L₂ d m hVQ hindex hcard
  refine ⟨?_, hW, ?_, ?_⟩
  · exact n.equiv.finrank_eq.trans (by
      simpa using BinaryPermutation.finrank_natural_even (Fin 6) (by decide))
  · simpa only [hW] using hQ
  · simpa only [hW] using hU

/-- The rank conclusion in 13.8.6(5), from the compatible source markings
and earlier local identities. The marked source orbit has dimension three,
so its doubled quotient has dimension six and its numerator dimension eight. -/
theorem source_cover_dimensions
    (d : SourceAction.LocalData H V V₁ V₂ V₃ I₂ L₂)
    (m : SourceAction.CompatibleMarking H V V₁ V₂ V₃ I₂ L₂ d)
    (hVQ : ⁅V, Source.QH H⁆ ≤ V₃) (hindex : V₂.relIndex V₃ = 2)
    (hcard : Nat.card V₂ = 4) (n : MarkedOrbit.CoverMarking H V₁ V₂ V₃) :
    finrank F (Additive (Source.Utilde H V₃ V₁)) = 5 ∧
      finrank F (W H V V₂ V₃ d.flag3V) = 3 ∧
      finrank F (Additive (Uhat H V V₂)) = 6 ∧
      finrank F (Additive (Source.U2 H V V₂)) = 8 := by
  have hW := MarkedOrbit.cover_finrank (V := V) d.flag12 d.flag23 d.flag3V n
  have hQ := (source_dimension_doubling_of_source_data H V V₂ V₃ V₁ I₂ L₂
    d m hVQ hindex).2
  have hU := source_rank_reduction_of_source_data H V V₂ V₃ V₁ I₂ L₂ d m hVQ hindex hcard
  refine ⟨?_, hW, ?_, ?_⟩
  · exact n.equiv.finrank_eq.trans (by simpa using BinaryPermutation.finrank_core (Fin 6))
  · simpa only [hW] using hQ
  · simpa only [hW] using hU

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling
