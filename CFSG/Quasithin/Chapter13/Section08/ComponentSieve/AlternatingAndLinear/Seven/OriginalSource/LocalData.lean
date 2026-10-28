module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Fitting.Orders
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.LocalData
public import Theory.ElementaryAbelian.PrimePlane
public import Theory.ElementaryAbelian.PrimeRankCard
public import Theory.Quasithin.CoprimeRank
/-!
# The original covered local residuals for the seven-point sieve

The original natural A₆ flag chooses the genuine cubic-cover model when
its local quotient is covered. The factorization of L₁ and its two
marked cubic quotient maps construct every field of LocalResidualData,
including relative normalization and the same element fixing L₀ and
inverting X. The elementary quotient has rank two and supplies the exact
order-nine model used by the first-case exclusion. L₀ centralizes the
original seed through the original central quotient action.

These are the local inputs consumed by both branches of 13.8.24. Final
assembly belongs to qt-d-138-linear-seven-source and its parent
qt-d-138-linear-source; no local factorization, marking, or rank input
remains in these exports.

Source: Aschbacher–Smith 13.2.2, 13.7.3–5, and 13.8.24,
printed pp.877–878,936–938,958–959.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FourThreeBranch.NaturalSelection
variable {G : Type*} [Group G] [Finite G]
variable {L T V V₁ V₃ : Subgroup G}
theorem covered_residual_data (a : LocalAction.NaturalSetup L T V V₁ V₃) :
    Nonempty (LocalResidualData (one L T V₁) (zero L) (plus L T V₁) T) := by
  let hfactor := CoverFactorization.source_factorization a
  let A := one L T V₁
  let Q := A ⧸ pCore 2 A
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsMulCommutative Q := a.one_quotient_commutative hfactor
  let : IsElementaryAbelian 3 Q := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (a.one_quotient_cube hfactor) }
  obtain ⟨e⟩ := IsElementaryAbelian.nonempty_mulEquiv_plane_of_card
    (show Nat.card Q = 3^2 from a.one_quotient_card hfactor)
  obtain ⟨t, hinv, hfix⟩ := a.exists_plus_inverter hfactor
  let actor : normalizer (one L T V₁ : Set G) :=
    ⟨t.val, T_normalizes_one L T V₁ a.line_stable t.property.1⟩
  refine ⟨{
    quotient := e
    generated := (sup_comm _ _).trans hfactor.symm
    first_perfect := residual_isPPerfect _
    second_perfect := residual_isPPerfect _
    core_normalizes_first := (map_subtype_le _).trans (LocalAction.one_normalizes_zero L T V₁ a.normalizes_L)
    core_normalizes_second := (map_subtype_le _).trans (one_normalizes_plus L T V₁)
    sylow_normalizes_first := a.normalizes_L.trans (normalizer_le_zero_normalizer L)
    sylow_normalizes_second := T_normalizes_plus L T V₁ a.normalizes_L a.line_stable
    first_card := ?_
    second_card := ?_
    actor := actor
    actor_mem := t.property.1
    fixes_first := ?_
    inverts_second := ?_ }⟩
  · have hh := (a.marks_card_three hfactor).1
    rw [LocalAction.zeroCoreMap, LocalAction.localCoreMap_range] at hh
    exact hh
  · have hh := (a.marks_card_three hfactor).2
    rw [LocalAction.plusCoreMap, LocalAction.localCoreMap_range] at hh
    exact hh
  · intro x hx
    let z : zero L := ⟨x.val, hx⟩
    have hh := LocalAction.zeroCoreMap_fixed L T V₁ a.normalizes_L a.line_stable hfactor t
      (QuotientGroup.mk' (pCore 2 (zero L)) z)
    rw [LocalAction.zeroCoreMap, LocalAction.localCoreMap_mk] at hh
    rw [coreAction_mk] at hh
    exact hh
  · intro x hx
    let z : plus L T V₁ := ⟨x.val, hx⟩
    have hh := congrArg (LocalAction.plusCoreMap L T V₁ a.line_stable)
      (hinv (QuotientGroup.mk' (pCore 2 (plus L T V₁)) z))
    rw [map_inv] at hh
    change LocalAction.localCoreMap _ _ _ _ (coreAction _ _ _) = _ at hh
    rw [LocalAction.localCoreMap_equivariant _ _ _ _ t.val
      (T_normalizes_plus L T V₁ a.normalizes_L a.line_stable t.property.1)
      (T_normalizes_one L T V₁ a.line_stable t.property.1), LocalAction.localCoreMap_mk] at hh
    rw [LocalAction.plusCoreMap, LocalAction.localCoreMap_mk, coreAction_mk] at hh
    exact hh

variable {S : Sylow 2 G} {V₂ M G₁ : Subgroup G}
private theorem covered_setup
    (d : LocalSetup S L V V₁ V₂ V₃ M G₁)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    Nonempty (LocalAction.NaturalSetup L S V V₁ V₃) := by
  rcases local_quotient_alternatives d with ⟨e, he⟩ | ⟨e, he⟩
  · exfalso
    have hc := Nat.card_congr (centerCongr e).toEquiv
    rw [alternatingGroup.center_eq_bot (by simp), card_bot] at hc
    rcases hcover with ht | ht
    · have hh := ht.2.1
      omega
    · obtain ⟨f⟩ := ht
      have hh := Nat.card_congr (centerCongr f).toEquiv
      rw [Representation.Hexacode.even_center_card] at hh
      omega
  · exact local_covered_flag_model d e he

theorem source_covered_nine
    (d : LocalSetup S L V V₁ V₂ V₃ M G₁)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L)) :
    Nonempty ((sourceOne L S V₁ ⧸ pCore 2 (sourceOne L S V₁)) ≃*
      Multiplicative (Fin 2 → ZMod 3)) := by
  obtain ⟨a⟩ := covered_setup d (Or.inl hcover)
  obtain ⟨r⟩ := covered_residual_data a
  exact ⟨r.quotient.trans ((MulEquiv.prodMultiplicative (ZMod 3) (ZMod 3)).symm.trans
    (LinearEquiv.finTwoArrow (R := ZMod 3) (M := ZMod 3)).symm.toAddEquiv.toMultiplicative)⟩

theorem source_covered_local_rank
    (d : LocalSetup S L V V₁ V₂ V₃ M G₁)
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    primeRank 3 (sourceOne L S V₁) = 2 := by
  obtain ⟨a⟩ := covered_setup d (Or.inr hcover)
  let hf := CoverFactorization.source_factorization a
  let A := one L (S : Subgroup G) V₁
  let Q := A ⧸ pCore 2 A
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsMulCommutative Q := a.one_quotient_commutative hf
  let : IsElementaryAbelian 3 Q := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (a.one_quotient_cube hf) }
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
  change primeRank 3 Q = 2
  rw [← IsElementaryAbelian.log_card_eq_primeRank]
  change Nat.log 3 (Nat.card (one L (S : Subgroup G) V₁ ⧸ pCore 2 (one L (S : Subgroup G) V₁))) = 2
  rw [a.one_quotient_card hf]
  decide

theorem source_covered_residual_data
    (d : LocalSetup S L V V₁ V₂ V₃ M G₁)
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    Nonempty (LocalResidualData (sourceOne L S V₁) (zero L) (plus L S V₁) S) := by
  obtain ⟨a⟩ := covered_setup d (Or.inr hcover)
  exact covered_residual_data a

theorem source_zero_centralizes_seed (d : LocalSetup S L V V₁ V₂ V₃ M G₁) :
    zero L ≤ centralizer (V₃ : Set G) :=
  (residual_le _).trans ((local_centralPreimage_centralizes d).trans
    (Subgroup.centralizer_le d.seed_le))
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
