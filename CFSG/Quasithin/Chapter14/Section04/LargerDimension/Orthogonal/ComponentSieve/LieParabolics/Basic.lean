module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings

/-!
# The actual Lie-parabolic placement in the orthogonal sieve

The five families in A.3.14(1) are specified by actual group isomorphisms.
The residual is computed inside the parabolic before being embedded in its
ambient group. Removing the enclosing component subtype gives an isomorphism
whose underlying map is that very inclusion. Consequently intrinsic two-cores
and their quotient actions can be transported without changing the subgroup
being tested in Lemma 14.4.9.

These are placement and transport interfaces, not a classification of the
parabolics or a proof of the five-family implication.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
A.3.14(1), printed pp.49–50, and Lemma 14.4.9, printed p.1010.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics
open Chapter1.Section02 Chapter1.Section02.LocalModels

/-- The two linear-three carriers occurring in A.3.14(1). -/
def LinearFamily (L : Type*) [Group L] : Prop :=
  ClassicalGroup.IsPSL L 3 4 ∨ IsSL L 3 4

/-- The other three carriers, using the genuine D₄ graph-field construction. -/
def NonlinearFamily (L : Type*) [Group L] : Prop :=
  ClassicalGroup.IsPSp L 2 4 ∨ ClassificationModels.IsG2At L 4 ∨
    Triality.Standard.IsTrialityGroupAt 4 L

/-- Exactly the actual ambient models in A.3.14(1). -/
def LieFamily (L : Type*) [Group L] : Prop :=
  LinearFamily L ∨ NonlinearFamily L

/-- The solvable residual, embedded only after computing it in the parabolic. -/
def embeddedResidual {L : Type*} [Group L] (P : Subgroup L) : Subgroup L :=
  (solvableResidual P).map P.subtype

/-- An ambient isomorphism transports the Sylow-normalizer placement. -/
theorem parabolic_map {L M : Type*} [Group L] [Group M] [Finite L]
    {P : Subgroup L} (hP : LieParabolicTwo P) (e : L ≃* M) :
    LieParabolicTwo (P.map e.toMonoidHom) := by
  obtain ⟨T, hT⟩ := hP
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change normalizer (↑((T : Subgroup L).map e.toMonoidHom) : Set M) ≤ _
  rw [← map_equiv_normalizer_eq]
  exact map_mono hT

/-- Solvable residual transport retains the literal subgroup inclusion. -/
theorem embeddedResidual_map {L M : Type*} [Group L] [Group M] [Finite L]
    (P : Subgroup L) (e : L ≃* M) :
    (embeddedResidual P).map e.toMonoidHom =
      embeddedResidual (P.map e.toMonoidHom) := by
  let f : P ≃* (P.map e.toMonoidHom) := e.subgroupMap P
  have hc : (P.map e.toMonoidHom).subtype.comp f.toMonoidHom =
      e.toMonoidHom.comp P.subtype := rfl
  have he : (solvableResidual P).map f.toMonoidHom =
      solvableResidual (P.map e.toMonoidHom) :=
    map_solvableResidual_eq f.toMonoidHom f.surjective
  unfold embeddedResidual
  rw [← he]
  simp only [map_map, hc]

/-- Intrinsic two-core order is invariant under the actual group isomorphism. -/
theorem card_twoCore_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (pCore 2 X) = Nat.card (pCore 2 Y) :=
  Nat.card_congr ((e.subgroupMap (pCore 2 X)).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 e))).toEquiv

/-- Remove the enclosing component subtype while retaining the exact map
from the parabolic residual to the source subgroup `B`. -/
theorem exists_residual_equiv {G : Type*} [Group G] {B K : Subgroup G}
    (h : IsParabolicResidual B K true) :
    ∃ P : Subgroup K, LieParabolicTwo P ∧ IsCoatom P ∧
      ∃ e : embeddedResidual P ≃* B,
        ∀ x : embeddedResidual P, (e x : G) = ((x : K) : G) := by
  obtain ⟨P, hP, hmax, he⟩ := h
  have hm : (embeddedResidual P).map K.subtype = B := by
    simpa only [embeddedResidual, map_map] using he
  refine ⟨P, hP, hmax rfl,
    ((embeddedResidual P).equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hm), ?_⟩
  intro x
  rfl

/-- Apply the source placement to the actual order-sixteen/A₅ section.
The quotient is transported by the induced map on the intrinsic two-cores. -/
theorem exists_parabolic_core_data {G : Type*} [Group G] {B K : Subgroup G}
    (h : IsParabolicResidual B K true)
    (hcard : Nat.card (pCore 2 B) = 16)
    (hquot : IsAlternating (B ⧸ pCore 2 B) 5) :
    ∃ P : Subgroup K, LieParabolicTwo P ∧ IsCoatom P ∧
      Nat.card (pCore 2 (embeddedResidual P)) = 16 ∧
      IsAlternating (embeddedResidual P ⧸ pCore 2 (embeddedResidual P)) 5 ∧
      ∃ e : embeddedResidual P ≃* B,
        ∀ x : embeddedResidual P, (e x : G) = ((x : K) : G) := by
  obtain ⟨P, hP, hmax, e, he⟩ := exists_residual_equiv h
  obtain ⟨a⟩ := hquot
  refine ⟨P, hP, hmax, (card_twoCore_congr e).trans hcard, ?_, e, he⟩
  exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans a⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics
