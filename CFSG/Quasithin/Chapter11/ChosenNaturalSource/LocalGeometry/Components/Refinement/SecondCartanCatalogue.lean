module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.SecondSeven

/-!
# The second-normalizer catalogue after the alternating-seven exclusions

Apply the actual second Cartan factor to both alternating-seven rows of
11.1.1. The ordinary quotient has no commuting three/five pair, and its
central three-cover has no moving central cubic on the full plane of
binary dimension at most six. Thus only equality, the two linear-three
rows and the nilpotent odd-kernel SL₂(5) row remain. The existential
consumer retains relative normality, He membership, and both original
two-core quotients.

The natural-plane projection, Cartan cardinality and faithful action are
preceding flag/model inputs of qt-d-1222-natural-flag-cartan; the parent
qt-d-1222-natural-local-geometry retains their final discharge. The linear
and signalizer exclusions, triangle and original 11.1.1--3 assembly remain
with qt-d-1222-natural-relative-components. This is not yet the full
second-component equality of 11.1.2.

Source: Aschbacher--Smith 11.1.2, printed pp.764--765,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The literal second Cartan removes both alternating-seven rows from the
complete source-derived catalogue. Only the linear and odd-radical rows remain. -/
theorem second_linear_or_nilpotent_from_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K) (hLK : f.Li 1 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) ⊓ centralizer (f.Vi 1 : Set G) = ⊥)
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    f.Li 1 = K ∨
      Source.IsSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) ∨
      (S.field.degree = 2 ∧
        HasExtension (K ⧸ pCore 2 K)
          (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
          (fun Q _ => Source.IsSL Q 2 5)) := by
  rcases second_remaining_models_from_preceding_inputs D S f hm hK.1 hLK π hπ p hp hact hk
    with he | h | h | ⟨hn,h⟩
  · exact .inl he
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · rcases h with h | h | h
    · exact (second_not_seven_of_cartan D S f hu hm hX hK hLK hXcard hfaith p hp hk (.inl h)).elim
    · exact (second_not_seven_of_cartan D S f hu hm hX hK hLK hXcard hfaith p hp hk (.inr h)).elim
    · exact .inr (.inr (.inr ⟨hn,h⟩))

/-- Construct the original containing component and apply the complete
alternating-seven exclusion, retaining normality in N_G(V₂) and He membership. -/
theorem second_exists_normal_component_linear_or_nilpotent
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    {X : Subgroup G} (hX : IsCartan T L X)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 1)) ⊓ centralizer (f.Vi 1 : Set G) = ⊥)
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v))
    (hk : ∀ v, p v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G)) :
    ∃ K : Subgroup G, Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K ∧
      f.Li 1 ≤ K ∧ K ∈ Chapter1.He G ∧
      (f.Li 1 = K ∨
        Source.IsSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ S.field.degree) ∨
        (S.field.degree = 2 ∧
          HasExtension (K ⧸ pCore 2 K)
            (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
            (fun Q _ => Source.IsSL Q 2 5))) := by
  obtain ⟨K,hK,hLK,hHe,_⟩ := flag_exists_unique_normal_component_of_model D S f 1 hm
  exact ⟨K,hK,hLK,hHe,second_linear_or_nilpotent_from_cartan D S f hu hm hX hK hLK
    hXcard hfaith π hπ p hp hact hk⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
