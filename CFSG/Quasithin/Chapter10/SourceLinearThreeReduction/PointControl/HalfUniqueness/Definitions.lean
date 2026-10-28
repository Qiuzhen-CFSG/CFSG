module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Contracts

/-!+# Independent source inputs to half-Sylow uniqueness

The first obligation is source 10.2.5 on the literal stabilizer N_T(L).
The second excludes the two normal containing C-components constructed
in the opening of 10.2.6. Their normality is relative to the competing
two-local H, and its prescribed Sylow subgroup is N_T(L). Neither
distinctness nor a model classification of the containing components is
assumed. The exclusion must prove the necessary A.3.12 and C.2.7 facts.

Both obligations are independent of the chosen seed in D. Their producers
may reselect a seed internally, but must return these exact statements.
These are interfaces for outstanding proofs, not asserted source results.
Source: Aschbacher--Smith, 10.2.5--6, printed pp.747--749.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual normal containing components supplied by 1.2.4. The strict
alternative records failure of H to normalize L₀. -/
structure ContainingPair
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (t : G) (K₁ K₂ : Subgroup H) : Prop where
  maximal : IsMaximalTwoLocal H
  half_le : halfJoin T L ≤ H
  sylow : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H
  t_mem : t ∈ (T : Subgroup G)
  t_not_normalizes : t ∉ normalizer (L : Set G)
  orbit_eq : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom
  first_component : K₁.IsCComponent
  first_normal : K₁.Normal
  second_component : K₂.IsCComponent
  second_normal : K₂.Normal
  first_le : L.subgroupOf H ≤ K₁
  second_le : (L.map (MulAut.conj t).toMonoidHom).subgroupOf H ≤ K₂
  strict : L.subgroupOf H < K₁ ∨
    (L.map (MulAut.conj t).toMonoidHom).subgroupOf H < K₂

/-- Source 10.2.5, restricted to the original non-A₅ consumer. -/
def StabilizerNormalizerAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal

/-- The A.3.12/C.2.7 contradiction in 10.2.6, with its independently
produced Sylow condition supplied explicitly by `ContainingPair`. -/
def ContainingPairExclusionAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    ∀ (H : Subgroup G) (t : G) (K₁ K₂ : Subgroup H),
      ContainingPair D H t K₁ K₂ → False

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
