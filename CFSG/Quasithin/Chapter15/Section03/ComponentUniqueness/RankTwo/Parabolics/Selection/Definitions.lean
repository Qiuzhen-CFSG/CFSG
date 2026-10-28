module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Models

/-!
# Inputs and intermediate cases for the parabolic selection

The ambient group is I, and normality of L is only normality in I. The
input record contains the component and quotient conclusions preceding
p.1139. The action record identifies the automorphism in 1.1.5(3) with
conjugation by the specified central involution of S.

The intermediate parabolic is a proper overgroup of the actual intrinsic
Sylow normalizer, maximal among S-invariant proper overgroups. The exceptional
model list retains all rank-one and small-field cases of Theorem C, with
actual group equivalences. Neither definition asserts their exclusion.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 1.1.5(3),
printed pp.501--502; 15.3.33, 15.3.39--41 and the first paragraph of the
final proof of 15.3.35, printed pp.1134--1139.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
open Chapter1.Section02.LocalModels ClassificationModels

variable {G : Type*} [Group G]

/-- The component setup of 15.3.39--41, before the parabolic inspection. -/
structure Setup (L MI Yplus S : Subgroup G) [L.Normal] : Prop where
  quasisimple : IsQuasisimple L
  yplus_le : Yplus ≤ L
  generated : L ⊔ S = ⊤
  sylow : ∃ P : Sylow 2 G, (P : Subgroup G) = S
  quotient_local : LocalConfiguration (centralizerQuotientComponent L)
    (MI.map (centralizerQuotientMap L)) (Yplus.map (centralizerQuotientMap L))
    (S.map (centralizerQuotientMap L))

/-- The action in 1.1.5 is the source involution's actual conjugation.
Its membership and centrality come from the choice of Z before 15.3.33. -/
structure SourceAction (L S : Subgroup G) (z : G) (α : MulAut L) : Prop where
  mem_sylow : z ∈ S
  involution : orderOf z = 2
  centralizes : z ∈ centralizer (S : Set G)
  action : ∀ x : L, (α x : G) = z * x * z⁻¹
  alternatives : CharacteristicTwoAction115 L α

/-- The normalizer formed inside the component, mapped back into the ambient group. -/
def sylowBorel (D T : Subgroup G) : Subgroup G :=
  (normalizer (T.subgroupOf D : Set D)).map D.subtype

/-- The precise maximal invariant parabolic output required by the inspection.
The whole component is excluded by strict properness. -/
structure MaximalInvariantParabolic (D T P : Subgroup G) : Prop where
  contains_borel : sylowBorel D T ≤ P
  proper : P < D
  invariant : T ≤ normalizer (P : Set G)
  maximal : ∀ Q : Subgroup G, sylowBorel D T ≤ Q → Q < D →
    T ≤ normalizer (Q : Set G) → P ≤ Q → Q ≤ P

/-- The actual local intersection in the centralizer quotient. This is an
intermediate conclusion, not a field of `Setup`. -/
def QuotientParabolic (L MI S : Subgroup G) [L.Normal] : Prop :=
  MaximalInvariantParabolic (centralizerQuotientComponent L)
    (S.map (centralizerQuotientMap L))
    (MI.map (centralizerQuotientMap L) ⊓ centralizerQuotientComponent L)

/-- Cases still requiring exclusion after transporting the 1.1.5 catalogue.
Keeping A₆ separate avoids assuming its exceptional symplectic isomorphism. -/
inductive ExceptionalModel (D : Type*) [Group D] : Prop
  | rank_one (model : IsBenderModel D)
  | linear_three_two (model : ClassicalGroup.IsPSL D 3 2)
  | triality_two (model : Triality.Standard.IsTrialityGroupAt 2 D)
  | symplectic_derived
      (model : Nonempty (D ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))))
  | g2_derived (model : Nonempty (D ≃* commutator (Atlas.G2.Model (ZMod 2))))
  | tits (model : Nonempty (D ≃* Tits.ParrottGroup))
  | alternating_six (model : Nonempty (D ≃* alternatingGroup (Fin 6)))

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
