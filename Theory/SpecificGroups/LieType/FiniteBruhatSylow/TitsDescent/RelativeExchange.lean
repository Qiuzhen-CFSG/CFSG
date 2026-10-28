module

public import Theory.SpecificGroups.LieType.FiniteBruhatSylow.FixedPoints
public import Theory.AlgebraicGroup.BNPair.SimpleLiftCoverage
public import Theory.SpecificGroups.LieType.FiniteBruhatSylow.TitsDescent.RelativeExchange.RayCalculus

/-!
# Relative simple-lift exchange in the defining residual

The ray groups here are the fixed points of specified algebraic whole-ray
subgroups. The marked lifts are elements of the literal prime-to-p residual,
and the normalizer is the intersection with the algebraic torus normalizer.
The local input records ordered positive-ray coordinates, the actual
conjugation action on rays and rank-one multiplication identities. It contains
neither exchange nor Bruhat coverage nor any BN axiom.

`RayRelations.collect` collects all but the marked ray into a factor whose
conjugate remains positive. The sign of the normalizer action and the local
rank-one identity give the two exchange alternatives. A nonidentity ray
element and opposite-ray separation supply nontriviality. All fixed ray
elements lie in the residual by unipotence. The same proof therefore retains
every factor in every literal intermediate subgroup of the full fixed group.

The ray index and multiplication identities are deliberately not replaced by
a reduced crystallographic root system or additive root parameters: the full
nonabelian unitary and Suzuki--Ree rays, including the Ree-F4 16-gon, must be
supplied by the geometric producer. The parent constructing the Tits system
must discharge these local inputs and identify the marked quotient reflections.

Sources: GLS3 2.3.4(b), 2.3.7--2.3.8 and §2.4; Chapter 1, 1.11.1(d).
-/

@[expose] public section
namespace Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent.RelativeExchange
open FiniteParabolicRealization

variable {k : Type*} [Field k] {K : Variety k} [AlgebraicGroup K]

/-- Fixed points in a specified algebraic point subgroup. -/
abbrev fixedIntersection (σ : AlgebraicEndomorphism K)
    (A : Subgroup (Variety.Point K)) : Subgroup (fixedPoints σ) :=
  A.comap (fixedPoints σ).subtype

/-- The literal Borel intersection in an intermediate fixed subgroup. -/
abbrev intermediateBorel (σ : AlgebraicEndomorphism K) (B : ClosedSubgroup K)
    (L : Subgroup (fixedPoints σ)) : Subgroup L :=
  (fixedIntersection σ B.toSubgroup).subgroupOf L

/-- Intersect with the algebraic torus normalizer, not the normalizer of the
possibly smaller finite torus. -/
abbrev intermediateNormalizer (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    (L : Subgroup (fixedPoints σ)) : Subgroup L :=
  (fixedIntersection σ (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)))).subgroupOf L

@[simp] theorem intermediateBorel_defining (σ : AlgebraicEndomorphism K) (p : ℕ)
    (B : ClosedSubgroup K) :
    intermediateBorel σ B (definingGroup σ p) = borel σ p B := rfl

@[simp] theorem intermediateNormalizer_defining (σ : AlgebraicEndomorphism K) (p : ℕ)
    (T : ClosedSubgroup K) :
    intermediateNormalizer σ T (definingGroup σ p) = normalizer σ p T := rfl

/-- The same residual lift, regarded as an element of an intermediate group. -/
def intermediateLift (σ : AlgebraicEndomorphism K) (p : ℕ)
    (L : Subgroup (fixedPoints σ)) (hL : definingGroup σ p ≤ L)
    (s : definingGroup σ p) : L := ⟨s.val, hL s.property⟩

@[simp] theorem intermediateLift_defining (σ : AlgebraicEndomorphism K) (p : ℕ)
    (s : definingGroup σ p) : intermediateLift σ p (definingGroup σ p) le_rfl s = s := rfl

/-- Read a marked residual lift in the full fixed algebraic normalizer. -/
def fixedNormalizerLift (σ : AlgebraicEndomorphism K) (p : ℕ)
    (T : ClosedSubgroup K) (s : definingGroup σ p) (hs : s ∈ normalizer σ p T) :
    fixedIntersection σ (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))) :=
  ⟨s.val, hs⟩

/-- The torus-transport input of `RayRelations` follows directly from the
literal algebraic normalizer; it needs no finite-torus normalizer theorem. -/
theorem fixed_torus_transport (σ : AlgebraicEndomorphism K) (T : ClosedSubgroup K)
    (n : fixedIntersection σ (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))))
    (t : fixedPoints σ) (ht : t ∈ fixedIntersection σ T.toSubgroup) :
    (n : fixedPoints σ) * t * (n : fixedPoints σ)⁻¹ ∈ fixedIntersection σ T.toSubgroup := by
  exact (Subgroup.mem_normalizer_iff.mp n.property (t : Variety.Point K)).mp ht

/-- The conditional local contract on the literal fixed ray groups. `Y α`
must be the entire projected-ray preimage of GLS3 2.3.6, not a selected
absolute root group. The reflection action is linked to the lifts by
`lift_action` and to the actual carriers by `transport`. -/
abbrev FixedRayRelations (σ : AlgebraicEndomorphism K) (p : ℕ)
    (B T : ClosedSubgroup K) {R I : Type*} (Y : R → ClosedSubgroup K)
    (simple : I → R) (lift : I → definingGroup σ p)
    (hlift : ∀ i, lift i ∈ normalizer σ p T) :=
  RayRelations (fixedIntersection σ B.toSubgroup) (fixedIntersection σ T.toSubgroup)
    (fixedIntersection σ (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))))
    (fun α => fixedIntersection σ (Y α).toSubgroup) simple
    (fun i => fixedNormalizerLift σ p T (lift i) (hlift i))

section Exchange
variable [IsAlgClosed k] (σ : AlgebraicEndomorphism K) (p : ℕ)
  [Fact p.Prime] [CharP k p]
  (B T : ClosedSubgroup K) {R I : Type*} (Y : R → ClosedSubgroup K)
  (hY : ∀ α, IsUnipotentAlgebraicGroup (Y α).carrierVariety)
  (simple : I → R) (lift : I → definingGroup σ p)
  (hlift : ∀ i, lift i ∈ normalizer σ p T)
  (D : FixedRayRelations σ p B T Y simple lift hlift)

include hY D

/-- Exchange in every intermediate subgroup. The resulting Borel factors
are elements of that subgroup, not merely fixed algebraic points. -/
theorem intermediate_simpleLiftExchange
    (L : Subgroup (fixedPoints σ)) (hL : definingGroup σ p ≤ L) :
    BruhatGeneration.SimpleLiftExchange (intermediateBorel σ B L)
      (intermediateNormalizer σ T L)
      (Set.range fun i => intermediateLift σ p L hL (lift i)) := by
  exact D.simpleLiftExchange L
    (fun α => (fixed_unipotent_le_definingGroup σ p (Y α) (hY α)).trans hL)
    (fun i => hL (lift i).property)

/-- Exchange for precisely the published residual Borel and normalizer and
the actual marked lift set. This discharges `SimpleLiftExchange` in the
finite Bruhat-generation consumer. -/
theorem defining_simpleLiftExchange :
    BruhatGeneration.SimpleLiftExchange (borel σ p B) (normalizer σ p T)
      (Set.range lift) := by
  exact intermediate_simpleLiftExchange σ p B T Y hY simple lift hlift D
    (definingGroup σ p) le_rfl

/-- The nontriviality witness for each marked lift in every intermediate
group uses the same nonidentity element of its whole fixed ray. -/
theorem intermediate_nontriviality
    (L : Subgroup (fixedPoints σ)) (hL : definingGroup σ p ≤ L) (i : I) :
    ∃ b ∈ intermediateBorel σ B L,
      intermediateLift σ p L hL (lift i) * b *
        (intermediateLift σ p L hL (lift i))⁻¹ ∉ intermediateBorel σ B L := by
  exact D.nontriviality L
    (fun α => (fixed_unipotent_le_definingGroup σ p (Y α) (hY α)).trans hL)
    (fun i => hL (lift i).property) i

/-- The nontriviality witness for the literal residual Borel. -/
theorem defining_nontriviality (i : I) :
    ∃ b ∈ borel σ p B, lift i * b * (lift i)⁻¹ ∉ borel σ p B := by
  exact intermediate_nontriviality σ p B T Y hY simple lift hlift D
    (definingGroup σ p) le_rfl i

end Exchange
end Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent.RelativeExchange
end
