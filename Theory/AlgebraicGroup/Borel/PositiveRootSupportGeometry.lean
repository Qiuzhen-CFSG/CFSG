module

public import Theory.AlgebraicGroup.Borel.RootSupport
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.FixedSubgroups

universe u

/-!
Geometric reductions for the root support of an actual Borel subgroup.

A regular cocharacter detecting the contained roots proves all three positive
system axioms by additivity of the character--cocharacter pairing. Separately,
the fixed-subgroup generation theorem for a normalizing torus generates a
connected unipotent subgroup from its codimension-one fixed subgroups. If
these are trivial or actual root subgroups, this is precisely root generation.
For a Borel radical, connectedness and normalization follow from the supplied
Borel and radical hypotheses, and the solvable torus decomposition then gives
the complete Borel witness.

The regular detecting cocharacter and the rank-one fixed-subgroup
identifications remain explicit geometric inputs. These reductions do not
assert their existence from reductivity. Sources: Borel, *Linear Algebraic
Groups*, III, 9.5 and IV, 13.18(5), 14.4; GLS3, Theorems 1.9.5(i), 1.11.2.
-/

namespace Theory.AlgebraicGroup

open SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
variable {D : RootGroupData G T}

omit [IsAlgClosed k] in
/-- A regular integral functional on the actual character lattice defines a
positive system. The stored height in `D` need not be nonzero. -/
public theorem RootGroupData.IsRealization.isPositiveSystem_of_characterFunctional
    (hD : D.IsRealization) (f : Additive (TorusWeight T) →+ ℤ)
    (hregular : ∀ a, f (Additive.ofMul (D.rootWeight a)) ≠ 0) :
    IsPositiveSystem D {a | 0 < f (Additive.ofMul (D.rootWeight a))} := by
  have hneg (a : D.Root) :
      f (Additive.ofMul (D.rootWeight (D.neg a))) =
        -f (Additive.ofMul (D.rootWeight a)) := by
    rw [hD.2.2.2.1 a]
    exact map_neg f (Additive.ofMul (D.rootWeight a))
  refine ⟨?_, ?_, ?_⟩
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hpos : 0 < f (Additive.ofMul (D.rootWeight a)) := ha.1
    have hnegative : 0 < f (Additive.ofMul (D.rootWeight (D.neg a))) := ha.2
    rw [hneg] at hnegative
    omega
  · apply Set.eq_univ_iff_forall.mpr
    intro a
    by_cases hpos : 0 < f (Additive.ofMul (D.rootWeight a))
    · exact Or.inl hpos
    · apply Or.inr
      change 0 < f (Additive.ofMul (D.rootWeight (D.neg a)))
      rw [hneg]
      have hne := hregular a
      omega
  · intro a ha b hb c hab
    change 0 < f (Additive.ofMul (D.rootWeight c))
    rw [hD.2.2.2.2.1 a b c hab]
    have hsum : f (Additive.ofMul (D.rootWeight a * D.rootWeight b)) =
        f (Additive.ofMul (D.rootWeight a)) +
          f (Additive.ofMul (D.rootWeight b)) :=
      map_add f (Additive.ofMul (D.rootWeight a)) (Additive.ofMul (D.rootWeight b))
    rw [hsum]
    exact add_pos ha hb

/-- The source's regular chamber cocharacter proves positivity of the literal
Borel root support, with the raw inverse-conjugation character convention. -/
public theorem RootGroupData.isPositiveSystem_borelRootSupport_of_cocharacter
    (hD : D.IsRealization) (B : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T)
    (hregular : ∀ a,
      characterCocharacterPairing T c (Additive.ofMul (D.rootWeight a)) ≠ 0)
    (hdetect : ∀ a, D.rootSubgroup a ≤ B ↔
      0 < characterCocharacterPairing T c (Additive.ofMul (D.rootWeight a))) :
    IsPositiveSystem D (D.borelRootSupport B) := by
  have heq : D.borelRootSupport B =
      {a | 0 < characterCocharacterPairing T c (Additive.ofMul (D.rootWeight a))} := by
    ext a
    exact hdetect a
  rw [heq]
  exact hD.isPositiveSystem_of_characterFunctional
    (characterCocharacterPairing T c) hregular

/-- Fixed subgroups under codimension-one subtori generate the root support
when each such subgroup is trivial or one of the specified actual roots. -/
public theorem RootGroupData.rootSupport_generation_of_fixed_subgroups
    (D : RootGroupData G T) (X : ClosedSubgroup G)
    (hXc : _root_.IsConnected (X : Set (Variety.Point G)))
    (hT : IsSubtorus T) (hTN : T ≤ X.normalizer)
    (hfixed : (X.pointwiseCentralizer T).toSubgroup = ⊥)
    (hrankOne : ∀ Q : CodimensionOneSubtorus T,
      (X.pointwiseCentralizer Q.1).toSubgroup = ⊥ ∨
        ∃ a, X.pointwiseCentralizer Q.1 = D.rootSubgroup a) :
    X.toSubgroup = RootSubgroupGenerated D (D.borelRootSupport X) := by
  apply le_antisymm
  · rw [← externalTorusFixed_generation X T hXc hT hTN]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with hx | hx
    · have hx' : x ∈ (X.pointwiseCentralizer T).toSubgroup := hx
      rw [hfixed] at hx'
      rw [Subgroup.mem_bot.mp hx']
      exact (RootSubgroupGenerated D (D.borelRootSupport X)).one_mem
    · obtain ⟨Q, hx⟩ := Set.mem_iUnion.mp hx
      rcases hrankOne Q with hbot | ⟨a, ha⟩
      · have hx' : x ∈ (X.pointwiseCentralizer Q.1).toSubgroup := hx
        rw [hbot] at hx'
        rw [Subgroup.mem_bot.mp hx']
        exact (RootSubgroupGenerated D (D.borelRootSupport X)).one_mem
      · have haroot : a ∈ D.borelRootSupport X := by
          intro y hy
          rw [← ha] at hy
          exact hy.1
        apply rootSubgroup_le_RootSubgroupGenerated D haroot
        rwa [← ha]
  · exact (RootSubgroupGenerated_le_iff D _ X.toSubgroup).mpr fun _ ha => ha

/-- Apply the fixed-subgroup generation reduction to the actual Borel
radical. Its connectedness and torus normalization are discharged here. -/
public theorem RootGroupData.radical_le_rootGenerated_borelRootSupport_of_fixed_subgroups
    (hD : D.IsRealization) {B U : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hU : IsUnipotentRadicalOf B U)
    (hfixed : (U.pointwiseCentralizer T).toSubgroup = ⊥)
    (hrankOne : ∀ Q : CodimensionOneSubtorus T,
      (U.pointwiseCentralizer Q.1).toSubgroup = ⊥ ∨
        ∃ a, U.pointwiseCentralizer Q.1 = D.rootSubgroup a) :
    U.toSubgroup ≤ RootSubgroupGenerated D (D.borelRootSupport B) := by
  obtain ⟨V, hV, hVc⟩ :=
    exists_unipotentRadical_of_connected_solvable B hB.connected hB.solvable
  have hUc : _root_.IsConnected (U : Set (Variety.Point G)) := by
    rwa [unipotent_radical_unique hV hU] at hVc
  have hTN : T ≤ U.normalizer := by
    intro t ht
    change t ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hU.2.2.1 t (hTB ht) x hx
    · intro hx
      have h := hU.2.2.1 t⁻¹ (hTB (T.toSubgroup.inv_mem ht)) (t * x * t⁻¹) hx
      have heq : t⁻¹ * (t * x * t⁻¹) * (t⁻¹)⁻¹ = x := by group
      rw [heq] at h
      exact h
  rw [D.borelRootSupport_eq_radicalSupport hD hB hU]
  exact (D.rootSupport_generation_of_fixed_subgroups U hUc hT.1 hTN hfixed hrankOne).le

/-- The same local geometric facts construct the full Borel witness, including
the literal radical and the proved torus--radical factorization. -/
public theorem RootGroupData.borelWitness_of_fixed_subgroups
    (hD : D.IsRealization) {B U : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hU : IsUnipotentRadicalOf B U)
    (hfixed : (U.pointwiseCentralizer T).toSubgroup = ⊥)
    (hrankOne : ∀ Q : CodimensionOneSubtorus T,
      (U.pointwiseCentralizer Q.1).toSubgroup = ⊥ ∨
        ∃ a, U.pointwiseCentralizer Q.1 = D.rootSubgroup a) :
    Nonempty (IsBorelOfPositiveSystem D (D.borelRootSupport B) B) := by
  exact D.borelWitness_of_radical_le_rootGenerated hD hB hT hTB hU
    (D.radical_le_rootGenerated_borelRootSupport_of_fixed_subgroups
      hD hB hT hTB hU hfixed hrankOne)

end Theory.AlgebraicGroup
