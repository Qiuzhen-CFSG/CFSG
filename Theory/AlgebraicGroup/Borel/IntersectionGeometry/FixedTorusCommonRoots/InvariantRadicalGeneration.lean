module

public import Theory.AlgebraicGroup.Borel.StandardPositiveSystemClassification.Defs
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.FixedTorusCommonRoots.InvariantRadicalGeneration.FiniteOrbits
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.FixedSubgroups

/-!
Generation of torus-invariant subgroups inside a Borel radical.

The connected case follows from Borel III, 9.4–9.5: codimension-one torus
fixed subgroups generate a connected invariant group. If the corresponding
fixed subgroups of the ambient radical are root groups, dimension one makes
each fixed subgroup either trivial or a contained root group.

For a possibly disconnected subgroup, `FiniteOrbits` proves the last paragraph
of Borel IV, 14.4(2)(a), from a finite invariant transverse set. The actual
Borel-radical and radical-intersection applications below keep the two
geometric inputs explicit: the fixed-subgroup classification and construction
of this transverse set. They are conditional reductions, not yet the
unconditional generation theorem of GLS3, 1.9.5(i) used in 1.11.4.

Sources: `refs/KGroup/Bor1/Chapter4.tex`, 14.4, and
`refs/KGroup/GLS3/Chapter1.tex`, 1.9.5(i), 1.11.2, 1.11.4.
-/

universe u

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry

open SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

omit [IsAlgClosed k] in
private theorem invariant_le_normalizer {T X : ClosedSubgroup G}
    (hTX : IsClosedSubgroupInvariant T X) : T ≤ X.normalizer := by
  intro t ht
  change t ∈ Subgroup.normalizer (X.toSubgroup : Set (Variety.Point G))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  change x ∈ X ↔ t * x * t⁻¹ ∈ X
  constructor
  · intro hx
    simpa only [inv_inv] using hTX t⁻¹ (T.toSubgroup.inv_mem ht) x hx
  · intro hx
    simpa [mul_assoc] using hTX t ht (t * x * t⁻¹) hx

private theorem unipotent_of_le {X U : ClosedSubgroup G}
    (hXU : X ≤ U) (hU : IsUnipotentAlgebraicGroup U.carrierVariety) :
    IsUnipotentAlgebraicGroup X.carrierVariety := by
  intro x
  have hxX : X.includePoint x ∈ X := (X.pointEquiv x).property
  have hxU : X.includePoint x ∈ U := hXU hxX
  have hu := (closedSubgroup_unipotentElement_iff U hxU).mpr
    (hU (U.pointEquiv.symm ⟨X.includePoint x, hxU⟩))
  have hx := (closedSubgroup_unipotentElement_iff X hxX).mp hu
  have heq : X.pointEquiv.symm ⟨X.includePoint x, hxX⟩ = x := by
    apply X.pointEquiv.injective
    apply Subtype.ext
    exact congrArg Subtype.val (X.pointEquiv.apply_symm_apply _)
  rwa [heq] at hx

private theorem connected_of_oneParameter (R : ClosedSubgroup G)
    (hR : IsOneParameterGroup R.carrierVariety) :
    _root_.IsConnected (R : Set (Variety.Point G)) := by
  let : ConnectedSpace (Variety.Point R.carrierVariety) :=
    connectedSpace_iff_univ.mpr hR.isConnected
  change _root_.IsConnected (R.toSubgroup : Set (Variety.Point G))
  rw [← R.range_inclusion]
  exact isConnected_range R.inclusion.toVariety.continuous

private theorem connected_subgroup_of_oneParameter_eq_bot_or_eq
    (H R : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G)))
    (hR : IsOneParameterGroup R.carrierVariety) (hHR : H ≤ R) :
    H.toSubgroup = ⊥ ∨ H = R := by
  by_cases hbot : H.toSubgroup = ⊥
  · exact Or.inl hbot
  right
  by_contra hne
  have hpos := connected_closedSubgroup_dimension_pos_of_ne_bot H hH hbot
  have hlt := connected_closedSubgroup_dimension_lt_of_le_of_ne H R hHR hne hH
    (connected_of_oneParameter R hR)
  rw [hR.dimension_eq_one] at hlt
  exact (not_lt_of_ge (Cardinal.one_le_iff_pos.mpr hpos)) hlt

/-- The connected case of Borel IV, 14.4(2)(a). Fixed groups of codimension-one
subtori generate `X`; each is connected and lies in a single root group of `U`,
so it is either trivial or that whole root group. The two local fixed-group
hypotheses are geometric inputs, not a generation hypothesis. -/
public theorem invariant_connected_generated_by_roots_of_fixed_subgroups
    (T U X : ClosedSubgroup G) (hT : IsSubtorus T)
    (D : RootGroupData G T) (hD : D.IsRealization)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hXU : X ≤ U) (hTX : IsClosedSubgroupInvariant T X)
    (hXc : _root_.IsConnected (X : Set (Variety.Point G)))
    (hUT : (U.pointwiseCentralizer T).toSubgroup = ⊥)
    (hUQ : ∀ Q : CodimensionOneSubtorus T,
      (U.pointwiseCentralizer Q.1).toSubgroup = ⊥ ∨
        ∃ a, U.pointwiseCentralizer Q.1 = D.rootSubgroup a) :
    X.toSubgroup = RootSubgroupGenerated D {a | D.rootSubgroup a ≤ X} := by
  have hTXn := invariant_le_normalizer hTX
  have hXu := unipotent_of_le hXU hU
  have hfixedT : (X.pointwiseCentralizer T).toSubgroup ≤
      RootSubgroupGenerated D {a | D.rootSubgroup a ≤ X} := by
    intro x hx
    have hu : x ∈ (U.pointwiseCentralizer T).toSubgroup := ⟨hXU hx.1, hx.2⟩
    rw [hUT] at hu
    rw [Subgroup.mem_bot.mp hu]
    exact Subgroup.one_mem _
  have hfixedQ (Q : CodimensionOneSubtorus T) :
      (X.pointwiseCentralizer Q.1).toSubgroup ≤
        RootSubgroupGenerated D {a | D.rootSubgroup a ≤ X} := by
    have hle : X.pointwiseCentralizer Q.1 ≤ U.pointwiseCentralizer Q.1 :=
      fun _ hx => ⟨hXU hx.1, hx.2⟩
    rcases hUQ Q with hbot | ⟨a, ha⟩
    · intro x hx
      have hu : x ∈ (U.pointwiseCentralizer Q.1).toSubgroup := hle hx
      rw [hbot] at hu
      rw [Subgroup.mem_bot.mp hu]
      exact Subgroup.one_mem _
    · rw [ha] at hle
      have hc := externalTorusFixed_isConnected_set X Q.1 hXc hXu Q.2.1
        (fun x hx => hTXn (Q.2.2.1 hx))
      rcases connected_subgroup_of_oneParameter_eq_bot_or_eq
          (X.pointwiseCentralizer Q.1) (D.rootSubgroup a) hc
          (hD.2.2.1 a).1.2 hle with hbot | heq
      · rw [hbot]
        exact bot_le
      · have haX : D.rootSubgroup a ≤ X := by
          rw [← heq]
          exact fun _ hx => hx.1
        rw [heq]
        exact rootSubgroup_le_RootSubgroupGenerated D haX
  apply le_antisymm
  · rw [← externalTorusFixed_generation X T hXc hT hTXn]
    apply (Subgroup.closure_le _).mpr
    rintro x (hx | hx)
    · exact hfixedT hx
    · obtain ⟨Q, hQ⟩ := Set.mem_iUnion.mp hx
      exact hfixedQ Q hQ
  · exact RootSubgroupGenerated_le_of_rootSubgroup_le D _ X.toSubgroup
      (fun _ ha => ha)

/-- Application to the literal radical of a Borel witness. Connectedness of
`X` and the fixed-subgroup geometry remain explicit until the source assembly
discharges them. No connectedness follows merely from `X ≤ U_B`. -/
public theorem invariant_borelRadical_generated_of_connected_fixed_subgroups
    {T B : ClosedSubgroup G} (hT : IsSubtorus T)
    (D : RootGroupData G T) (hD : D.IsRealization)
    {P : Set D.Root} (hBP : IsBorelOfPositiveSystem D P B)
    (X : ClosedSubgroup G) (hXU : X ≤ hBP.unipotent)
    (hTX : IsClosedSubgroupInvariant T X)
    (hXc : _root_.IsConnected (X : Set (Variety.Point G)))
    (hUT : (hBP.unipotent.pointwiseCentralizer T).toSubgroup = ⊥)
    (hUQ : ∀ Q : CodimensionOneSubtorus T,
      (hBP.unipotent.pointwiseCentralizer Q.1).toSubgroup = ⊥ ∨
        ∃ a, hBP.unipotent.pointwiseCentralizer Q.1 = D.rootSubgroup a) :
    X.toSubgroup = RootSubgroupGenerated D {a | D.rootSubgroup a ≤ X} :=
  invariant_connected_generated_by_roots_of_fixed_subgroups
    T hBP.unipotent X hT D hD hBP.radical.2.1 hXU hTX hXc hUT hUQ

/-- The full invariant-subgroup reduction, including the disconnected case.
A finite torus-invariant transverse set supplies the connectedness premise;
the two local fixed-subgroup conclusions supply root generation. -/
public theorem invariant_borelRadical_generated_of_finite_transversal_fixed_subgroups
    {T B : ClosedSubgroup G} (hT : IsSubtorus T)
    (D : RootGroupData G T) (hD : D.IsRealization)
    {P : Set D.Root} (hBP : IsBorelOfPositiveSystem D P B)
    (X : ClosedSubgroup G) (hXU : X ≤ hBP.unipotent)
    (hTX : IsClosedSubgroupInvariant T X)
    (hUT : (hBP.unipotent.pointwiseCentralizer T).toSubgroup = ⊥)
    (hUQ : ∀ Q : CodimensionOneSubtorus T,
      (hBP.unipotent.pointwiseCentralizer Q.1).toSubgroup = ⊥ ∨
        ∃ a, hBP.unipotent.pointwiseCentralizer Q.1 = D.rootSubgroup a)
    (F : Set (Variety.Point G)) (hF : F.Finite) (hFX : F ⊆ X)
    (hTF : ∀ t, t ∈ T → ∀ x, x ∈ F → t⁻¹ * x * t ∈ F)
    (hfactor : ∀ x, x ∈ X → ∃ y, y ∈ X.identityComponentAmbient ∧
      ∃ f, f ∈ F ∧ x = y * f) :
    X.toSubgroup = RootSubgroupGenerated D {a | D.rootSubgroup a ≤ X} := by
  have hXc := invariant_subgroup_connected_of_finite_transversal
    T hBP.unipotent X hT hUT F hF (fun _ hf => hXU (hFX hf)) hTF hfactor
  exact invariant_borelRadical_generated_of_connected_fixed_subgroups
    hT D hD hBP X hXU hTX hXc hUT hUQ

/-- The actual Borel-intersection application of the preceding reduction.
Torus invariance is proved using the relative normality in each Borel. The
transverse set and local fixed-root geometry still need their source proofs. -/
public theorem radical_inter_generated_of_finite_transversal_fixed_subgroups
    {T B C : ClosedSubgroup G} (hT : IsSubtorus T)
    (D : RootGroupData G T) (hD : D.IsRealization)
    {P Q : Set D.Root} (hBP : IsBorelOfPositiveSystem D P B)
    (hCQ : IsBorelOfPositiveSystem D Q C)
    (hUT : (hBP.unipotent.pointwiseCentralizer T).toSubgroup = ⊥)
    (hUQ : ∀ S : CodimensionOneSubtorus T,
      (hBP.unipotent.pointwiseCentralizer S.1).toSubgroup = ⊥ ∨
        ∃ a, hBP.unipotent.pointwiseCentralizer S.1 = D.rootSubgroup a)
    (F : Set (Variety.Point G)) (hF : F.Finite)
    (hFX : F ⊆ hBP.unipotent.inter hCQ.unipotent)
    (hTF : ∀ t, t ∈ T → ∀ x, x ∈ F → t⁻¹ * x * t ∈ F)
    (hfactor : ∀ x, x ∈ hBP.unipotent.inter hCQ.unipotent →
      ∃ y, y ∈ (hBP.unipotent.inter hCQ.unipotent).identityComponentAmbient ∧
        ∃ f, f ∈ F ∧ x = y * f) :
    (hBP.unipotent.inter hCQ.unipotent).toSubgroup =
      RootSubgroupGenerated D
        {a | D.rootSubgroup a ≤ hBP.unipotent.inter hCQ.unipotent} := by
  have hTB : T ≤ B := by
    change T.toSubgroup ≤ B.toSubgroup
    rw [hBP.torus_unipotent_generate]
    exact le_sup_left
  have hTC : T ≤ C := by
    change T.toSubgroup ≤ C.toSubgroup
    rw [hCQ.torus_unipotent_generate]
    exact le_sup_left
  have hTX : IsClosedSubgroupInvariant T
      (hBP.unipotent.inter hCQ.unipotent) := by
    intro t ht x hx
    have htinv : t⁻¹ ∈ T := T.toSubgroup.inv_mem ht
    have hB := hBP.radical.2.2.1 t⁻¹ (hTB htinv) x hx.1
    have hC := hCQ.radical.2.2.1 t⁻¹ (hTC htinv) x hx.2
    change t⁻¹ * x * t ∈ hBP.unipotent ∧ t⁻¹ * x * t ∈ hCQ.unipotent
    simpa only [inv_inv] using And.intro hB hC
  exact invariant_borelRadical_generated_of_finite_transversal_fixed_subgroups
    hT D hD hBP (hBP.unipotent.inter hCQ.unipotent) (fun _ hx => hx.1)
    hTX hUT hUQ F hF hFX hTF hfactor

end Theory.AlgebraicGroup.BorelIntersectionGeometry
