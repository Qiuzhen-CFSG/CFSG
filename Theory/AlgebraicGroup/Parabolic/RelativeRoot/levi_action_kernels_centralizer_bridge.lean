module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.theorem_1_13_3
public import Theory.AlgebraicGroup.RootData.Extrema

/-!
# Levi action-kernel centralizer bridge

This module transfers the source Levi-centralizer equality to a
`ParabolicRelativeRootSetup`.  The setup stores `L` by its aligned Levi
closure and stores `U` by an equality with the generated positive roots, so
the transfer is a short closure argument.  The group-theoretic theorem from
`RootData.Extrema` then turns the intersection equality into the exact
conjugation kernel, with the ambient center retained as the endpoint.

The adjacent-quotient kernel is exposed through a small source-faithfulness
interface: a source proof that layer-2-trivial conjugation already centralizes
the first layer transfers along the same two alignments.
-/

set_option warningAsError false

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma subgroupZariskiClosure_toSubgroup_eq
    {K : Variety k} [AlgebraicGroup K] (H : ClosedSubgroup K) :
    (subgroupZariskiClosure K H.toSubgroup).toSubgroup = H.toSubgroup := by
  apply SetLike.coe_injective
  change closure (H.toSubgroup : Set (Variety.Point K)) =
    (H.toSubgroup : Set (Variety.Point K))
  exact closure_eq_iff_isClosed.mpr H.isClosed'

omit [IsAlgClosed k] in
private lemma sourceUnipotentClosure_toSubgroup_eq
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) :
      (subgroupZariskiClosure K
      (standardUnipotentRootFactor S.D S.positiveRoots S.sigmaJ)).toSubgroup =
      S.U.toSubgroup := by
  rw [standardUnipotentRootFactor, ← S.unipotentRootGeneration]
  exact subgroupZariskiClosure_toSubgroup_eq S.U

omit [IsAlgClosed k] in
private lemma sourceLeviClosure_eq
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) :
    subgroupZariskiClosure K
        (S.T.toSubgroup ⊔ standardLeviRootFactor S.D S.sigmaJ) = S.L := by
  exact S.levi_alignment.symm

omit [IsAlgClosed k] in
private lemma top_centralizer_toSubgroup_eq_center
    {K : Variety k} [AlgebraicGroup K] :
    (ClosedSubgroup.top (G := K)).centralizer.toSubgroup =
      Subgroup.center (Variety.Point K) := by
  ext x
  change x ∈ Subgroup.centralizer (Set.univ : Set (Variety.Point K)) ↔ _
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff]
  simp

omit [IsAlgClosed k] in
private lemma source_levi_centralizer_toSubgroup_eq_center
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K)
    (hsource :
      (subgroupZariskiClosure K
          (S.T.toSubgroup ⊔ standardLeviRootFactor S.D S.sigmaJ)).inter
        (subgroupZariskiClosure K
          (standardUnipotentRootFactor S.D S.positiveRoots S.sigmaJ)).centralizer =
      (ClosedSubgroup.top (G := K)).centralizer) :
    S.L.toSubgroup ⊓
        Subgroup.centralizer (S.U.toSubgroup : Set (Variety.Point K)) =
      Subgroup.center (Variety.Point K) := by
  have hsource' := congrArg (fun H : ClosedSubgroup K => H.toSubgroup) hsource
  rw [top_centralizer_toSubgroup_eq_center] at hsource'
  simpa [sourceLeviClosure_eq S, sourceUnipotentClosure_toSubgroup_eq S,
    ClosedSubgroup.inter, ClosedSubgroup.centralizer,
    ClosedSubgroup.ofSubgroup] using hsource'

/-- Transfer the source theorem in its root-generated closure notation to the
aligned setup. -/
public theorem parabolicRelativeRootSetup_levi_inf_unipotentCentralizer_eq_center
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K)
    (hsource :
      (subgroupZariskiClosure K
          (S.T.toSubgroup ⊔ standardLeviRootFactor S.D S.sigmaJ)).inter
        (subgroupZariskiClosure K
          (standardUnipotentRootFactor S.D S.positiveRoots S.sigmaJ)).centralizer =
      (ClosedSubgroup.top (G := K)).centralizer) :
    S.L.toSubgroup ⊓
        Subgroup.centralizer (S.U.toSubgroup : Set (Variety.Point K)) =
      Subgroup.center (Variety.Point K) := by
  apply source_levi_centralizer_toSubgroup_eq_center S
  exact hsource

/-- The first-layer conjugation kernel is exactly the ambient center. -/
public theorem parabolicRelativeRootSetup_unipotent_conjugation_iff_center
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K)
    (hsource :
      (subgroupZariskiClosure K
          (S.T.toSubgroup ⊔ standardLeviRootFactor S.D S.sigmaJ)).inter
        (subgroupZariskiClosure K
          (standardUnipotentRootFactor S.D S.positiveRoots S.sigmaJ)).centralizer =
      (ClosedSubgroup.top (G := K)).centralizer) :
    ∀ l, l ∈ S.L →
      ((∀ u, u ∈ S.U → l⁻¹ * u * l = u) ↔
        l ∈ Subgroup.center (Variety.Point K)) := by
  exact kernel_of_conjugation_eq_center_of_intersection
    S.L.toSubgroup S.U.toSubgroup
    (parabolicRelativeRootSetup_levi_inf_unipotentCentralizer_eq_center S hsource)

/--
Transfer a source proof that layer-2-trivial conjugation centralizes the first
layer, yielding the second action-kernel characterization.
-/
public theorem parabolicRelativeRootSetup_layer_two_conjugation_iff_center
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K)
    (hsource :
      (subgroupZariskiClosure K
          (S.T.toSubgroup ⊔ standardLeviRootFactor S.D S.sigmaJ)).inter
        (subgroupZariskiClosure K
          (standardUnipotentRootFactor S.D S.positiveRoots S.sigmaJ)).centralizer =
      (ClosedSubgroup.top (G := K)).centralizer)
    (hfaith : ∀ l,
      l ∈ (subgroupZariskiClosure K
          (S.T.toSubgroup ⊔ standardLeviRootFactor S.D S.sigmaJ)).toSubgroup →
      (∀ u,
        u ∈ (subgroupZariskiClosure K
          (standardUnipotentRootFactor S.D S.positiveRoots S.sigmaJ)).toSubgroup →
        l⁻¹ * u * l * u⁻¹ ∈ S.layer 2) →
      ∀ u,
        u ∈ (subgroupZariskiClosure K
          (standardUnipotentRootFactor S.D S.positiveRoots S.sigmaJ)).toSubgroup →
        l⁻¹ * u * l = u) :
    ∀ l, l ∈ S.L →
      ((∀ u, u ∈ S.U → l⁻¹ * u * l * u⁻¹ ∈ S.layer 2) ↔
        l ∈ Subgroup.center (Variety.Point K)) := by
  have hLU :=
    parabolicRelativeRootSetup_levi_inf_unipotentCentralizer_eq_center S hsource
  intro l hl
  change l ∈ S.L.toSubgroup at hl
  constructor
  · intro hquot
    have hfaith' := hfaith l (by simpa [sourceLeviClosure_eq S] using hl)
    have hcent : ∀ u,
        u ∈ (subgroupZariskiClosure K
          (standardUnipotentRootFactor S.D S.positiveRoots S.sigmaJ)).toSubgroup →
        l⁻¹ * u * l = u := by
      apply hfaith'
      intro u hu
      have huU : u ∈ S.U := by
        change u ∈ S.U.toSubgroup
        rw [← sourceUnipotentClosure_toSubgroup_eq S]
        exact hu
      simpa [sourceUnipotentClosure_toSubgroup_eq S] using hquot u huU
    apply (kernel_of_conjugation_eq_center_of_intersection
      S.L.toSubgroup S.U.toSubgroup hLU l hl).mp
    intro u hu
    change u ∈ S.U.toSubgroup at hu
    exact hcent u (by
      simpa [sourceUnipotentClosure_toSubgroup_eq S] using hu)
  · intro hcenter u hu
    have hcomm := (Subgroup.mem_center_iff.mp hcenter) u
    have hconj := congrArg (fun x => l⁻¹ * x) hcomm
    have hdisp := congrArg (fun x => x * u⁻¹) hconj
    have hone : l⁻¹ * u * l * u⁻¹ = 1 := by
      simpa [mul_assoc] using hdisp
    rw [hone]
    exact (S.layer 2).one_mem

end Theory.AlgebraicGroup
