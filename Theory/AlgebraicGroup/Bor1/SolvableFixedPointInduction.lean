module

public import Theory.AlgebraicGroup.Variety.MorphicActionPullback
public import Theory.AlgebraicGroup.Variety.MorphicActionFixedLocus
public import Theory.AlgebraicGroup.Solvable.Basic
public import Theory.AlgebraicGroup.Dimension.Finite

/-!
# Solvable fixed-point induction

This module proves the induction in Borel, *Linear Algebraic Groups*, §10.4
(`refs/KGroup/Bor1/Chapter3.tex`), reducing the fixed-point theorem to actions
whose commutator subgroup acts trivially. The Zariski closure of the derived
subgroup is connected and proper in a nontrivial solvable algebraic group,
so it has smaller dimension. Induction makes its closed fixed locus nonempty;
normality supplies the ambient action on this complete locus.

The remaining geometric case is an explicit hypothesis here. It must be
discharged using a smooth closed orbit and the affine normal-stabilizer
quotient before this reduction yields the source fixed-point theorem.
-/

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup.Variety.Geometric.MorphicAction

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The dimension induction in Bor1 §10.4: it suffices to prove the fixed-point
theorem for connected morphic actions with trivial commutator action. -/
public theorem exists_fixedPoint_of_commutator_trivial_case
    (hcomm : ∀ (H : Theory.AlgebraicGroup.Variety k) [AlgebraicGroup H]
      (Y : Geometric k) (B : MorphicAction H Y),
      Variety.IsConnected H → IsComplete Y → Nonempty (Point Y) →
      (∀ c ∈ commutator (Variety.Point H), ∀ y : Point Y, B.toMulAction.smul c y = y) →
      ∃ y : Point Y, ∀ h : Variety.Point H, B.toMulAction.smul h y = y)
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (hG : Variety.IsConnected G) (hsol : Group.IsSolvable (Variety.Point G))
    (hX : IsComplete X) (hne : Nonempty (Point X)) :
    ∃ x : Point X, ∀ g : Variety.Point G, A.toMulAction.smul g x = x := by
  have hind : ∀ n : ℕ, ∀ (H : Theory.AlgebraicGroup.Variety k) [AlgebraicGroup H],
      Cardinal.toNat (Variety.dimension H) = n →
      ∀ (Y : Geometric k) (B : MorphicAction H Y),
      Variety.IsConnected H → Group.IsSolvable (Variety.Point H) →
      IsComplete Y → Nonempty (Point Y) →
      ∃ y : Point Y, ∀ h : Variety.Point H, B.toMulAction.smul h y = y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H _ hdim Y B hH hsolH hY hYne
      classical
      by_cases htriv : Subsingleton (Variety.Point H)
      · obtain ⟨y⟩ := hYne
        refine ⟨y, fun h => ?_⟩
        rw [htriv.elim h 1]
        exact B.toMulAction.one_smul y
      · letI : Nontrivial (Variety.Point H) := not_subsingleton_iff_nontrivial.mp htriv
        let D := subgroupZariskiClosure H (commutator (Variety.Point H))
        have hDconn : _root_.IsConnected (D : Set (Variety.Point H)) :=
          subgroupZariskiClosure_commutator_isConnected hH
        have hDproper : D ≠ ClosedSubgroup.top :=
          subgroupZariskiClosure_commutator_ne_top_of_isSolvable hsolH inferInstance
        have hDdim : Variety.dimension D.carrierVariety < Variety.dimension H := by
          have hlt := connected_closedSubgroup_dimension_lt_of_le_of_ne D
            ClosedSubgroup.top (fun _ _ => trivial) hDproper hDconn hH
          exact hlt.trans_le (closedSubvariety_dimension_le H ClosedSubgroup.top.isZariskiClosed)
        have hDdimNat : Cardinal.toNat (Variety.dimension D.carrierVariety) < n := by
          rw [← hdim]
          exact Cardinal.toNat_lt_toNat hDdim (variety_dimension_lt_aleph0 H)
        have hDcarrier : Variety.IsConnected D.carrierVariety := by
          letI : ConnectedSpace (D : Set (Variety.Point H)) := Subtype.connectedSpace hDconn
          letI : ConnectedSpace (Variety.Point D.carrierVariety) :=
            (Variety.closedSubvarietyPointHomeomorph D.isZariskiClosed).connectedSpace_iff.mpr
              inferInstance
          exact connectedSpace_iff_univ.mp inferInstance
        letI : Group.IsSolvable (Variety.Point H) := hsolH
        have hDsol : Group.IsSolvable (Variety.Point D.carrierVariety) :=
          Group.isSolvable_of_isSolvable_injective D.inclusion_injective
        obtain ⟨y, hy⟩ := ih _ hDdimNat D.carrierVariety rfl Y
          (B.pullbackGroup D.inclusion) hDcarrier hDsol hY hYne
        have hyD : ∀ d : D.toSubgroup, B.toMulAction.smul (d : Variety.Point H) y = y := by
          intro d
          have hd := hy (D.pointEquiv.symm d)
          rw [pullbackGroup_smul] at hd
          change B.toMulAction.smul (D.pointEquiv (D.pointEquiv.symm d)).val y = y at hd
          simpa only [Equiv.apply_symm_apply] using hd
        have hDnormal : D.toSubgroup.Normal :=
          subgroupZariskiClosure_isNormal H (commutator (Variety.Point H)) inferInstance
        let F := B.subgroupFixedLocus D.toSubgroup
        let C := B.onSubgroupFixedLocus D.toSubgroup hDnormal
        have hFne : Nonempty (Point F.toGeometric) :=
          B.subgroupFixedLocus_nonempty D.toSubgroup ⟨y, hyD⟩
        obtain ⟨z, hz⟩ := hcomm H F.toGeometric C hH
          (B.subgroupFixedLocus_isComplete D.toSubgroup hY) hFne (by
            intro c hc z
            have hcD : c ∈ D.toSubgroup := subset_closure hc
            exact B.onSubgroupFixedLocus_subgroup_fixed D.toSubgroup hDnormal z ⟨c, hcD⟩)
        refine ⟨F.inclusion z, fun h => ?_⟩
        exact (B.onSubgroupFixedLocus_smul D.toSubgroup hDnormal h z).symm.trans
          (congrArg (fun w : Point F.toGeometric => F.inclusion w) (hz h))
  exact hind _ G rfl X A hG hsol hX hne

end Theory.AlgebraicGroup.Variety.Geometric.MorphicAction
