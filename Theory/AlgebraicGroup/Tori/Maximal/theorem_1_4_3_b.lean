module

public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.ClosedSubgroup.Maximal
public import Theory.AlgebraicGroup.Tori.Power

/-!
This module isolates `theorem_1_4_3_b` from `Theory.AlgebraicGroup.Tori.Maximal`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u

set_option linter.style.haveILetI false

/-! Maximality conditions for tori in an ambient algebraic group. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The local maximality condition for a torus inside a fixed closed
subgroup. -/
@[expose]
public def IsTorusMaximalIn
    {G : Variety k} [AlgebraicGroup G]
    (T B : ClosedSubgroup G) : Prop :=
  IsSubtorus T ∧ T ≤ B ∧
    ∀ S : ClosedSubgroup G, IsSubtorus S → S ≤ B → T ≤ S → S = T

/-- A maximal torus is a subtorus. -/
public lemma IsMaximalTorus.isSubtorus
    {G : Variety k} [AlgebraicGroup G]
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    IsSubtorus T :=
  hT.1

/-- A subtorus containing a maximal torus is equal to it. -/
public lemma IsMaximalTorus.maximal_of_le
    {G : Variety k} [AlgebraicGroup G]
    {T S : ClosedSubgroup G}
    (hT : IsMaximalTorus T) (hS : IsSubtorus S) (hTS : T ≤ S) :
    S = T :=
  hT.2 S hS hTS

/-- The trivial closed subgroup is the rank-zero torus. -/
public lemma closedSubgroup_bot_isTorus
    [IsAlgClosed k]
    (G : Variety k) [AlgebraicGroup G] :
    IsSubtorus (ClosedSubgroup.bot : ClosedSubgroup G) := by
  let B : ClosedSubgroup G := ClosedSubgroup.bot
  letI : AlgebraicGroup B.carrierVariety := B.carrierAlgebraicGroup
  change IsTorus B.carrierVariety
  refine ⟨0, ⟨?_⟩⟩
  let toB : AlgebraicGroup.Morphism (dVariety k 0) B.carrierVariety :=
    { toVariety := Variety.Morphism.const _ _ 1
      map_one := rfl
      map_mul := by
        intro _ _
        exact (one_mul (1 : Variety.Point B.carrierVariety)).symm }
  let fromB : AlgebraicGroup.Morphism B.carrierVariety (dVariety k 0) :=
    { toVariety := Variety.Morphism.const _ _ 1
      map_one := rfl
      map_mul := by
        intro _ _
        exact (one_mul (1 : Variety.Point (dVariety k 0))).symm }
  exact
    { hom := toB
      inv := fromB
      hom_inv_id := by
        intro x
        apply (dPointEquiv 0).injective
        funext i
        exact Fin.elim0 i
      inv_hom_id := by
        intro y
        apply B.inclusion_injective
        change (B.pointEquiv 1).val = (B.pointEquiv y).val
        have hy : (B.pointEquiv y).val ∈ B.toSubgroup :=
          (B.pointEquiv y).property
        change (B.pointEquiv y).val ∈
          (⊥ : Subgroup (Variety.Point G)) at hy
        have hone : (B.pointEquiv 1).val = (1 : Variety.Point G) := rfl
        rw [hone, hy] }

/-- Every algebraic group contains a maximal torus. -/
public theorem exists_maximalTorus
    [IsAlgClosed k]
    (G : Variety k) [AlgebraicGroup G] :
    ∃ T : ClosedSubgroup G, IsMaximalTorus T := by
  obtain ⟨T, hT, hmax⟩ := exists_maximal_connected_closedSubgroup G
    IsSubtorus
    ⟨ClosedSubgroup.bot, closedSubgroup_bot_isTorus G⟩
    (fun S hS => by
      have hSvar : Variety.IsConnected S.carrierVariety := hS.isConnected
      let : ConnectedSpace (Variety.Point S.carrierVariety) :=
        connectedSpace_iff_univ.mpr hSvar
      change _root_.IsConnected (S.toSubgroup : Set (Variety.Point G))
      rw [← S.range_inclusion]
      exact isConnected_range S.inclusion.toVariety.continuous)
  exact ⟨T, hT, hmax⟩

/-- Every subtorus is contained in a maximal torus. -/
public theorem exists_maximalTorus_containing
    [IsAlgClosed k]
    {G : Variety k} [AlgebraicGroup G]
    (T : ClosedSubgroup G) (hT : IsSubtorus T) :
    ∃ M : ClosedSubgroup G, IsMaximalTorus M ∧ T ≤ M := by
  obtain ⟨M, hM, hmax⟩ := exists_maximal_connected_closedSubgroup G
    (fun S => IsSubtorus S ∧ T ≤ S)
    ⟨T, hT, fun _ hx => hx⟩
    (fun S hS => by
      have hSvar : Variety.IsConnected S.carrierVariety := hS.1.isConnected
      let : ConnectedSpace (Variety.Point S.carrierVariety) :=
        connectedSpace_iff_univ.mpr hSvar
      change _root_.IsConnected (S.toSubgroup : Set (Variety.Point G))
      rw [← S.range_inclusion]
      exact isConnected_range S.inclusion.toVariety.continuous)
  refine ⟨M, ⟨hM.1, ?_⟩, hM.2⟩
  intro S hS hMS
  exact hmax S ⟨hS, fun x hx => hMS (hM.2 hx)⟩ hMS

/-- Every element of a maximal torus centralizes the torus. -/
public lemma maximalTorus_le_centralizer
    {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
    (hT : IsMaximalTorus T) : T ≤ T.centralizer := by
  have hcomm : IsMulCommutative (Variety.Point T.carrierVariety) :=
    hT.isSubtorus.isMulCommutative
  rw [isMulCommutative_iff] at hcomm
  intro x hx
  change x ∈ Subgroup.centralizer (T.toSubgroup : Set (Variety.Point G))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let xT : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨x, hx⟩
  let yT : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨y, hy⟩
  have hxy : yT * xT = xT * yT := hcomm yT xT
  have hinc := congrArg T.inclusion.onPoints hxy
  have hxval : T.inclusion.onPoints xT = x := by
    change (T.pointEquiv xT).val = x
    dsimp [xT]
    rw [T.pointEquiv.apply_symm_apply]
  have hyval : T.inclusion.onPoints yT = y := by
    change (T.pointEquiv yT).val = y
    dsimp [yT]
    rw [T.pointEquiv.apply_symm_apply]
  rw [map_mul, map_mul, hxval, hyval] at hinc
  exact hinc

/-- A maximal torus contained in a closed subgroup lies in its ambient
identity component. -/
public theorem maximalTorus_le_identityComponentAmbient_of_le
    [IsAlgClosed k]
    {G : Variety k} [AlgebraicGroup G]
    (T X : ClosedSubgroup G) (hT : IsMaximalTorus T) (hTX : T ≤ X) :
    T ≤ X.identityComponentAmbient := by
  have hTvar : Variety.IsConnected T.carrierVariety :=
    IsSubtorus.isConnected hT.1
  let : ConnectedSpace (Variety.Point T.carrierVariety) :=
    connectedSpace_iff_univ.mpr hTvar
  have hTconn : _root_.IsConnected (T : Set (Variety.Point G)) := by
    change _root_.IsConnected (T.toSubgroup : Set (Variety.Point G))
    rw [← T.range_inclusion]
    exact isConnected_range T.inclusion.toVariety.continuous
  exact connected_closedSubgroup_le_identityComponentAmbient T X hTconn hTX

/-- Maximality identifies a maximal torus with its centralizer once the
centralizer is known to be a torus. -/
public lemma maximalTorus_centralizer_eq_of_isTorus
    {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
    (hT : IsMaximalTorus T)
    (hcentralizer : IsTorus T.centralizer.carrierVariety) :
    T.centralizer.toSubgroup = T.toSubgroup := by
  have hEq : T.centralizer = T :=
    hT.2 T.centralizer hcentralizer (maximalTorus_le_centralizer hT)
  exact congrArg (fun S : ClosedSubgroup G => S.toSubgroup) hEq

/-- A maximal torus maps into the identity component of its centralizer. -/
public lemma maximalTorus_le_centralizer_identityComponent
    [IsAlgClosed k]
    {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
    (hT : IsMaximalTorus T) :
    T.toSubgroup ≤
      (AlgebraicGroup.identityComponentSubgroup T.centralizer.carrierVariety).map
        T.centralizer.inclusion.onPoints := by
  let C := T.centralizer
  have hTC : T ≤ C := maximalTorus_le_centralizer hT
  let j : AlgebraicGroup.Morphism T.carrierVariety C.carrierVariety :=
    T.inclusion.codRestrictClosedSubgroup C fun x => hTC (T.pointEquiv x).property
  have himageConnected : _root_.IsConnected (j.onPoints '' Set.univ) :=
    hT.1.isConnected.image j.onPoints j.toVariety.continuous.continuousOn
  have hone : (1 : Variety.Point C.carrierVariety) ∈ j.onPoints '' Set.univ :=
    ⟨1, Set.mem_univ _, j.map_one⟩
  have himageSub : j.onPoints '' Set.univ ⊆
      AlgebraicGroup.identityComponent C.carrierVariety :=
    himageConnected.subset_connectedComponent hone
  intro x hx
  let xT : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨x, hx⟩
  have hxj : j.onPoints xT ∈
      AlgebraicGroup.identityComponentSubgroup C.carrierVariety :=
    himageSub ⟨xT, Set.mem_univ _, rfl⟩
  refine ⟨j.onPoints xT, hxj, ?_⟩
  rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
  change (T.pointEquiv xT).val = x
  dsimp [xT]
  rw [T.pointEquiv.apply_symm_apply]

section

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option warningAsError false in
public theorem theorem_1_4_3_b
    {G : Variety k} [AlgebraicGroup G] {T₁ T₂ : ClosedSubgroup G}
    (hT₁ : IsMaximalTorus T₁) (hT₂ : IsMaximalTorus T₂) :
    ∃ g : Variety.Point G, T₂ = T₁.conjugate g := by sorry

end

end Theory.AlgebraicGroup
