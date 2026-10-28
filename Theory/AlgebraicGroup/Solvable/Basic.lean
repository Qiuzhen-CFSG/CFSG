module

public import Theory.AlgebraicGroup.ClosedSubgroup.Closure
public import Theory.AlgebraicGroup.ClosedSubgroup.Connected

universe u

set_option linter.style.haveILetI false

/-! Closed normal series for solvable algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A finite closed normal series whose successive quotients are abelian. -/
public inductive HasClosedNormalAbelianSeries
    (G : Variety k) [AlgebraicGroup G] : Prop where
  | intro
      (length : ℕ)
      (subgroup : ℕ → ClosedSubgroup G)
      (head_eq : subgroup 0 = ClosedSubgroup.top)
      (last_eq : subgroup length = ClosedSubgroup.bot)
      (normal : ∀ i, i ≤ length → (subgroup i).toSubgroup.Normal)
      (step_le : ∀ i, i < length → subgroup (i + 1) ≤ subgroup i)
      (commutator_le : ∀ i, i < length →
        ⁅(subgroup i).toSubgroup, (subgroup i).toSubgroup⁆ ≤
          (subgroup (i + 1)).toSubgroup) :
      HasClosedNormalAbelianSeries G

/-- A closed normal series with abelian successive quotients implies abstract
solvability of the rational-point group. -/
public theorem isSolvable_of_hasClosedNormalAbelianSeries
    (G : Variety k) [AlgebraicGroup G]
    (hseries : HasClosedNormalAbelianSeries G) :
    Group.IsSolvable (Variety.Point G) := by
  rcases hseries with
    ⟨length, subgroup, head_eq, last_eq, _, _, commutator_le⟩
  refine ⟨⟨length, le_antisymm ?_ bot_le⟩⟩
  have hderived : ∀ i, i ≤ length →
      derivedSeries (Variety.Point G) i ≤ (subgroup i).toSubgroup := by
    intro i hi
    induction i with
    | zero =>
        rw [derivedSeries_zero, head_eq]
        exact le_top
    | succ i ih =>
        rw [derivedSeries_succ]
        have hin : i < length := Nat.lt_of_succ_le hi
        exact (Subgroup.commutator_mono (ih hin.le) (ih hin.le)).trans
          (by simpa [Nat.succ_eq_add_one] using commutator_le i hin)
  have hlast := hderived length le_rfl
  rw [last_eq] at hlast
  exact hlast

/-- A solvable algebraic group has a finite chain of closed normal subgroups
with abelian successive quotients. -/
public theorem hasClosedNormalAbelianSeries_of_isSolvable
    (G : Variety k) [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G)) :
    HasClosedNormalAbelianSeries G := by
  rcases hsolvable with ⟨⟨n, hn⟩⟩
  let H : ℕ → ClosedSubgroup G := fun i =>
    subgroupZariskiClosure G (derivedSeries (Variety.Point G) i)
  refine ⟨n, H, ?_, ?_, ?_, ?_, ?_⟩
  · apply SetLike.coe_injective
    ext x
    change x ∈ closure ((⊤ : Subgroup (Variety.Point G)) :
      Set (Variety.Point G)) ↔ x ∈ (⊤ : Subgroup (Variety.Point G))
    simp
  · apply SetLike.coe_injective
    ext x
    change x ∈ closure (derivedSeries (Variety.Point G) n :
      Set (Variety.Point G)) ↔ x ∈ (⊥ : Subgroup (Variety.Point G))
    rw [hn]
    change x ∈ closure ({1} : Set (Variety.Point G)) ↔
      x ∈ ({1} : Set (Variety.Point G))
    rw [(Variety.isClosed_iff_isZariskiClosed.mpr
      (isZariskiClosed_singleton G (1 : Variety.Point G))).closure_eq]
  · intro i _
    exact subgroupZariskiClosure_isNormal G
      (derivedSeries (Variety.Point G) i)
      (derivedSeries_normal (Variety.Point G) i)
  · intro i _
    change closure (derivedSeries (Variety.Point G) (i + 1) :
        Set (Variety.Point G)) ⊆
      closure (derivedSeries (Variety.Point G) i :
        Set (Variety.Point G))
    exact closure_mono
      (derivedSeries_antitone (Variety.Point G) (Nat.le_succ i))
  · intro i _
    simpa [H, derivedSeries_succ] using
      commutator_subgroupZariskiClosure_le G
        (derivedSeries (Variety.Point G) i)

/-- An algebraic group is solvable exactly when it has a finite chain of
closed normal subgroups with abelian successive quotients. -/
public theorem isSolvable_iff_hasClosedNormalAbelianSeries
    (G : Variety k) [AlgebraicGroup G] :
    Group.IsSolvable (Variety.Point G) ↔ HasClosedNormalAbelianSeries G :=
  ⟨hasClosedNormalAbelianSeries_of_isSolvable G,
    isSolvable_of_hasClosedNormalAbelianSeries G⟩

/-- In a nontrivial solvable algebraic group, the Zariski closure of the
abstract commutator subgroup is proper. -/
public theorem subgroupZariskiClosure_commutator_ne_top_of_isSolvable
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hnontrivial : Nontrivial (Variety.Point G)) :
    subgroupZariskiClosure G (commutator (Variety.Point G)) ≠
      ClosedSubgroup.top := by
  intro htop
  rcases hsolvable with ⟨⟨n, hn⟩⟩
  have hall : ∀ i : ℕ,
      subgroupZariskiClosure G (derivedSeries (Variety.Point G) i) =
        ClosedSubgroup.top := by
    intro i
    induction i with
    | zero =>
        apply SetLike.coe_injective
        ext x
        change x ∈ closure (Set.univ : Set (Variety.Point G)) ↔ True
        simp
    | succ i ih =>
        apply SetLike.coe_injective
        apply Set.Subset.antisymm
        · exact fun _ _ => trivial
        · intro x _
          have hcommle := commutator_subgroupZariskiClosure_le G
            (derivedSeries (Variety.Point G) i)
          have htopsub : (subgroupZariskiClosure G
              (derivedSeries (Variety.Point G) i)).toSubgroup = ⊤ := by
            rw [ih]
            rfl
          rw [htopsub] at hcommle
          have htopcomm : commutator (Variety.Point G) ≤
              (subgroupZariskiClosure G
                (derivedSeries (Variety.Point G) (i + 1))).toSubgroup := by
            simpa [derivedSeries_succ, commutator_def] using hcommle
          have hDle : (subgroupZariskiClosure G
              (commutator (Variety.Point G))).toSubgroup ≤
              (subgroupZariskiClosure G
                (derivedSeries (Variety.Point G) (i + 1))).toSubgroup := by
            intro y hy
            change y ∈ closure
              (commutator (Variety.Point G) : Set (Variety.Point G)) at hy
            exact (closure_minimal htopcomm
              (Variety.isClosed_iff_isZariskiClosed.mpr
                (subgroupZariskiClosure G
                  (derivedSeries (Variety.Point G) (i + 1))).isZariskiClosed)) hy
          rw [htop] at hDle
          exact hDle trivial
  have hnclosure := hall n
  rw [hn] at hnclosure
  have hbotclosure : subgroupZariskiClosure G (⊥ : Subgroup (Variety.Point G)) =
      ClosedSubgroup.bot := by
    apply SetLike.coe_injective
    ext x
    change x ∈ closure ({1} : Set (Variety.Point G)) ↔ x = 1
    rw [(Variety.isClosed_iff_isZariskiClosed.mpr
      (isZariskiClosed_singleton G (1 : Variety.Point G))).closure_eq]
    simp
  rw [hbotclosure] at hnclosure
  have hne : (ClosedSubgroup.bot : ClosedSubgroup G) ≠ ClosedSubgroup.top := by
    intro h
    have hallmem (x : Variety.Point G) : x = 1 := by
      apply Subgroup.mem_bot.mp
      change x ∈ (ClosedSubgroup.bot : ClosedSubgroup G).toSubgroup
      rw [h]
      trivial
    exact not_subsingleton (Variety.Point G)
      (Subsingleton.intro fun x y => (hallmem x).trans (hallmem y).symm)
  exact hne hnclosure

/-- The Zariski closure of the abstract commutator subgroup of a
connected algebraic group is connected. -/
public theorem subgroupZariskiClosure_commutator_isConnected
    [IsAlgClosed k] {G : Variety k} [AlgebraicGroup G]
    (hG : Variety.IsConnected G) :
    _root_.IsConnected
      ((subgroupZariskiClosure G (commutator (Variety.Point G))) :
        Set (Variety.Point G)) := by
  let D : ClosedSubgroup G :=
    subgroupZariskiClosure G (commutator (Variety.Point G))
  letI : AlgebraicGroup D.carrierVariety := D.carrierAlgebraicGroup
  let c := AlgebraicGroup.commutatorMorphism G
  have hcmap (z : Variety.Point (Variety.prod G G)) :
      c.toFun z ∈ D.toSubgroup := by
    change c.toFun z ∈ closure
      (commutator (Variety.Point G) : Set (Variety.Point G))
    apply subset_closure
    obtain ⟨⟨x, y⟩, rfl⟩ := (Variety.prodPointEquiv G G).symm.surjective z
    rw [AlgebraicGroup.commutatorMorphism_apply]
    exact Subgroup.commutator_mem_commutator
      (H₁ := ⊤) (H₂ := ⊤) trivial trivial
  let q : Variety.Morphism (Variety.prod G G) D.carrierVariety :=
    { toFun := fun z => D.pointEquiv.symm ⟨c.toFun z, hcmap z⟩
      regular := by
        intro i
        rcases c.regular i with ⟨p, hp⟩
        exact ⟨p, fun z => by
          change (D.pointEquiv (D.pointEquiv.symm
            ⟨c.toFun z, hcmap z⟩)).val.val i = _
          rw [D.pointEquiv.apply_symm_apply]
          exact hp z⟩ }
  have hqinc (z : Variety.Point (Variety.prod G G)) :
      D.inclusion.onPoints (q.toFun z) = c.toFun z := by
    change (D.pointEquiv (D.pointEquiv.symm
      ⟨c.toFun z, hcmap z⟩)).val = c.toFun z
    rw [D.pointEquiv.apply_symm_apply]
  have hprodConnected : Variety.IsConnected (Variety.prod G G) := by
    have hI := prodSet_irreducible_of_irreducible
      (connectedAlgebraicGroup_irreducible G hG)
      (connectedAlgebraicGroup_irreducible G hG)
    have hprod : Variety.prodSet
        (Set.univ : Set (Variety.Point G))
        (Set.univ : Set (Variety.Point G)) =
        (Set.univ : Set (Variety.Point (Variety.prod G G))) := by
      ext z
      simp [Variety.prodSet]
    rw [hprod] at hI
    exact hI.isConnected
  have hrange : _root_.IsConnected (Set.range q.toFun) := by
    rw [← Set.image_univ]
    exact hprodConnected.image q.toFun q.continuous.continuousOn
  have hone : (1 : Variety.Point D.carrierVariety) ∈ Set.range q.toFun := by
    refine ⟨(Variety.prodPointEquiv G G).symm (1, 1), ?_⟩
    apply D.inclusion_injective
    rw [hqinc, AlgebraicGroup.commutatorMorphism_apply]
    simp
  have hrange0 : Set.range q.toFun ⊆
      AlgebraicGroup.identityComponent D.carrierVariety :=
    hrange.subset_connectedComponent hone
  have hcomm : commutator (Variety.Point G) ≤
      D.identityComponentAmbient.toSubgroup := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    intro z hz
    rcases hz with ⟨x, y, rfl⟩
    let p : Variety.Point (Variety.prod G G) :=
      (Variety.prodPointEquiv G G).symm (x, y)
    apply (ClosedSubgroup.mem_identityComponentAmbient_iff D _).mpr
    refine ⟨q.toFun p, hrange0 ⟨p, rfl⟩, ?_⟩
    rw [hqinc]
    exact AlgebraicGroup.commutatorMorphism_apply G x y
  have hDle : D ≤ D.identityComponentAmbient := by
    intro z hz
    change z ∈ closure
      (commutator (Variety.Point G) : Set (Variety.Point G)) at hz
    exact (closure_minimal hcomm
      (Variety.isClosed_iff_isZariskiClosed.mpr
        D.identityComponentAmbient.isZariskiClosed)) hz
  have hEq : D = D.identityComponentAmbient := by
    apply SetLike.coe_injective
    exact Set.Subset.antisymm hDle D.identityComponentAmbient_le
  change _root_.IsConnected (D : Set (Variety.Point G))
  rw [hEq]
  exact D.identityComponentAmbient_isConnected

end Theory.AlgebraicGroup
