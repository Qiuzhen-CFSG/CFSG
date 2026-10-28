module

public import Theory.AlgebraicGroup.ClosedSubgroup.CentralSeries

universe u

/-! Centralizers as closed subgroups of algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The centralizer of a closed subgroup is Zariski closed. -/
public lemma ClosedSubgroup.centralizer_isZariskiClosed
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    IsZariskiClosed G
      (Subgroup.centralizer (H.toSubgroup : Set (Variety.Point G)) :
        Set (Variety.Point G)) := by
  let S : H.toSubgroup → Set (Variety.Point G) := fun h ↦
    {g | (Theory.AlgebraicGroup.leftMulMorphism G h.val).toFun g =
      (Theory.AlgebraicGroup.rightMulMorphism G h.val).toFun g}
  have hclosed : IsZariskiClosed G (⋂ h, S h) :=
    isZariskiClosed_iInter S fun h ↦
      Variety.Morphism.isZariskiClosed_equalizer
        (Theory.AlgebraicGroup.leftMulMorphism G h.val)
        (Theory.AlgebraicGroup.rightMulMorphism G h.val)
  have hset :
      (Subgroup.centralizer (H.toSubgroup : Set (Variety.Point G)) :
          Set (Variety.Point G)) = ⋂ h, S h := by
    ext g
    constructor
    · intro hg
      rw [Set.mem_iInter]
      intro h
      change (Theory.AlgebraicGroup.leftMulMorphism G h.val).toFun g =
        (Theory.AlgebraicGroup.rightMulMorphism G h.val).toFun g
      rw [Theory.AlgebraicGroup.leftMulMorphism_apply,
        Theory.AlgebraicGroup.rightMulMorphism_apply]
      exact (Subgroup.mem_centralizer_iff.mp hg) h.val h.property
    · intro hg
      change g ∈ Subgroup.centralizer
        (H.toSubgroup : Set (Variety.Point G))
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hcomm := Set.mem_iInter.mp hg ⟨h, hh⟩
      change (Theory.AlgebraicGroup.leftMulMorphism G h).toFun g =
        (Theory.AlgebraicGroup.rightMulMorphism G h).toFun g at hcomm
      rw [Theory.AlgebraicGroup.leftMulMorphism_apply,
        Theory.AlgebraicGroup.rightMulMorphism_apply] at hcomm
      exact hcomm
  rw [hset]
  exact hclosed

/-- The centralizer as a closed subgroup. -/
@[expose]
public def ClosedSubgroup.centralizer {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) : ClosedSubgroup G :=
  ClosedSubgroup.ofSubgroup
    (Subgroup.centralizer (H.toSubgroup : Set (Variety.Point G)))
    H.centralizer_isZariskiClosed

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A positive-dimensional nilpotent algebraic group has
positive-dimensional center. -/
public theorem positive_dimension_centralizer_of_nilpotent
    {G : Variety k} [AlgebraicGroup G]
    (hG : Group.IsNilpotent (Variety.Point G))
    (hpositive : 0 < Variety.dimension G) :
    0 < Variety.dimension
      (ClosedSubgroup.centralizer
        (ClosedSubgroup.top (G := G))).carrierVariety := by
  let I : ClosedSubgroup G := AlgebraicGroup.identityComponentClosedSubgroup G
  let S : Subgroup (Variety.Point G) := I.toSubgroup
  have hSconn : _root_.IsConnected (S : Set (Variety.Point G)) := by
    change _root_.IsConnected (AlgebraicGroup.identityComponent G)
    exact AlgebraicGroup.identityComponent_isConnected G
  have hleL : ∀ n, relativeLowerCentralSeries G S n ≤
      Subgroup.lowerCentralSeries (⊤ : Subgroup (Variety.Point G)) n :=
    relativeLowerCentralSeries_le_lowerCentralSeries S
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hG
  have hterminal : relativeLowerCentralSeries G S n = ⊥ := by
    apply le_antisymm
    · have hle := hleL n
      rw [hn] at hle
      exact hle
    · exact bot_le
  have hIne : I.toSubgroup ≠ ⊥ := by
    intro hbot
    have hIbot : I = ClosedSubgroup.bot := by
      apply SetLike.coe_injective
      exact congrArg (fun H : Subgroup (Variety.Point G) ↦
        (H : Set (Variety.Point G))) hbot
    let B : ClosedSubgroup G := ClosedSubgroup.bot
    have hdimB : Variety.dimension B.carrierVariety = 0 := by
      apply (dimension_zero_iff_finite_points B.carrierVariety).2
      let : Subsingleton B.toSubgroup := by
        constructor
        intro x y
        apply Subtype.ext
        exact (Subgroup.mem_bot.mp x.property).trans
          (Subgroup.mem_bot.mp y.property).symm
      let : Subsingleton (Variety.Point B.carrierVariety) :=
        B.pointEquiv.subsingleton
      exact Finite.of_subsingleton
    have hdimI : Variety.dimension I.carrierVariety = 0 := by
      rw [hIbot]
      exact hdimB
    have hdimIpos : 0 < Variety.dimension I.carrierVariety := by
      rw [AlgebraicGroup.dimension_identityComponentClosedSubgroup G]
      exact hpositive
    exact (ne_of_gt hdimIpos) hdimI
  classical
  let hex : ∃ m, relativeLowerCentralSeries G S m = ⊥ := ⟨n, hterminal⟩
  let m := Nat.find hex
  have hm : relativeLowerCentralSeries G S m = ⊥ := Nat.find_spec hex
  have hmin : ∀ q < m, relativeLowerCentralSeries G S q ≠ ⊥ := by
    intro q hq
    exact Nat.find_min hex hq
  have hp0 : ¬ relativeLowerCentralSeries G S 0 = ⊥ := by
    simpa [relativeLowerCentralSeries] using hIne
  have hmpos : 0 < m := (Nat.find_pos hex).2 hp0
  let j := m - 1
  have hjm : j < m := by
    dsimp [j]
    omega
  have hjone : j + 1 = m := by
    dsimp [j]
    omega
  have hjne : relativeLowerCentralSeries G S j ≠ ⊥ := hmin j hjm
  let C : ClosedSubgroup G := subgroupZariskiClosure G
    (relativeLowerCentralSeries G S j)
  have hCconn : _root_.IsConnected (C : Set (Variety.Point G)) :=
    relativeLowerCentralSeries_closure_connected S hSconn j
  have hCnebot : C.toSubgroup ≠ ⊥ := by
    intro hCbot
    have hraw : relativeLowerCentralSeries G S j ≤ C.toSubgroup := by
      intro x hx
      exact subset_closure hx
    rw [hCbot] at hraw
    exact hjne (le_bot_iff.mp hraw)
  have hCdim : 0 < Variety.dimension C.carrierVariety :=
    connected_closedSubgroup_dimension_pos_of_ne_bot C hCconn hCnebot
  have hclosure_top : subgroupZariskiClosure G
      (⊤ : Subgroup (Variety.Point G)) = ClosedSubgroup.top := by
    apply SetLike.coe_injective
    change closure (Set.univ : Set (Variety.Point G)) = Set.univ
    exact closure_univ
  have hclosure_bot : subgroupZariskiClosure G
      (⊥ : Subgroup (Variety.Point G)) = ClosedSubgroup.bot := by
    apply SetLike.coe_injective
    change closure ({1} : Set (Variety.Point G)) = ({1} : Set (Variety.Point G))
    rw [(Variety.isClosed_iff_isZariskiClosed.mpr
      (isZariskiClosed_singleton G (1 : Variety.Point G))).closure_eq]
  have hjterminal : relativeLowerCentralSeries G S (j + 1) = ⊥ := by
    rw [hjone]
    exact hm
  have hcomm_le : ⁅C.toSubgroup,
      (ClosedSubgroup.top (G := G)).toSubgroup⁆ ≤
      (ClosedSubgroup.bot (G := G)).toSubgroup := by
    have hcomm := commutator_subgroupZariskiClosure_le_two G
      (relativeLowerCentralSeries G S j)
      (⊤ : Subgroup (Variety.Point G))
    rw [hclosure_top] at hcomm
    rw [show ⁅relativeLowerCentralSeries G S j,
        (⊤ : Subgroup (Variety.Point G))⁆ =
      relativeLowerCentralSeries G S (j + 1) by rfl,
      hjterminal, hclosure_bot] at hcomm
    exact hcomm
  have hCcentral : C.toSubgroup ≤
      Subgroup.centralizer
        ((⊤ : Subgroup (Variety.Point G)) : Set (Variety.Point G)) := by
    have hcomm_eq : ⁅C.toSubgroup,
        (ClosedSubgroup.top (G := G)).toSubgroup⁆ = ⊥ :=
      le_antisymm hcomm_le bot_le
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_eq
  let Z : ClosedSubgroup G := (ClosedSubgroup.top (G := G)).centralizer
  have hCZ : C ≤ Z := by
    intro x hx
    exact hCcentral hx
  have hdimle : Variety.dimension C.carrierVariety ≤
      Variety.dimension Z.carrierVariety :=
    connected_closedSubgroup_dimension_le_of_le C Z hCconn hCZ
  exact lt_of_lt_of_le hCdim hdimle

end Theory.AlgebraicGroup
