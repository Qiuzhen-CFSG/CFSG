module

public import Theory.AlgebraicGroup.RootSubgroups.Defs
public import Theory.AlgebraicGroup.Tori.Semisimple

universe u

/-! Trivial intersections of subtori and unipotent closed subgroups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A subtorus and a unipotent closed subgroup have trivial intersection. -/
public theorem subtorus_inf_unipotent_eq_bot
    {K : Variety k} [AlgebraicGroup K]
    (T U : ClosedSubgroup K)
    (hT : IsSubtorus T)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) :
    T.toSubgroup ⊓ U.toSubgroup = ⊥ := by
  apply le_antisymm
  · intro x hx
    apply Subgroup.mem_bot.mpr
    let xT : Variety.Point T.carrierVariety :=
      T.pointEquiv.symm ⟨x, hx.1⟩
    have hxsemisimpleT : IsSemisimpleElement T.carrierVariety xT :=
      hT.all_semisimple xT
    have hxsemisimple : IsSemisimpleElement K x := by
      have h :=
        (closedSubgroup_semisimpleElement_iff T hx.1).mpr hxsemisimpleT
      simpa [xT] using h
    let xU : Variety.Point U.carrierVariety :=
      U.pointEquiv.symm ⟨x, hx.2⟩
    have hxunipotentU : IsUnipotentElement U.carrierVariety xU := hU xU
    have hxunipotent : IsUnipotentElement K x := by
      have h :=
        (closedSubgroup_unipotentElement_iff U hx.2).mpr hxunipotentU
      simpa [xU] using h
    exact semisimple_unipotent_eq_one x hxsemisimple hxunipotent
  · exact bot_le

/-- A torus root subgroup intersects its ambient torus trivially. -/
public lemma IsTorusRootSubgroup.inf_torus_eq_bot
    {K : Variety k} [AlgebraicGroup K]
    {T X : ClosedSubgroup K}
    (hX : IsTorusRootSubgroup T X)
    (hT : IsSubtorus T) :
    X.toSubgroup ⊓ T.toSubgroup = ⊥ := by
  rw [inf_comm]
  exact subtorus_inf_unipotent_eq_bot T X hT
    hX.2.isUnipotentAlgebraicGroup

end Theory.AlgebraicGroup
