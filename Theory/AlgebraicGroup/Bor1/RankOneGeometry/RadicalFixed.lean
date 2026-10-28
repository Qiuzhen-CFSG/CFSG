module

public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.RadicalAction
public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.FiniteKernel
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.FixedSubgroups.Connected

/-!
# Fixed points in a one-dimensional rank-one radical

The connected fixed-subgroup theorem for torus actions on connected unipotent
groups, together with the genuine nontrivial torus action, makes the fixed
subgroup proper. In dimension one strict dimension forces it to be trivial.
In particular every central kernel meets this radical trivially. This is the
kernel-removal step of Borel §13.14; the one-dimensional radical premise is
discharged by the projective-line realization in the final rank-one assembly.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Theory.AlgebraicGroup.Bor1.RankOneGeometry
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

theorem torus_fixed_unipotentRadical_eq_bot_of_dimension_one
    (hG : IsSemisimpleAlgebraicGroup G)
    (T B V : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety = 1)
    (hB : IsBorelSubgroup B) (hTB : T ≤ B)
    (hV : IsUnipotentRadicalOf B V)
    (hdimV : Variety.dimension V.carrierVariety = 1) :
    (V.pointwiseCentralizer T).toSubgroup = ⊥ := by
  obtain ⟨V',hV',hVc⟩ := exists_unipotentRadical_of_connected_solvable B hB.connected hB.solvable
  have he : V'=V := unipotent_radical_unique hV' hV
  subst V'
  have hTN : T ≤ V.normalizer := by
    apply Subgroup.le_normalizer_iff.mpr
    intro t ht v hv
    exact hV.2.2.1 t (hTB ht) v hv
  have hfixed :=
    SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.externalTorusFixed_isConnected_set
      V T hVc hV.2.1 hT.1 hTN
  have hne : V.pointwiseCentralizer T ≠ V := by
    intro he
    obtain ⟨t,ht,v,hv,hnot⟩ := exists_torus_unipotentRadical_noncommuting hG T B V hT hdimT hB hTB hV
    have hvfixed : v ∈ (V.pointwiseCentralizer T).toSubgroup := he.symm ▸ hv
    exact hnot ((Subgroup.mem_centralizer_iff.mp hvfixed.2) t ht)
  have hdim := connected_closedSubgroup_dimension_lt_of_le_of_ne
    (V.pointwiseCentralizer T) V (fun _ hx => hx.1) hne hfixed hVc
  rw [hdimV] at hdim
  have hz := Cardinal.lt_one_iff.mp hdim
  by_contra hbot
  have hp := connected_closedSubgroup_dimension_pos_of_ne_bot (V.pointwiseCentralizer T) hfixed hbot
  rw [hz] at hp
  exact lt_irrefl _ hp

theorem central_kernel_inf_unipotentRadical_eq_bot_of_dimension_one
    (hG : IsSemisimpleAlgebraicGroup G)
    (T B V : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety = 1)
    (hB : IsBorelSubgroup B) (hTB : T ≤ B)
    (hV : IsUnipotentRadicalOf B V)
    (hdimV : Variety.dimension V.carrierVariety = 1)
    (N : Subgroup (Variety.Point G)) (hN : N ≤ Subgroup.center (Variety.Point G)) :
    N ⊓ V.toSubgroup = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← torus_fixed_unipotentRadical_eq_bot_of_dimension_one hG T B V hT hdimT hB hTB hV hdimV]
  intro v hv
  exact ⟨hv.2,Subgroup.mem_centralizer_iff.mpr (fun t _ => Subgroup.mem_center_iff.mp (hN hv.1) t)⟩

end Theory.AlgebraicGroup.Bor1.RankOneGeometry
