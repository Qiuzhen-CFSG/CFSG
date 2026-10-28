module

public import Theory.AlgebraicGroup.Semisimple.Defs
public import Theory.AlgebraicGroup.Radical.Existence
public import Theory.AlgebraicGroup.ClosedSubgroup.Connected
public import Theory.AlgebraicGroup.Borel.Defs

/-!
# Solvable normal subgroups of semisimple algebraic groups

A normal subgroup contained in a Borel has solvable identity component. That
component lies in the radical and is trivial in a semisimple group, so the
subgroup is finite. Conjugation by a connected group has connected image;
a finite such image is constant, proving centrality.

This is the finite-central-kernel step in Borel §13.13, without a separability
assumption or any rank-one classification.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
namespace Theory.AlgebraicGroup
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

omit [IsAlgClosed k] in
theorem finite_normal_closedSubgroup_le_center
    (hG : Variety.IsConnected G) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) (hfinite : Finite (Variety.Point N.carrierVariety)) :
    N.toSubgroup ≤ Subgroup.center (Variety.Point G) := by
  letI := hfinite
  letI : Finite N.toSubgroup := Finite.of_equiv _ N.pointEquiv
  have hfin : (N : Set (Variety.Point G)).Finite := Set.finite_coe_iff.mp inferInstance
  intro n hn
  apply Subgroup.mem_center_iff.mpr
  intro g
  let f := AlgebraicGroup.conjugateMorphism G n
  have hmap : Set.MapsTo f.toFun Set.univ (N : Set (Variety.Point G)) := by
    intro a _
    rw [AlgebraicGroup.conjugateMorphism_apply]
    exact hN.conj_mem n hn a
  have hrange : (Set.range f.toFun).Finite := hfin.subset (by
    rintro _ ⟨a,rfl⟩
    exact hmap (Set.mem_univ a))
  have he := connected_finite_morphism_range_subsingleton f hG hrange
    (Set.mem_range_self g) (Set.mem_range_self 1)
  change f.toFun g=f.toFun 1 at he
  simp only [f,AlgebraicGroup.conjugateMorphism_apply,one_mul,inv_one,mul_one] at he
  exact mul_inv_eq_iff_eq_mul.mp he

theorem semisimple_normal_le_borel_finite_central
    (hG : IsSemisimpleAlgebraicGroup G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (N : ClosedSubgroup G) (hN : N.toSubgroup.Normal) (hNB : N ≤ B) :
    Finite (Variety.Point N.carrierVariety) ∧
      N.toSubgroup ≤ Subgroup.center (Variety.Point G) := by
  let I := N.identityComponentAmbient
  have hIB : I ≤ B := fun x hx => hNB (N.identityComponentAmbient_le hx)
  have hIs : Group.IsSolvable (Variety.Point I.carrierVariety) := by
    let eB : Variety.Point B.carrierVariety ≃* B.toSubgroup := Equiv.mulEquiv B.pointEquiv
    let eI : Variety.Point I.carrierVariety ≃* I.toSubgroup := Equiv.mulEquiv I.pointEquiv
    let f := eB.symm.toMonoidHom.comp ((Subgroup.inclusion hIB).comp eI.toMonoidHom)
    letI := hB.solvable
    exact Group.isSolvable_of_isSolvable_injective (f := f)
      (eB.symm.injective.comp ((Subgroup.inclusion_injective hIB).comp eI.injective))
  obtain ⟨R,hR⟩ := exists_radical G
  have hIR : I ≤ R := hR.maximal I (N.identityComponentAmbient_normal_of_normal hN)
    N.identityComponentAmbient_isConnected hIs
  have hIbot : I.toSubgroup ≤ ⊥ := by
    rw [←hG.2 R hR]
    exact hIR
  letI : Subsingleton I.toSubgroup := ⟨fun x y => Subtype.ext
    ((Subgroup.mem_bot.mp (hIbot x.2)).trans (Subgroup.mem_bot.mp (hIbot y.2)).symm)⟩
  letI : Subsingleton (Variety.Point I.carrierVariety) := I.pointEquiv.subsingleton
  have hIdim := (dimension_zero_iff_finite_points I.carrierVariety).mpr inferInstance
  have hNdim : Variety.dimension N.carrierVariety=0 :=
    N.dimension_identityComponentAmbient.symm.trans hIdim
  have hfin := (dimension_zero_iff_finite_points N.carrierVariety).mp hNdim
  exact ⟨hfin,finite_normal_closedSubgroup_le_center hG.1 N hN hfin⟩

end Theory.AlgebraicGroup
