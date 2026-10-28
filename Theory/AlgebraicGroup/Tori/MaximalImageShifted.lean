module

public import Theory.AlgebraicGroup.Tori.Maximal
public import Theory.AlgebraicGroup.Borel.Conjugation
public import Theory.AlgebraicGroup.Borel.IsogenyImage
public import Theory.AlgebraicGroup.Borel.Existence
public import Theory.AlgebraicGroup.Tori.Character.Image
public import Theory.AlgebraicGroup.Tori.Semisimple
public import Theory.AlgebraicGroup.Unipotent.Radical
public import Theory.AlgebraicGroup.Morphism.CodRestrict

/-!
This module contains a shifted implementation of clause (d).  The proof
constructs the lifting/maximality bridge through a Borel subgroup and the
unipotent-radical decomposition; it does not call the source clause (d)
recursively.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma carrier_isConnected_of_set_isConnected
    {G : Variety k} [AlgebraicGroup G] (B : ClosedSubgroup G)
    (hB : _root_.IsConnected (B : Set (Variety.Point G))) :
    Variety.IsConnected B.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph B.isZariskiClosed
  let _ : ConnectedSpace {x : Variety.Point G // x ∈ (B : Set (Variety.Point G))} :=
    Subtype.connectedSpace hB
  let _ : ConnectedSpace (Variety.Point B.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

private theorem torus_image_maximal_in_borel_carrier
    {G : Variety k} [AlgebraicGroup G]
    (B T : ClosedSubgroup G)
    (hT : IsMaximalTorus T)
    (hTB : T ≤ B) :
    let tB : AlgebraicGroup.Morphism T.carrierVariety B.carrierVariety :=
      T.inclusion.codRestrictClosedSubgroup B (fun x => hTB (T.pointEquiv x).property)
    let TB := tB.imageClosedSubgroup
    IsMaximalTorus TB := by
  let tB : AlgebraicGroup.Morphism T.carrierVariety B.carrierVariety :=
    T.inclusion.codRestrictClosedSubgroup B (fun x => hTB (T.pointEquiv x).property)
  let TB := tB.imageClosedSubgroup
  have hTBtorus : IsSubtorus TB := morphism_image_isTorus tB hT.1
  refine ⟨hTBtorus, ?_⟩
  intro U hU hTBU
  let _ : AlgebraicGroup U.carrierVariety := U.carrierAlgebraicGroup
  let uG : AlgebraicGroup.Morphism U.carrierVariety G :=
    B.inclusion.comp U.inclusion
  let UG := uG.imageClosedSubgroup
  have hUGtorus : IsSubtorus UG := morphism_image_isTorus uG hU
  have hTUG : T ≤ UG := by
    intro x hx
    let tx : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨x, hx⟩
    have htxTB : tB.onPoints tx ∈ TB.toSubgroup := ⟨tx, rfl⟩
    have htxU : tB.onPoints tx ∈ U.toSubgroup := hTBU htxTB
    let ux : Variety.Point U.carrierVariety :=
      U.pointEquiv.symm ⟨tB.onPoints tx, htxU⟩
    change x ∈ uG.image
    refine ⟨ux, ?_⟩
    change B.inclusion.onPoints (U.inclusion.onPoints ux) = x
    change B.inclusion.onPoints (tB.onPoints tx) = x
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
    change (T.pointEquiv tx).val = x
    dsimp [tx]
    rw [T.pointEquiv.apply_symm_apply]
  have hUGeq : UG = T := hT.2 UG hUGtorus hTUG
  apply SetLike.coe_injective
  ext z
  constructor
  · intro hz
    let uz : Variety.Point U.carrierVariety := U.pointEquiv.symm ⟨z, hz⟩
    have hzUG : uG.onPoints uz ∈ UG.toSubgroup := ⟨uz, rfl⟩
    rw [hUGeq] at hzUG
    let tz : Variety.Point T.carrierVariety :=
      T.pointEquiv.symm ⟨uG.onPoints uz, hzUG⟩
    have htzTB : tB.onPoints tz ∈ TB.toSubgroup := ⟨tz, rfl⟩
    have htzU : tB.onPoints tz ∈ U.toSubgroup := hTBU htzTB
    let uz' : Variety.Point U.carrierVariety :=
      U.pointEquiv.symm ⟨tB.onPoints tz, htzU⟩
    have huz : uz = uz' := by
      apply U.pointEquiv.injective
      apply Subtype.ext
      apply B.inclusion_injective
      change B.inclusion.onPoints (U.inclusion.onPoints uz) =
        B.inclusion.onPoints (U.inclusion.onPoints uz')
      change B.inclusion.onPoints z =
        B.inclusion.onPoints (tB.onPoints tz)
      exact (by
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        change T.inclusion.onPoints tz = B.inclusion.onPoints z
        have htz : T.inclusion.onPoints tz = uG.onPoints uz := by
          change (T.pointEquiv tz).val = uG.onPoints uz
          dsimp [tz]
          rw [T.pointEquiv.apply_symm_apply]
        have huz : uG.onPoints uz = B.inclusion.onPoints z := by
          change B.inclusion.onPoints (U.inclusion.onPoints uz) =
            B.inclusion.onPoints z
          change B.inclusion.onPoints (U.pointEquiv uz).val =
            B.inclusion.onPoints z
          dsimp [uz]
          rw [U.pointEquiv.apply_symm_apply]
        exact htz.trans huz.symm)
    exact htzTB
  · intro hz
    exact hTBU hz

public theorem theorem_1_4_3_d_shifted
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism G H)
    (hφ : Function.Surjective φ.onPoints)
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T) :
    IsMaximalTorus ((φ.comp T.inclusion).imageClosedSubgroup) := by
  let _ : ConnectedSpace (Variety.Point T.carrierVariety) := by
    exact connectedSpace_iff_univ.mpr hT.1.isConnected
  have hTconn : _root_.IsConnected (T : Set (Variety.Point G)) := by
    change _root_.IsConnected (T.toSubgroup : Set (Variety.Point G))
    rw [← T.range_inclusion]
    exact isConnected_range T.inclusion.toVariety.continuous
  have hTsolv : Group.IsSolvable (Variety.Point T.carrierVariety) := by
    have hcomm := hT.1.isMulCommutative
    rw [isMulCommutative_iff] at hcomm
    exact Group.isSolvable_of_comm hcomm
  obtain ⟨B, hB, hTB⟩ := exists_borelSubgroup_containing_connected_solvable
    T hTconn hTsolv
  let φB0 : AlgebraicGroup.Morphism B.carrierVariety H :=
    φ.comp B.inclusion
  let IB := φB0.imageClosedSubgroup
  have hIB : IsBorelSubgroup IB := theorem_1_6_2_d φ hφ B hB
  let tB : AlgebraicGroup.Morphism T.carrierVariety B.carrierVariety :=
    T.inclusion.codRestrictClosedSubgroup B (fun x => hTB (T.pointEquiv x).property)
  let TB := tB.imageClosedSubgroup
  have hTBmax : IsMaximalTorus TB := by
    exact torus_image_maximal_in_borel_carrier B T hT hTB
  let φB : AlgebraicGroup.Morphism B.carrierVariety IB.carrierVariety :=
    φB0.codRestrictClosedSubgroup IB (fun x => ⟨x, rfl⟩)
  have hφBsurj : Function.Surjective φB.onPoints := by
    exact φB0.codRestrictImageClosedSubgroup_surjective (fun x => ⟨x, rfl⟩)
  let I := (φ.comp T.inclusion).imageClosedSubgroup
  have hIle : I ≤ IB := by
    intro x hx
    change x ∈ (φ.comp T.inclusion).image at hx
    rcases hx with ⟨tx, rfl⟩
    change φB0.onPoints (tB.onPoints tx) ∈ IB.toSubgroup
    exact ⟨tB.onPoints tx, rfl⟩
  have hIlocal : IsTorusMaximalIn I IB := by
    refine ⟨morphism_image_isTorus (φ.comp T.inclusion) hT.1, hIle, ?_⟩
    intro U hU hUI hIU
    let _ : AlgebraicGroup U.carrierVariety := U.carrierAlgebraicGroup
    have hBconn : Variety.IsConnected B.carrierVariety :=
      carrier_isConnected_of_set_isConnected B hB.connected
    obtain ⟨N, hN, hTN⟩ := theorem_1_5_1_d hBconn hB.solvable
    apply SetLike.coe_injective
    apply Set.Subset.antisymm
    · intro y hy
      let uy : Variety.Point U.carrierVariety := U.pointEquiv.symm ⟨y, hy⟩
      let uyIB : Variety.Point IB.carrierVariety :=
        IB.pointEquiv.symm ⟨y, hUI hy⟩
      obtain ⟨bx, hbx⟩ := hφBsurj uyIB
      obtain ⟨tx, nx, htx, hnx, hmul⟩ := (hTN TB hTBmax).1 bx
      have htxI : IB.inclusion.onPoints (φB.onPoints tx) ∈ I.toSubgroup := by
        obtain ⟨tt, htt⟩ := htx
        rw [← htt]
        change φB0.onPoints (tB.onPoints tt) ∈ I.toSubgroup
        exact ⟨tt, by rfl⟩
      have htxU : IB.inclusion.onPoints (φB.onPoints tx) ∈ U.toSubgroup := hIU htxI
      have hydecomp : y =
          IB.inclusion.onPoints (φB.onPoints tx) *
            IB.inclusion.onPoints (φB.onPoints nx) := by
        have heq := congrArg IB.inclusion.onPoints hbx
        change IB.inclusion.onPoints (φB.onPoints bx) = y at heq
        rw [show IB.inclusion.onPoints (φB.onPoints bx) =
            φB0.onPoints bx by rfl] at heq
        rw [hmul, map_mul] at heq
        exact heq.symm
      have hnxH : IB.inclusion.onPoints (φB.onPoints nx) ∈ U.toSubgroup := by
        have hh := U.toSubgroup.mul_mem (U.toSubgroup.inv_mem htxU) hy
        rw [hydecomp] at hh
        simpa [mul_assoc] using hh
      have hnxone : IB.inclusion.onPoints (φB.onPoints nx) = 1 := by
        let unx : Variety.Point U.carrierVariety :=
          U.pointEquiv.symm ⟨IB.inclusion.onPoints (φB.onPoints nx), hnxH⟩
        have hunx : unx = 1 := by
          apply semisimple_unipotent_eq_one
          · exact hU.all_semisimple unx
          · have hnxUnipIB : IsUnipotentElement IB.carrierVariety
                (φB.onPoints nx) :=
              morphism_preserves_unipotentElement φB nx ((hN nx).mp hnx)
            have hnxUnipH : IsUnipotentElement H
                (IB.inclusion.onPoints (φB.onPoints nx)) :=
              morphism_preserves_unipotentElement IB.inclusion
                (φB.onPoints nx) hnxUnipIB
            exact (closedSubgroup_unipotentElement_iff U hnxH).mp hnxUnipH
        change U.inclusion.onPoints unx = 1
        rw [hunx]
        rfl
      have hyI : y ∈ I.toSubgroup := by
        rw [hydecomp, hnxone, mul_one]
        exact htxI
      exact hyI
    · intro y hy
      exact hIU hy
  have hglobal := theorem_1_6_4 hIB hIB hIlocal hIlocal
  exact hglobal.1

end Theory.AlgebraicGroup
