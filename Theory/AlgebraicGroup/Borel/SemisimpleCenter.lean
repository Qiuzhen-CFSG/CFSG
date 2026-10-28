module

public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.Radical.Existence
public import Theory.AlgebraicGroup.Semisimple.Defs

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem connectedSemisimple_center_finite
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsSemisimpleAlgebraicGroup K) :
    Finite (Subgroup.center (Variety.Point K)) := by
  let Z : ClosedSubgroup K := (ClosedSubgroup.top (G := K)).centralizer
  let Z0 := AlgebraicGroup.identityComponentClosedSubgroup Z.carrierVariety
  letI : AlgebraicGroup Z0.carrierVariety := Z0.carrierAlgebraicGroup
  let q : AlgebraicGroup.Morphism Z0.carrierVariety K :=
    Z.inclusion.comp Z0.inclusion
  let Q := q.imageClosedSubgroup
  have hZmemCenter (z : Variety.Point Z.carrierVariety) :
      Z.inclusion.onPoints z ∈ Subgroup.center (Variety.Point K) := by
    have hz := (Z.pointEquiv z).property
    change Z.inclusion.onPoints z ∈ Z.toSubgroup at hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hcomm := (Subgroup.mem_centralizer_iff.mp hz) g
      (by change g ∈ (⊤ : Subgroup (Variety.Point K)); simp)
    exact hcomm
  have hZ0conn : Variety.IsConnected Z0.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph Z0.isZariskiClosed
    have hcarrier : (Z0 : Set (Variety.Point Z.carrierVariety)) =
        AlgebraicGroup.identityComponent Z.carrierVariety := by rfl
    have hconn : _root_.IsConnected
        (Z0 : Set (Variety.Point Z.carrierVariety)) := by
      rw [hcarrier]
      exact AlgebraicGroup.identityComponent_isConnected Z.carrierVariety
    let : ConnectedSpace {x : Variety.Point Z.carrierVariety //
        x ∈ (Z0 : Set (Variety.Point Z.carrierVariety))} :=
      Subtype.connectedSpace hconn
    let : ConnectedSpace (Variety.Point Z0.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  have hZ0solv : Group.IsSolvable (Variety.Point Z0.carrierVariety) := by
    apply Group.isSolvable_of_comm
    intro a b
    apply Z0.inclusion_injective
    apply Z.inclusion_injective
    have ha := hZmemCenter (Z0.inclusion.onPoints a)
    change q.onPoints (a * b) = q.onPoints (b * a)
    rw [map_mul, map_mul]
    have hqapply (z : Variety.Point Z0.carrierVariety) :
        q.onPoints z = Z.inclusion.onPoints (Z0.inclusion.onPoints z) := rfl
    simpa only [hqapply] using
      (Subgroup.mem_center_iff.mp ha (q.onPoints b)).symm
  have hQconnected := q.imageClosedSubgroup_isConnected hZ0conn
  have hQsolvable := q.imageClosedSubgroup_isSolvable hZ0solv
  have hQcenter : Q.toSubgroup ≤ Subgroup.center (Variety.Point K) := by
    intro y hy
    change y ∈ q.image at hy
    obtain ⟨z, rfl⟩ := hy
    exact hZmemCenter (Z0.inclusion.onPoints z)
  have hQnormal : Q.toSubgroup.Normal := by
    constructor
    intro n hn g
    have hncenter := Subgroup.mem_center_iff.mp (hQcenter hn) g
    have heq : g * n * g⁻¹ = n := by
      rw [hncenter]
      simp
    rwa [heq]
  obtain ⟨R, hR⟩ := exists_radical K
  have hQR : Q ≤ R := hR.maximal Q hQnormal hQconnected hQsolvable
  have hRbot : R.toSubgroup = ⊥ := hK.2 R hR
  have hQbot : Q.toSubgroup = ⊥ := by
    apply le_antisymm
    · intro x hx
      apply Subgroup.mem_bot.mpr
      apply Subgroup.mem_bot.mp
      rw [← hRbot]
      exact hQR hx
    · exact bot_le
  have hqone (z : Variety.Point Z0.carrierVariety) : q.onPoints z = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hQbot]
    change q.onPoints z ∈ q.image
    exact ⟨z, rfl⟩
  have hZ0subsingleton : Subsingleton (Variety.Point Z0.carrierVariety) := by
    constructor
    intro a b
    apply Z0.inclusion_injective
    apply Z.inclusion_injective
    change q.onPoints a = q.onPoints b
    rw [hqone, hqone]
  let : Subsingleton (Variety.Point Z0.carrierVariety) := hZ0subsingleton
  let H := AlgebraicGroup.identityComponentSubgroup Z.carrierVariety
  have hHbot : H = ⊥ := by
    apply SetLike.ext
    intro z
    constructor
    · intro hz
      let z0 : Variety.Point Z0.carrierVariety := Z0.pointEquiv.symm ⟨z, hz⟩
      have hz0 : z0 = 1 := Subsingleton.elim _ _
      apply Subgroup.mem_bot.mpr
      have hzsub : (⟨z, hz⟩ : Z0.toSubgroup) = 1 := by
        calc
          (⟨z, hz⟩ : Z0.toSubgroup) = Z0.pointEquiv z0 := by simp [z0]
          _ = Z0.pointEquiv 1 := congrArg Z0.pointEquiv hz0
          _ = 1 := by rfl
      exact congrArg Subtype.val hzsub
    · intro hz
      exact hz ▸ H.one_mem
  let : Finite (Variety.Point Z.carrierVariety ⧸ H) :=
    finite_quotient_identityComponentSubgroup Z.carrierVariety
  let : H.Normal := by
    simpa [H, AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
      (AlgebraicGroup.identityComponentClosedSubgroup_isNormal Z.carrierVariety)
  have hmkInj : Function.Injective (QuotientGroup.mk' H) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    exact (QuotientGroup.ker_mk' H).trans hHbot
  let : Finite (Variety.Point Z.carrierVariety) :=
    Finite.of_injective (QuotientGroup.mk' H) hmkInj
  let : Finite Z.toSubgroup := (Equiv.finite_iff Z.pointEquiv).mp inferInstance
  have hZcenter : Z.toSubgroup = Subgroup.center (Variety.Point K) := by
    change Subgroup.centralizer
      ((ClosedSubgroup.top (G := K)).toSubgroup : Set (Variety.Point K)) = _
    rw [show (ClosedSubgroup.top (G := K)).toSubgroup = ⊤ by rfl,
      Subgroup.coe_top, Subgroup.centralizer_univ]
  rw [← hZcenter]
  infer_instance

end

end Theory.AlgebraicGroup
