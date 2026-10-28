module

public import Theory.AlgebraicGroup.Radical.Existence
public import Theory.AlgebraicGroup.Tori.Character.FiniteGeneration
public import Theory.AlgebraicGroup.Tori.Character.Image
public import Theory.AlgebraicGroup.Tori.Maximal

universe u

set_option linter.style.haveILetI false

/-! Centralization of normal subtori by connected algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Every point of a connected algebraic group centralizes every point of a
normal subtorus. -/
public theorem connected_centralizes_normal_subtorus
    {G : Variety k} [AlgebraicGroup G]
    (hG : Variety.IsConnected G)
    (N : ClosedSubgroup G) (hN : IsSubtorus N)
    (hNnormal : N.toSubgroup.Normal)
    (g : Variety.Point G) (x : Variety.Point N.carrierVariety) :
    g * N.inclusion.onPoints x * g⁻¹ = N.inclusion.onPoints x := by
  obtain ⟨n, ⟨e⟩⟩ := hN
  have hrestricted :
      (N.conjugationRestriction hNnormal g).onPoints x = x := by
    have hinv : Function.Injective e.inv.onPoints :=
      Function.LeftInverse.injective (fun y => e.inv_hom_id y)
    apply hinv
    apply (dPointEquiv n).injective
    funext i
    let χ : TorusCharacter N.carrierVariety :=
      (dCoordinateCharacter n i).comp e.inv
    have hχ :=
      torusCharacter_comp_conjugationRestriction_eq_self_of_connected
        hG N hNnormal χ g
    have hv := congrArg
      (fun ψ : TorusCharacter N.carrierVariety => ψ.onPoints x) hχ
    exact congrFun (congrArg (dPointEquiv 1) hv) 0
  rw [← N.conjugationRestriction_inclusion_apply hNnormal, hrestricted]

/-- A torus radical in the identity component of a maximal-torus centralizer
has ambient image equal to the original maximal torus. -/
public theorem exists_centralizerIdentityComponent_radical_ambientImage_eq_maximalTorus_of_isSubtorus
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (hT : IsMaximalTorus T) :
    let C := T.centralizer
    letI : AlgebraicGroup C.carrierVariety := C.carrierAlgebraicGroup
    let C0 := AlgebraicGroup.identityComponentClosedSubgroup C.carrierVariety
    letI : AlgebraicGroup C0.carrierVariety := C0.carrierAlgebraicGroup
    ∃ R : ClosedSubgroup C0.carrierVariety,
      IsRadicalSubgroup R ∧
        (IsSubtorus R →
          letI : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
          ((C.inclusion.comp C0.inclusion).comp R.inclusion).imageClosedSubgroup = T) := by
  let C := T.centralizer
  letI : AlgebraicGroup C.carrierVariety := C.carrierAlgebraicGroup
  let C0 := AlgebraicGroup.identityComponentClosedSubgroup C.carrierVariety
  letI : AlgebraicGroup C0.carrierVariety := C0.carrierAlgebraicGroup
  have hTC : T ≤ C := maximalTorus_le_centralizer hT
  let jC : AlgebraicGroup.Morphism T.carrierVariety C.carrierVariety :=
    T.inclusion.codRestrictClosedSubgroup C fun x => hTC (T.pointEquiv x).property
  have hTC0 (x : Variety.Point T.carrierVariety) :
      jC.onPoints x ∈ C0.toSubgroup := by
    obtain ⟨y, hy, heq⟩ :=
      maximalTorus_le_centralizer_identityComponent hT (T.pointEquiv x).property
    have hyj : y = jC.onPoints x := by
      apply C.inclusion_injective
      rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
      exact heq
    rwa [← hyj]
  let j : AlgebraicGroup.Morphism T.carrierVariety C0.carrierVariety :=
    jC.codRestrictClosedSubgroup C0 hTC0
  have hjambient (x : Variety.Point T.carrierVariety) :
      C.inclusion.onPoints (C0.inclusion.onPoints (j.onPoints x)) =
        T.inclusion.onPoints x := by
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply,
      AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
  let TI := j.imageClosedSubgroup
  letI : AlgebraicGroup TI.carrierVariety := TI.carrierAlgebraicGroup
  have hTIconnected : _root_.IsConnected
      (TI.toSubgroup : Set (Variety.Point C0.carrierVariety)) :=
    j.imageClosedSubgroup_isConnected hT.1.isConnected
  have hTcomm := hT.1.isMulCommutative
  rw [isMulCommutative_iff] at hTcomm
  have hTIsolvable : Group.IsSolvable (Variety.Point TI.carrierVariety) :=
    j.imageClosedSubgroup_isSolvable (Group.isSolvable_of_comm hTcomm)
  have hTInormal : TI.toSubgroup.Normal := by
    constructor
    intro n hn g
    change n ∈ j.image at hn
    obtain ⟨x, rfl⟩ := hn
    have hgC : C.inclusion.onPoints (C0.inclusion.onPoints g) ∈ C.toSubgroup :=
      (C.pointEquiv (C0.inclusion.onPoints g)).property
    have hcomm := Subgroup.mem_centralizer_iff.mp hgC
      (T.inclusion.onPoints x) (T.pointEquiv x).property
    have hconj : g * j.onPoints x * g⁻¹ = j.onPoints x := by
      apply C0.inclusion_injective
      apply C.inclusion_injective
      simp only [map_mul, map_inv, hjambient]
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj]
    change j.onPoints x ∈ j.image
    exact ⟨x, rfl⟩
  obtain ⟨R, hR⟩ := exists_radical C0.carrierVariety
  have hTIR : TI ≤ R := hR.2.2.2 TI hTInormal hTIconnected hTIsolvable
  refine ⟨R, hR, ?_⟩
  intro hRtorus
  letI : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
  let rAmb : AlgebraicGroup.Morphism R.carrierVariety K :=
    C.inclusion.comp (C0.inclusion.comp R.inclusion)
  let RI := rAmb.imageClosedSubgroup
  have hRItorus : IsSubtorus RI := morphism_image_isTorus rAmb hRtorus
  have hTRI : T ≤ RI := by
    intro x hx
    let xT : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨x, hx⟩
    have hxTI : j.onPoints xT ∈ TI.toSubgroup := ⟨xT, rfl⟩
    let xR : Variety.Point R.carrierVariety :=
      R.pointEquiv.symm ⟨j.onPoints xT, hTIR hxTI⟩
    change x ∈ rAmb.image
    refine ⟨xR, ?_⟩
    change C.inclusion.onPoints
      (C0.inclusion.onPoints (R.inclusion.onPoints xR)) = x
    change C.inclusion.onPoints
      (C0.inclusion.onPoints (R.pointEquiv xR).val) = x
    dsimp [xR]
    rw [R.pointEquiv.apply_symm_apply, hjambient]
    change (T.pointEquiv xT).val = x
    dsimp [xT]
    rw [T.pointEquiv.apply_symm_apply]
  change RI = T
  exact hT.2 RI hRItorus hTRI

end Theory.AlgebraicGroup
