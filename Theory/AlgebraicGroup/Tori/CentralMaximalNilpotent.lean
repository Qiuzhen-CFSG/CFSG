module

public import Theory.AlgebraicGroup.Tori.Extension
public import Theory.AlgebraicGroup.Tori.CartanStructure
public import Theory.AlgebraicGroup.Tori.CentralMaximalNilpotent.TorusFree
public import Theory.AlgebraicGroup.Morphism.Connected
public import Theory.AlgebraicGroup.ClosedSubgroup.Quotient
public import Theory.AlgebraicGroup.Unipotent.Basic

/-!
# Nilpotence from a central maximal torus

A quotient by a maximal torus contains no nontrivial subtorus. Indeed, the
identity component of a torus preimage is a torus by the torus-extension
theorem, contains the kernel torus, and still surjects onto the target torus.
Maximality therefore makes the target torus trivial.

For a central maximal torus we construct a surjective algebraic morphism
with exactly that point kernel and connected target. The earlier source
assertion, proved in `TorusFree`, makes a connected group with no nontrivial
tori unipotent. Thus the target is nilpotent, and centrality of the kernel
gives nilpotence of the original point group. The last theorem applies this to the literal group
`T.centralizer.identityComponentAmbient` used by the regular-witness argument.

The conditional quotient and centralizer interfaces are retained, and the
terminal theorems discharge their torus-free unipotence premise. No ambient
solvability or nilpotence is assumed.

Source: Borel, *Linear Algebraic Groups*, second edition,
`refs/KGroup/Bor1/Chapter4.tex`, §§11.5(2), 11.5(3)(b⇒c), and 11.7.
-/

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup.CentralMaximalNilpotent
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]

/-- A surjective morphism whose kernel is a maximal torus has no nontrivial
subtorus in its target. Neither ambient connectedness nor centrality is needed
for this part of Borel §11.5(3)(b⇒c). -/
public theorem subtorus_eq_bot_of_surjective_of_maximalTorus_kernel
    (q : Morphism G Q) (hq : Function.Surjective q.onPoints)
    (hker : IsMaximalTorus q.kernelClosedSubgroup)
    (R : ClosedSubgroup Q) (hR : IsSubtorus R) : R.toSubgroup = ⊥ := by
  let P := q.closedSubgroupPreimage R
  let P₀ := AlgebraicGroup.identityComponentClosedSubgroup P.carrierVariety
  letI : AlgebraicGroup P₀.carrierVariety := P₀.carrierAlgebraicGroup
  let r := (q.preimageRestriction R).comp P₀.inclusion
  have hrker : IsSubtorus r.kernelClosedSubgroup :=
    q.preimageRestriction_identityComponent_kernel_isSubtorus R hker.1
  have hP₀ : IsTorus P₀.carrierVariety :=
    connected_isTorus_of_torus_kernel_to_torus r
      (identityComponentClosedSubgroup_carrier_isConnected P.carrierVariety) hrker hR
  have hPtorus : IsSubtorus P.identityComponentAmbient :=
    morphism_image_isTorus (P.inclusion.comp P₀.inclusion) hP₀
  have hkerP : q.kernelClosedSubgroup ≤ P := by
    intro x hx
    change q.onPoints x ∈ R.toSubgroup
    change q.onPoints x = 1 at hx
    rw [hx]
    exact R.toSubgroup.one_mem
  have heq : P.identityComponentAmbient = q.kernelClosedSubgroup :=
    hker.2 _ hPtorus
      (maximalTorus_le_identityComponentAmbient_of_le _ _ hker hkerP)
  have hr : Function.Surjective r.onPoints :=
    q.preimageRestriction_identityComponent_surjective hq R hR.isConnected
  apply le_antisymm _ bot_le
  intro y hy
  let yR := R.pointEquiv.symm ⟨y, hy⟩
  obtain ⟨z, hz⟩ := hr yR
  have hzmem : P.inclusion.onPoints (P₀.inclusion.onPoints z) ∈
      P.identityComponentAmbient.toSubgroup := ⟨z, rfl⟩
  rw [heq] at hzmem
  change q.onPoints (P.inclusion.onPoints (P₀.inclusion.onPoints z)) = 1 at hzmem
  have hzy := congrArg R.inclusion.onPoints hz
  change R.inclusion.onPoints
    ((q.preimageRestriction R).onPoints (P₀.inclusion.onPoints z)) = y at hzy
  rw [q.preimageRestriction_inclusion_apply] at hzy
  exact Subgroup.mem_bot.mpr (hzy.symm.trans hzmem)

/-- Realize the quotient by a central maximal torus as a connected affine
algebraic group with no nontrivial subtori. The projection is surjective on
points and has exactly the prescribed kernel. -/
public theorem exists_torusFree_quotient
    (hG : Variety.IsConnected G) (S : ClosedSubgroup G)
    (hS : IsMaximalTorus S)
    (hcentral : S.toSubgroup ≤ Subgroup.center (Variety.Point G)) :
    ∃ (Q : Variety k) (_ : AlgebraicGroup Q) (q : Morphism G Q),
      Function.Surjective q.onPoints ∧ q.kernel = S.toSubgroup ∧
      Variety.IsConnected Q ∧
      ∀ R : ClosedSubgroup Q, IsSubtorus R → R.toSubgroup = ⊥ := by
  have hnormal : S.toSubgroup.Normal := by
    constructor
    intro x hx g
    have hc := Subgroup.mem_center_iff.mp (hcentral hx) g
    rw [hc, mul_inv_cancel_right]
    exact hx
  obtain ⟨n, F, hFker⟩ := S.generalLinearMorphism_exactKernel_exists hnormal
  letI : AlgebraicGroup F.imageClosedSubgroup.carrierVariety :=
    F.imageClosedSubgroup.carrierAlgebraicGroup
  obtain ⟨q, hq, hqker, _⟩ := F.closedImageProjection_exists
  have hkernel : q.kernel = S.toSubgroup := hqker.trans hFker
  have hclosedker : q.kernelClosedSubgroup = S := by
    apply SetLike.coe_injective
    exact congrArg (fun L : Subgroup (Variety.Point G) => (L : Set (Variety.Point G)))
      hkernel
  have hQ : Variety.IsConnected F.imageClosedSubgroup.carrierVariety := by
    let : ConnectedSpace (Variety.Point G) := connectedSpace_iff_univ.mpr hG
    let : ConnectedSpace (Variety.Point F.imageClosedSubgroup.carrierVariety) :=
      hq.connectedSpace q.toVariety.continuous
    exact connectedSpace_iff_univ.mp inferInstance
  refine ⟨F.imageClosedSubgroup.carrierVariety,
    F.imageClosedSubgroup.carrierAlgebraicGroup, q, hq, hkernel, hQ, ?_⟩
  intro R hR
  apply subtorus_eq_bot_of_surjective_of_maximalTorus_kernel q hq _ R hR
  rwa [hclosedker]

/-- The central-torus quotient argument in Borel §11.5(3)(b⇒c), conditional
only on the earlier torus-free unipotence assertion of §11.5(2). -/
public theorem isNilpotent_of_torusFree_unipotence
    (hunip : ∀ (K : Variety k) [AlgebraicGroup K], Variety.IsConnected K →
      (∀ R : ClosedSubgroup K, IsSubtorus R → R.toSubgroup = ⊥) →
      IsUnipotentAlgebraicGroup K)
    (hG : Variety.IsConnected G) (S : ClosedSubgroup G)
    (hS : IsMaximalTorus S)
    (hcentral : S.toSubgroup ≤ Subgroup.center (Variety.Point G)) :
    Group.IsNilpotent (Variety.Point G) := by
  obtain ⟨Q, hQgroup, q, _hq, hker, hQ, hQtorus⟩ :=
    exists_torusFree_quotient hG S hS hcentral
  letI : AlgebraicGroup Q := hQgroup
  let : Group.IsNilpotent (Variety.Point Q) :=
    unipotentGroup_isNilpotent (hunip Q hQ hQtorus)
  apply Subgroup.isNilpotent_of_ker_le_center q.onPoints
  change q.kernel ≤ Subgroup.center (Variety.Point G)
  rwa [hker]

/-- Apply the central maximal torus supplied by `CartanStructure` to the
literal centralizer component. This supplies the regular-witness nilpotence
input once the earlier §11.5(2) assertion has been proved. -/
public theorem centralizerComponent_isNilpotent_of_torusFree_unipotence
    (hunip : ∀ (K : Variety k) [AlgebraicGroup K], Variety.IsConnected K →
      (∀ R : ClosedSubgroup K, IsSubtorus R → R.toSubgroup = ⊥) →
      IsUnipotentAlgebraicGroup K)
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    Group.IsNilpotent
      (Variety.Point T.centralizer.identityComponentAmbient.carrierVariety) := by
  let H := T.centralizer.identityComponentAmbient
  have hH : Variety.IsConnected H.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
    let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
      Subtype.connectedSpace T.centralizer.identityComponentAmbient_isConnected
    let : ConnectedSpace (Variety.Point H.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  obtain ⟨S, hS, hcentral, _himage⟩ :=
    CartanStructure.exists_central_maximalTorus_in_centralizerComponent hT
  exact isNilpotent_of_torusFree_unipotence hunip hH S hS hcentral

/-- Borel §11.5(3)(b⇒c): a connected affine algebraic group with a central
maximal torus is nilpotent. The quotient by that torus is torus-free, hence
unipotent by §11.5(2); its central kernel then lifts nilpotence. -/
public theorem isNilpotent_of_central_maximalTorus
    (hG : Variety.IsConnected G) (S : ClosedSubgroup G)
    (hS : IsMaximalTorus S)
    (hcentral : S.toSubgroup ≤ Subgroup.center (Variety.Point G)) :
    Group.IsNilpotent (Variety.Point G) :=
  isNilpotent_of_torusFree_unipotence
    (fun _ _ hK htorus => TorusFree.isUnipotent_of_torusFree hK htorus)
    hG S hS hcentral

/-- The nilpotence assertion of Borel §11.7 for the literal centralizer
component `C_G(T)^0`. Its connectedness and central maximal torus are supplied
by the carrier homeomorphism and `CartanStructure`, respectively. -/
public theorem centralizerComponent_isNilpotent
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    Group.IsNilpotent
      (Variety.Point T.centralizer.identityComponentAmbient.carrierVariety) :=
  centralizerComponent_isNilpotent_of_torusFree_unipotence
    (fun _ _ hK htorus => TorusFree.isUnipotent_of_torusFree hK htorus) hT

end Theory.AlgebraicGroup.CentralMaximalNilpotent
