module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Source
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Transfer

/-!
# Conditional assembly of 15.3.59–61

The earlier-source interface retains the actual subgroups, the H-action on
U/Z, the natural and dual coordinates, the orthogonal V-action and the common
action on V and P/V. It contains no conclusion of 15.3.59–61. Its construction
from the standing subsection hypotheses belongs to the owner of 15.3.50.

The core calculation supplies U = O₂(H), the actual Sylow embedding in YU,
the relative index two and M = YT. Restricting H → H/O₂(H) to K constructs
K/U ≃ SL₃(2). The cubic calculation constructs the generators and a new
involution t, separates the cubic classes by centralizer two-parts 8 and 16,
and proves both nonfusion claims. The same quotient coordinates, now marked
by this t, feed the residual orbit calculation, including the corrected E32
local planes, the E64 blocks and their moving normalizers.

`source_fusion_of_earlier_data` supplies all four clauses of 15.3.59, the full
cubic witnesses and the exact marked transfer inputs. `false_of_earlier_data`
applies the already proved Thompson-transfer theorem and derives the needed
order four of ZS from the natural action. Neither theorem asserts 15.3.50
without the earlier source data.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.59–61,
printed pp.1149–1151; earlier inputs from 15.3.2, 15.3.46 and 15.3.48–58.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Assembly
open Core Core.ResidualGeneration Core.Automizers.Models
open ResidualOrbits
variable {G : Type*} [Group G] [Finite G]

/-- The first isomorphism theorem for the literal residual actor projection.
Its kernel becomes U ∩ K once the proved core equality is supplied; the
image is the actual inner automorphism group, not an equal-order model. -/
noncomputable def residualQuotientEquiv (Z ZS : Subgroup G)
    (hcore : closureU Z ZS = coreQ Z)
    (e : ActorQuotient Z ≃* MulAut Matrix.PSL3Two.SL) :
    (residualK Z ⧸ (closureU Z ZS).subgroupOf (residualK Z)) ≃* Matrix.PSL3Two.SL :=
  (QuotientGroup.quotientMulEquivOfEq (by rw [residualActor_ker, hcore])).trans
    ((QuotientGroup.quotientKerEquivRange (residualActor Z)).trans (residualImageEquiv Z e))

/-- Exactly the marked involution and two-class cover consumed by transfer. -/
def TransferWitnesses (T : Sylow 2 G) (Z ZS V₁ : Subgroup G) : Prop :=
  ((residualSylow T Z).subgroupOf (T : Subgroup G)).index = 2 ∧
    ∃ (z v : G) (t : T),
      orderOf z = 2 ∧ orderOf v = 2 ∧ zpowers z = Z ∧ zpowers v = ZS ⊓ V₁ ∧
      orderOf t = 2 ∧ (t : G) ∉ residualSylow T Z ∧
      ¬ IsConj (t : G) z ∧ ¬ IsConj (t : G) v ∧
      ∀ x ∈ residualK Z, orderOf x = 2 → IsConj x z ∨ IsConj x v


variable {T : Sylow 2 G} {M : Subgroup G}
  {a : NaturalOrthogonalAction M (localModule T M)} {i : OrthogonalPlaneIndex}
  {g : G} {Y₁ : Subgroup G} {y t₀ : G}
variable [(((centralInvolutions T)).subgroupOf (closureU (centralInvolutions T) (fixedPlane (localModule
  T M) (planeStabilizer T (a.plane i))))).Normal] [(((localModule T M)).subgroupOf (pairP
  (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane i))) g)).Normal]

/-- Earlier local conclusions, with every subgroup fixed by the source
constructions. `core` and `partner` record 15.3.48–58; `layers` and
`quotientPair` retain the two compatible actions in 15.3.53–54. The scalar
U-action inputs are 15.3.51(2a). Plus type, total singularity and the swap
are 15.3.58; the power-map form and fixed line are 15.3.56(1,7).

The last markings express earlier orthogonal geometry for whichever
nonidentity generators are subsequently constructed. `separated` is exactly
the earlier 15.3.46 separation of these generators. No property of the new
separating involution, cubic centralizer or residual involution cover occurs
in this record. The parent 15.3.50 assembly owns all these earlier inputs. -/
structure EarlierData (T : Sylow 2 G) (M : Subgroup G)
    (a : NaturalOrthogonalAction M (localModule T M)) (i : OrthogonalPlaneIndex)
    (g : G) (Y₁ : Subgroup G) (y t₀ : G)
    [((centralInvolutions T).subgroupOf (closureU (centralInvolutions T)
      (fixedPlane (localModule T M) (planeStabilizer T (a.plane i))))).Normal]
    [((localModule T M).subgroupOf (pairP (centralInvolutions T)
      (fixedPlane (localModule T M) (planeStabilizer T (a.plane i))) g)).Normal] where
  T_le_M : (T : Subgroup G) ≤ M
  core : LocalCoreData (T : Subgroup G) (centralInvolutions T) (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i))) (localModule T M) (residualY M (centralizerH (centralInvolutions
    T)))
  partner : Partner.EarlierGeometry (T : Subgroup G) (centralInvolutions T) (fixedPlane (localModule T
    M) (planeStabilizer T (a.plane i))) (localModule T M) Y₁ y t₀
  Y₁_le : Y₁ ≤ (residualY M (centralizerH (centralInvolutions T)))
  V_not_le_core : ¬ (localModule T M) ≤ coreQ (centralInvolutions T)
  displacement_le : ⁅(closureU (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T
    (a.plane i)))), (localModule T M)⁆ ≤ (localModule T M)
  displacement_card : Nat.card (vectorDisplacement (centralInvolutions T) (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i))) (localModule T M)) = 4
  U_card : Nat.card (closureU (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T
    (a.plane i)))) = 2 ^ 7
  extraspecial : IsExtraspecial 2 (closureU (centralInvolutions T) (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i))))
  pair_eq : (pairI (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane i)))
    g) = (residualY M (centralizerH (centralInvolutions T))) ⊔ (closureU (centralInvolutions T)
    (fixedPlane (localModule T M) (planeStabilizer T (a.plane i))))
  pair_le_M : (pairI (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane
    i))) g) ≤ M
  normalizes_Y : M ≤ normalizer ((residualY M (centralizerH (centralInvolutions T))) : Set G)
  center_P : (localModule T M) = (center (pairP (centralInvolutions T) (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i))) g)).map ((pairP (centralInvolutions T) (fixedPlane (localModule T
    M) (planeStabilizer T (a.plane i))) g)).subtype
  layers : LayerActions (pairI (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T
    (a.plane i))) g) (residualY M (centralizerH (centralInvolutions T))) (pairP (centralInvolutions T)
    (fixedPlane (localModule T M) (planeStabilizer T (a.plane i))) g) (localModule T M)
    (Cubic.MLocal.Structure.pairI_normalizes_pairP (centralInvolutions T) (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i))) g) (pair_le_M.trans a.normalizes)
  quotientPair : Cubic.MLocal.Structure.NaturalQuotientPair a (pairI (centralInvolutions T) (fixedPlane
    (localModule T M) (planeStabilizer T (a.plane i))) g) (pairP (centralInvolutions T) (fixedPlane
    (localModule T M) (planeStabilizer T (a.plane i))) g) pair_le_M
    (Cubic.MLocal.Structure.pairI_normalizes_pairP (centralInvolutions T) (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i))) g)
  centralizer_Y : (residualY M (centralizerH (centralInvolutions T))) ⊓ centralizer ((localModule T M) :
    Set G) = Stellmacher.twoCoreAmbient (residualY M (centralizerH (centralInvolutions T)))
  characteristic_two : centralizer (pCore 2 M : Set M) ≤ pCore 2 M
  chosen_mem : g ∈ (residualY M (centralizerH (centralInvolutions T)))
  chosen_moving : ¬ rightConjugate (centralInvolutions T) g ≤ (localModule T M) ⊓ (closureU
    (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane i))))
  U_image_elementary : IsElementaryAbelian 2 (a.image (closureU (centralInvolutions T) (fixedPlane
    (localModule T M) (planeStabilizer T (a.plane i)))))
  U_image_card : Nat.card (a.image (closureU (centralInvolutions T) (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i))))) = 4
  U_image_other : a.image (closureU (centralInvolutions T) (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i)))) ≠ a.image (planeStabilizer T (a.plane i))
  U_action_card : Nat.card ((((closureU (centralInvolutions T) (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i))))).subgroupOf (T : Subgroup G)).map
    (conjugationOnV (T : Subgroup G) (localModule T M) core.normalizes_module)) = 4
  fixed_action_card : Nat.card (Extraspecial.FixedLift.actionOnV
    ((show (closureU (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane
      i)))) ≤ (pairI (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane
      i))) g) from le_sup_left).trans (pair_le_M.trans a.normalizes))).range = 4
  centralizer_control : centralizer (fixedPlane (a.plane i) (planeStabilizer T (a.plane i)) : Set G) ≤ M
  Z_card : Nat.card (centralInvolutions T) = 2
  plusType : (closureU (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane
    i)))) ≃* Cubic.HLocal.DihedralCube
  plusElementary : ∃ A : Subgroup (closureU (centralInvolutions T) (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i)))), IsElementaryAbelian 2 A ∧ Nat.card A = 16
  natural_singular : ∀ (x : G), x ∈ Extraspecial.naturalPreimage partner.recognized → x ^ 2 = 1
  square : ∀ z : G, orderOf z = 2 → zpowers z = (centralInvolutions T) →
    Extraspecial.SquareForm partner.recognized z
  swap : ∀ (t : (centralizerH (centralInvolutions T))), (t : G) ∈ (T : Subgroup G) →
    (t : G) ∉ (closureU (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane
      i)))) ⊔ ((T : Subgroup G) ⊓ centralizer ((localModule T M) : Set G)) →
    (∀ w : BinaryLinearThree.Vector,
      (partner.recognized.coordinates (quotientAction (centralInvolutions T) (fixedPlane (localModule T
        M) (planeStabilizer T (a.plane i))) t
        (partner.recognized.coordinates.symm (Multiplicative.ofAdd (w, 0))))).toAdd.1 = 0) ∧
    (∀ f : Module.Dual (ZMod 2) BinaryLinearThree.Vector,
      (partner.recognized.coordinates (quotientAction (centralInvolutions T) (fixedPlane (localModule T
        M) (planeStabilizer T (a.plane i))) t
        (partner.recognized.coordinates.symm (Multiplicative.ofAdd (0, f))))).toAdd.2 = 0)
  fixed_line : ∀ (t : (centralizerH (centralInvolutions T))), (t : G) ∈ (T : Subgroup G) → ∀ x :
    (closureU (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane i)))), (x
    : G) ∈ (fixedPlane (localModule T M) (planeStabilizer T (a.plane i))) →
    quotientAction (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane i)))
      t (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x
  marked_geometry : ∀ z v : G, orderOf z = 2 → orderOf v = 2 →
    zpowers z = (centralInvolutions T) → zpowers v = (fixedPlane (localModule T M) (planeStabilizer T
      (a.plane i))) ⊓ (a.plane i) →
    Extraspecial.LocalGeometry partner.recognized M (a.plane i) z v
  intersection_card : Nat.card ((closureU (centralInvolutions T) (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i)))) ⊓ (localModule T M) : Subgroup G) = 8
  singular : ∀ z : (localModule T M), orderOf (z : G) = 2 → zpowers (z : G) = (centralInvolutions T) →
    (layers.lowerCoordinates z).toAdd.det = 0
  hyperplane : ∀ z : (localModule T M), orderOf (z : G) = 2 → zpowers (z : G) = (centralInvolutions T) →
    (closureU (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane i)))) ⊓
      (localModule T M) = CubicBlocks.Realization.sourceHyperplane layers z
  nonsingular : ∀ v : (localModule T M), orderOf (v : G) = 2 → zpowers (v : G) = (fixedPlane
    (localModule T M) (planeStabilizer T (a.plane i))) ⊓ (a.plane i) →
    (layers.lowerCoordinates v).toAdd.det ≠ 0
  separated : ∀ z v : G, orderOf z = 2 → orderOf v = 2 →
    zpowers z = (centralInvolutions T) → zpowers v = (fixedPlane (localModule T M) (planeStabilizer T
      (a.plane i))) ⊓ (a.plane i) → ¬ IsConj z v

variable (d : EarlierData T M a i g Y₁ y t₀)

/-- Supply the cubic calculation with the proved core equality. The actor
identification is transported from SL₃(2) to its projective model by the
actual equivalence, and the square identity is derived from the earlier
power-map form and total singularity. -/
noncomputable def cubicRecognition (hcore : (closureU (centralInvolutions T) (fixedPlane (localModule T
  M) (planeStabilizer T (a.plane i)))) = coreQ (centralInvolutions T)) : Cubic.HLocal.Recognition
  (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane i))) where
  subgroup_le := d.partner.ZS_le_H
  center_le := d.partner.Z_le_ZS
  center_card := d.Z_card
  core_eq := hcore
  extraspecial := d.extraspecial
  center_eq := by
    apply map_injective ((closureU (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer
      T (a.plane i))))).subtype_injective
    rw [subgroupOf_map_subtype, inf_eq_left.mpr
      (d.partner.Z_le_ZS.trans (ZS_le_closureU (centralInvolutions T) (fixedPlane (localModule T M)
        (planeStabilizer T (a.plane i))))), d.core.center_closure]
  plusType := d.plusType
  actor := d.partner.recognized.actorEquiv.trans (MulAut.congr Matrix.PSL3Two.equiv)
  coordinates := d.partner.recognized.coordinates
  inner_action := by
    intro h k hk w
    apply d.partner.recognized.equivariant h k _ w
    apply (MulAut.congr Matrix.PSL3Two.equiv).injective
    rw [show (MulAut.congr Matrix.PSL3Two.equiv)
      (d.partner.recognized.actorEquiv (QuotientGroup.mk' _ h)) =
      MulAut.conj (Matrix.PSL3Two.equiv k) from hk]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
    simpa only [Matrix.PSL3Two.equiv_apply] using
      (Matrix.PSL3Two.equiv.apply_symm_apply x).symm
  quadratic := by
    obtain ⟨z, hzZ, hz, hzgen⟩ := exists_generator_of_card_two (centralInvolutions T) d.Z_card
    intro u
    have he := Extraspecial.square_eq_one_iff_quadratic_zero d.partner.recognized
      (d.square z hz hzgen) hz hzZ d.natural_singular u
    rw [BinaryNaturalDual.quadratic_apply] at he
    constructor
    · intro hu
      exact he.mp (congrArg Subtype.val hu)
    · intro hu
      exact Subtype.ext (he.mpr hu)

/-- Retain the same actor and vector coordinates at the new source element.
The uniform summand interchange is 15.3.58(3). -/
noncomputable def actionAt (t : G) (ht : t ∈ (T : Subgroup G))
    (hout : t ∉ (closureU (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T
      (a.plane i)))) ⊔ ((T : Subgroup G) ⊓ centralizer ((localModule T M) : Set G))) :
    RecognizedAction (T : Subgroup G) (centralInvolutions T) (fixedPlane (localModule T M)
      (planeStabilizer T (a.plane i))) (localModule T M) t where
  actorEquiv := d.partner.recognized.actorEquiv
  coordinates := d.partner.recognized.coordinates
  equivariant := d.partner.recognized.equivariant
  t_mem := ht
  t_mem_H := d.core.T_le_H ht
  t_outside := hout
  swaps_natural := (d.swap ⟨t, d.core.T_le_H ht⟩ ht hout).1
  swaps_dual := (d.swap ⟨t, d.core.T_le_H ht⟩ ht hout).2


/-- Discharge the later core, residual-quotient and involution premises of
the residual-orbit calculation, preserving the original marked coordinates.
The new t fixes ZS/Z by the earlier Sylow fixed-line conclusion. -/
noncomputable def orbitGeometry (hcore : (closureU (centralInvolutions T) (fixedPlane (localModule T M)
  (planeStabilizer T (a.plane i)))) = coreQ (centralInvolutions T))
    (z v t : G) (hz : orderOf z = 2) (hv : orderOf v = 2)
    (hzgen : zpowers z = (centralInvolutions T)) (hvgen : zpowers v = (fixedPlane (localModule T M)
      (planeStabilizer T (a.plane i))) ⊓ (a.plane i))
    (ht : t ∈ (T : Subgroup G)) (ht2 : orderOf t = 2)
    (hout : t ∉ (closureU (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T
      (a.plane i)))) ⊔ ((T : Subgroup G) ⊓ centralizer ((localModule T M) : Set G))) :
    Extraspecial.EarlierGeometry (actionAt d t ht hout) M (a.plane i) z v where
  extraspecial := d.extraspecial
  order128 := d.U_card
  plus_type := d.plusElementary
  center_eq := (cubicRecognition d hcore).center_eq
  Z_le_ZS := d.partner.Z_le_ZS
  ZS_le_H := d.partner.ZS_le_H
  core_eq := hcore
  residualEquiv := residualQuotientEquiv (centralInvolutions T) (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i))) hcore d.partner.recognized.actorEquiv
  t_involution := ht2
  squareForm := {
    form := (d.square z hz hzgen).form
    nondegenerate := (d.square z hz hzgen).nondegenerate
    square := (d.square z hz hzgen).square }
  natural_totally_singular := d.natural_singular
  localGeometry := {
    orthogonal := (d.marked_geometry z v hz hv hzgen hvgen).orthogonal
    z_order := hz
    z_mark := hzgen
    z_mem := (d.marked_geometry z v hz hv hzgen hvgen).z_mem
    z_singular := (d.marked_geometry z v hz hv hzgen hvgen).z_singular
    v_order := hv
    v_mark := hvgen
    definite_le := (d.marked_geometry z v hz hv hzgen hvgen).definite_le
    definite := (d.marked_geometry z v hz hv hzgen hvgen).definite
    perpendicular := (d.marked_geometry z v hz hv hzgen hvgen).perpendicular
    fixed_line := d.fixed_line ⟨t, d.core.T_le_H ht⟩ ht
    naturalCenter := (d.marked_geometry z v hz hv hzgen hvgen).naturalCenter
    naturalCenter_ne := (d.marked_geometry z v hz hv hzgen hvgen).naturalCenter_ne
    dualCenter := (d.marked_geometry z v hz hv hzgen hvgen).dualCenter
    dualCenter_ne := (d.marked_geometry z v hz hv hzgen hvgen).dualCenter_ne
    plane := (d.marked_geometry z v hz hv hzgen hvgen).plane }


include d

open scoped Pointwise in
/-- All conclusions of 15.3.59–61 from the earlier local geometry and exact
recognition. The cubic witnesses and transfer witnesses are constructed
in this proof; the latter use the same z, v and separating involution. -/
theorem source_fusion_of_earlier_data :
    (closureU (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane i)))) =
      coreQ (centralInvolutions T) ∧
      (∃ S : Sylow 2 ((residualY M (centralizerH (centralInvolutions T))) ⊔ (closureU
        (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane i)))) :
        Subgroup G),
        (S : Subgroup ((residualY M (centralizerH (centralInvolutions T))) ⊔ (closureU
          (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane i)))) :
          Subgroup G)).map ((residualY M (centralizerH (centralInvolutions T))) ⊔ (closureU
          (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane
          i))))).subtype = residualSylow T (centralInvolutions T)) ∧
      M = (residualY M (centralizerH (centralInvolutions T))) ⊔ (T : Subgroup G) ∧
      (M : Set G) = ((residualY M (centralizerH (centralInvolutions T))) : Set G) * (T : Set G) ∧
      (∀ x ∈ M, ∃ y ∈ (residualY M (centralizerH (centralInvolutions T))), ∃ t ∈ (T : Subgroup G), x = y
        * t) ∧
      residualSylow T (centralInvolutions T) = (closureU (centralInvolutions T) (fixedPlane (localModule
        T M) (planeStabilizer T (a.plane i)))) ⊔ ((T : Subgroup G) ⊓ centralizer ((localModule T M) :
        Set G)) ∧
      (residualSylow T (centralInvolutions T) : Set G) = ((closureU (centralInvolutions T) (fixedPlane
        (localModule T M) (planeStabilizer T (a.plane i)))) : Set G) * (((T : Subgroup G) ⊓ centralizer
        (localModule T M : Set G)) : Subgroup G) ∧
      (∀ k ∈ residualSylow T (centralInvolutions T), ∃ u ∈ (closureU (centralInvolutions T) (fixedPlane
        (localModule T M) (planeStabilizer T (a.plane i)))), ∃ c ∈ ((T : Subgroup G) ⊓ centralizer
        (localModule T M : Set G)), k = u * c) ∧
      Cubic.Witnesses T M a i ∧ TransferWitnesses T (centralInvolutions T) (fixedPlane (localModule T M)
        (planeStabilizer T (a.plane i))) (a.plane i) := by
  classical
  let := d.extraspecial
  have hVP : (localModule T M) ≤ (pairP (centralInvolutions T) (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i))) g) := d.center_P.le.trans (map_subtype_le _)
  have h59 := Core.source_lemma_15_3_59 T M (residualY M (centralizerH (centralInvolutions T))) (pairI
    (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane i))) g) (pairP
    (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane i))) g)
    (localModule T M) (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane
    i))) Y₁ y t₀
    d.core d.partner d.Y₁_le d.V_not_le_core d.displacement_le d.displacement_card
    d.U_card d.T_le_M d.pair_eq d.pair_le_M d.normalizes_Y rfl hVP d.layers a
    d.centralizer_Y d.characteristic_two d.center_P
  have htransfer := Core.residualSylow_transfer_of_natural_action T M (residualY M (centralizerH
    (centralInvolutions T))) (localModule T M) (centralInvolutions T) (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i))) Y₁ y t₀
    d.core d.partner d.Y₁_le d.V_not_le_core d.displacement_le d.displacement_card
    d.U_card d.T_le_M a d.U_action_card
  have hS : ∃ S : Sylow 2 (pairI (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T
    (a.plane i))) g),
      (S : Subgroup (pairI (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T
        (a.plane i))) g)).map ((pairI (centralInvolutions T) (fixedPlane (localModule T M)
        (planeStabilizer T (a.plane i))) g)).subtype = residualSylow T (centralInvolutions T) := by
    rw [d.pair_eq]
    exact h59.2.1
  obtain ⟨S, hS⟩ := hS
  have hUT : (closureU (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer T (a.plane
    i)))) ≤ (T : Subgroup G) := d.core.closure_le_core.trans d.core.core_le_sylow
  have hcubic := Cubic.source_cubic_witnesses T M d.T_le_M a i g
    d.chosen_mem d.chosen_moving hUT d.core.T_le_H d.normalizes_Y d.centralizer_Y
    d.pair_eq d.center_P S hS h59.2.2.1 h59.2.2.2.1 d.quotientPair
    d.U_image_elementary d.U_image_card d.U_image_other d.centralizer_control
    (cubicRecognition d h59.1) d.swap
  refine ⟨h59.1, h59.2.1, h59.2.2.2.1, h59.2.2.2.2.1, h59.2.2.2.2.2,
    htransfer.1, htransfer.2.1, htransfer.2.2, hcubic, h59.2.2.1, ?_⟩
  obtain ⟨PM3, PH, J, e, z, v, t, P2, PM, SH, R, Pz, Pv,
      hmark, hz, hv, hzgen, hvgen, hvc, hDM, hDH, hPH, hDMM, hJM, hdisj, hcomm,
      hprod, hcoreJ, ht, ht2, htout, htfix, htnot, htnotprod, hDt,
      hP2, hP2T, hP2card, hP2group, hP2idx, hP2center, hP2dihedral, hPMimage, hPM,
      hCH, hSH, hRimage, hR, hRcard, hRDH, hPz, hPv, htH, hnf, hntz, hntv⟩ := hcubic
  let zV : (localModule T M) := ⟨z, (d.marked_geometry z v hz hv hzgen hvgen).z_mem⟩
  let vV : (localModule T M) := ⟨v, a.plane_le i (show v ∈ (fixedPlane (localModule T M)
    (planeStabilizer T (a.plane i))) ⊓ (a.plane i) from hvgen ▸ mem_zpowers v).2⟩
  have hcover := residual_cover_of_earlier_geometry zV vV (actionAt d t ht.1 htnot)
    (orbitGeometry d h59.1 z v t hz hv hzgen hvgen ht.1 ht2 htnot) d.layers
    d.core.action_kernel d.center_P d.intersection_card d.fixed_action_card
    (d.singular zV hz hzgen) (d.hyperplane zV hz hzgen) (d.nonsingular vV hv hvgen)
    S hS (d.separated z v hz hv hzgen hvgen)
  refine ⟨z, v, ⟨t, ht.1⟩, hz, hv, hzgen, hvgen, ?_, ?_, hntz, hntv, hcover⟩
  · exact (Subgroup.orderOf_coe ⟨t, ht.1⟩).symm.trans ht2
  · rwa [htransfer.1]

/-- The actual source consumer: the proved fusion inputs contradict transfer
in a finite simple ambient group. The order-four subgroup is constructed
from the natural action, with no additional transfer witness. -/
theorem false_of_earlier_data [IsSimpleGroup G] : False := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hindex, z, v, t, _, _, _, _, ht, _, htz, htv, hcover⟩ :=
    source_fusion_of_earlier_data d
  have hZS : Nat.card (fixedPlane (localModule T M) (planeStabilizer T (a.plane i))) = 4 := by
    rw [a.card_fixedPlane (X := planeStabilizer T (a.plane i))
      (inf_le_left.trans d.T_le_M), a.image_planeStabilizer]
    exact OrthogonalGeometry.plane_sylow_fixedVectors_card (a.sylowImage T d.T_le_M) i
  exact false_of_residual_fusion T (centralInvolutions T) (fixedPlane (localModule T M) (planeStabilizer
    T (a.plane i))) hZS hindex z v t ht htz htv hcover

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Assembly
