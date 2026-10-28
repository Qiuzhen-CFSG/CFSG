module

public import Theory.SpecificGroups.Suzuki.MultiplierFieldAction.LocalCover
public import Theory.ElementaryAbelian.Quotient

/-!
# The elementary eight quotient of the lifted root group

The square formula makes the actual Suzuki root group modulo its center
an elementary abelian group of order eight. The original covering map
identifies the quotient of its root preimage by the full preimage of that
center with this same group. Sylow transfer also identifies that full
center preimage with the lifted root group's derived subgroup.

The additional assertion that this subgroup is central is deliberately
not made here: that is the field-action step in GLS3 section 6.3, p.337.
These quotient maps supply the literal input to the subsequent class-two
commutator bound, without presupposing its centrality.
-/

namespace BenderSuzuki.MatrixGroups.MultiplierFieldAction
open Subgroup Theory.GroupTheory

/-- The actual root group modulo its center is elementary abelian. -/
public theorem root_quotient_center_elementary :
    IsElementaryAbelian 2 (SuzukiRootSubgroup 1 ⧸ center (SuzukiRootSubgroup 1)) := by
  have hs (x : SuzukiRootSubgroup 1 ⧸ center (SuzukiRootSubgroup 1)) : x ^ 2 = 1 := by
    induction x using QuotientGroup.induction_on with
    | H x =>
      change QuotientGroup.mk' (center (SuzukiRootSubgroup 1)) x ^ 2 = 1
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr
        (suzukiRootSubgroup_square_mem_center 1 (by decide) x)
  exact {
    toIsMulCommutative := ⟨⟨fun x y =>
      (Commute.of_orderOf_dvd_two (fun z => orderOf_dvd_of_pow_eq_one (hs z)) x y).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

/-- The central quotient of the root group has order eight. -/
public theorem root_quotient_center_card :
    Nat.card (SuzukiRootSubgroup 1 ⧸ center (SuzukiRootSubgroup 1)) = 8 := by
  have h := (center (SuzukiRootSubgroup 1)).index_mul_card
  rw [suzukiRootSubgroup_center_card 1 (by decide),
    suzukiRootSubgroup_card 1 (by decide)] at h
  change Nat.card (SuzukiRootSubgroup 1 ⧸ center (SuzukiRootSubgroup 1)) * 8 = 64 at h
  omega

/-- The derived and central root subgroups are equal on the actual root carrier. -/
public theorem root_commutator_eq_center :
    _root_.commutator (SuzukiRootSubgroup 1) = center (SuzukiRootSubgroup 1) := by
  let := root_quotient_center_elementary
  apply eq_of_le_of_card_ge
    (Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative
        (SuzukiRootSubgroup 1 ⧸ center (SuzukiRootSubgroup 1))))
  rw [root_commutator_card, suzukiRootSubgroup_center_card 1 (by decide)]
  decide

universe u
variable {S U : Type u}
variable [Group S] [Finite S] [IsQuasisimple S]
variable [Group U] [Finite U] [IsQuasisimple U]

/-- The full inverse image of the root center, relative to the lifted root group. -/
@[expose] public noncomputable def rootCenterPreimage
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S) :
    Subgroup (rootPreimage e f) :=
  (center (SuzukiRootSubgroup 1)).comap (rootProjection e f)

public instance rootCenterPreimage_normal
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S) :
    (rootCenterPreimage e f).Normal :=
  inferInstanceAs ((center (SuzukiRootSubgroup 1)).comap (rootProjection e f)).Normal

/-- The quotient equivalence induced by the original restricted covering map. -/
@[expose] public noncomputable def rootQuotientEquiv
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S) :
    (rootPreimage e f ⧸ rootCenterPreimage e f) ≃*
      (SuzukiRootSubgroup 1 ⧸ center (SuzukiRootSubgroup 1)) := by
  let q := (QuotientGroup.mk' (center (SuzukiRootSubgroup 1))).comp (rootProjection e f)
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp (rootProjection_surjective e f)
  have hk : q.ker = rootCenterPreimage e f := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

/-- The elementary quotient belongs to the literal root-center preimage. -/
public theorem rootPreimage_quotient_elementary
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S) :
    IsElementaryAbelian 2 (rootPreimage e f ⧸ rootCenterPreimage e f) := by
  let := root_quotient_center_elementary
  exact IsElementaryAbelian.of_surjective
    (rootQuotientEquiv e f).symm.toMonoidHom (rootQuotientEquiv e f).symm.surjective

public theorem rootPreimage_quotient_card
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S) :
    Nat.card (rootPreimage e f ⧸ rootCenterPreimage e f) = 8 :=
  (Nat.card_congr (rootQuotientEquiv e f).toEquiv).trans root_quotient_center_card

/-- Transfer identifies the full root-center preimage with the derived group;
no class-two assumption is used. -/
public theorem rootPreimage_commutator_eq
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hfour : Nat.card f.toMonoidHom.ker = 4) :
    _root_.commutator (rootPreimage e f) = rootCenterPreimage e f := by
  have himage : (_root_.commutator (rootPreimage e f)).map (rootProjection e f) =
      center (SuzukiRootSubgroup 1) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (rootProjection_surjective e f)]
    exact root_commutator_eq_center
  have h := comap_map_eq_self (rootProjection_ker_le_commutator e f hfour)
  rw [himage] at h
  exact h.symm

/-- The source's subgroup of order 32 is the full inverse image, not an
independently selected central supplement. -/
public theorem rootCenterPreimage_card
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hfour : Nat.card f.toMonoidHom.ker = 4) :
    Nat.card (rootCenterPreimage e f) = 32 := by
  rw [← rootPreimage_commutator_eq e f hfour]
  exact rootPreimage_commutator_card e f hfour

end BenderSuzuki.MatrixGroups.MultiplierFieldAction
