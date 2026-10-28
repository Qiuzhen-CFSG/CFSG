module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.ReturningPair
public import Theory.SpecificGroups.MinusExtraspecial.InvolutionCentralizerGeometry
public import Theory.GroupTheory.SubgroupProductCard

/-!
# The canonical root product has order 64

The H-type centralizer comparison puts z in the conjugate core Qᵍ. Squares in Q
are 1 or z, while squares in Qᵍ are 1 or zᵍ. Consequently their intersection
has exponent two. The concrete minus-extraspecial centralizer calculation
identifies this intersection with E and gives order sixteen for each of
Q ∩ Hᵍ and Qᵍ ∩ H. The literal set-product formula then gives |R| = 64.

This proves the w = 2 intersection and order assertions without assuming
anything about the normalizer action or the other involution centralizer.
The common core calculations are adapted from the J₂ `SourceFrame`
implementation; reciprocity here uses only H-type, not its two-class census.
Source: Aschbacher, *Sporadic Groups* (1994), 46.2–46.3, printed p.251.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise

namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen.ReturningPair

variable {G : Type*} [Group G] [Finite G] {D : Seed G} (P : ReturningPair D)

private noncomputable def coreEquiv : ambientCore D.z ≃* MinusExtraspecial.Model :=
  ((localCore D.z).equivMapOfInjective (involutionCentralizer D.z).subtype
    (involutionCentralizer D.z).subtype_injective).symm.trans D.localType.core_equiv.some

private theorem z_center :
    (⟨D.z, HTypeAt.involution_mem_core⟩ : ambientCore D.z) ∈ center (ambientCore D.z) := by
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (ambientCore_le D.z x.property))

private theorem z_ne_one : D.z ≠ 1 := by
  intro h
  have hz := D.localType.involution
  simp [h] at hz

private theorem u_ne_one : P.u ≠ 1 := by
  intro h
  have hu := P.u_order
  simp [h] at hu

theorem u_mem_conjugateCore : P.u ∈ P.conjugateCore :=
  mem_map_of_mem (MulAut.conj P.g).toMonoidHom HTypeAt.involution_mem_core

theorem E_le_conjugateCore : P.E ≤ P.conjugateCore :=
  sup_le (zpowers_le.mpr (P.z_mem_conjugateCore ))
    (zpowers_le.mpr P.u_mem_conjugateCore)

private noncomputable def conjugateCoreEquiv : P.conjugateCore ≃* MinusExtraspecial.Model :=
  ((ambientCore D.z).equivMapOfInjective (MulAut.conj P.g).toMonoidHom
    (MulAut.conj P.g).injective).symm.trans coreEquiv

private theorem u_center :
    (⟨P.u, P.u_mem_conjugateCore⟩ : P.conjugateCore) ∈ center P.conjugateCore := by
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (P.conjugateCore_le x.property))

/-- The square alternatives in the two cores have different central involutions. -/
theorem core_inf_square {x : G} (hx : x ∈ ambientCore D.z ⊓ P.conjugateCore) :
    x ^ 2 = 1 := by
  have hleft : x ^ 2 = 1 ∨ x ^ 2 = D.z := by
    have h := MinusExtraspecial.square_eq_one_or_of_equiv coreEquiv z_center
      (by exact fun h => z_ne_one (congrArg Subtype.val h)) (⟨x, hx.1⟩ : ambientCore D.z)
    exact h.imp (congrArg Subtype.val) (congrArg Subtype.val)
  have hright : x ^ 2 = 1 ∨ x ^ 2 = P.u := by
    have h := MinusExtraspecial.square_eq_one_or_of_equiv P.conjugateCoreEquiv P.u_center
      (by exact fun h => P.u_ne_one (congrArg Subtype.val h)) (⟨x, hx.2⟩ : P.conjugateCore)
    exact h.imp (congrArg Subtype.val) (congrArg Subtype.val)
  rcases hleft with h | h
  · exact h
  · exact hright.resolve_right (fun hu => P.ne (hu.symm.trans h))

/-- The literal intersection asserted in source 46.2(1). -/
theorem core_inf_eq_E : ambientCore D.z ⊓ P.conjugateCore = P.E := by
  apply le_antisymm
  · intro x hx
    have h := MinusExtraspecial.commuting_square_one_of_equiv coreEquiv z_center
      (by exact fun h => z_ne_one (congrArg Subtype.val h))
      (u := (⟨P.u, P.mem_core⟩ : ambientCore D.z))
      (x := (⟨x, hx.1⟩ : ambientCore D.z))
      (Subtype.ext (P.u_order ▸ pow_orderOf_eq_one P.u))
      (by exact fun h => P.u_ne_one (congrArg Subtype.val h))
      (by exact fun h => P.ne (congrArg Subtype.val h))
      (Subtype.ext (mem_centralizer_singleton_iff.mp (P.conjugateCore_le hx.2)))
      (Subtype.ext (P.core_inf_square hx))
    rcases h with h | h | h | h
    · exact by simpa only [show x = 1 from congrArg Subtype.val h] using P.E.one_mem
    · exact by simpa only [show x = D.z from congrArg Subtype.val h] using P.z_mem_E
    · exact by simpa only [show x = P.u from congrArg Subtype.val h] using P.u_mem_E
    · exact by simpa only [show x = D.z * P.u from congrArg Subtype.val h] using P.E.mul_mem P.z_mem_E P.u_mem_E
  · exact le_inf P.E_le_core (P.E_le_conjugateCore )

omit [Finite G] in
private theorem card_inf_centralizer (Q : Subgroup G) (u : Q) :
    Nat.card (Q ⊓ involutionCentralizer (u : G) : Subgroup G) =
      Nat.card (centralizer ({u} : Set Q)) := by
  let e : (Q ⊓ involutionCentralizer (u : G) : Subgroup G) ≃
      centralizer ({u} : Set Q) :=
    { toFun := fun x => ⟨⟨x, x.property.1⟩,
        mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))⟩
      invFun := fun x => ⟨x.val, x.val.property,
        mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

theorem leftCore_card : Nat.card P.leftCore = 16 := by
  rw [leftCore, card_inf_centralizer (ambientCore D.z) ⟨P.u, P.mem_core⟩]
  exact MinusExtraspecial.centralizer_card_of_equiv coreEquiv z_center
    (fun h => z_ne_one (congrArg Subtype.val h))
    (Subtype.ext (P.u_order ▸ pow_orderOf_eq_one P.u))
    (fun h => P.u_ne_one (congrArg Subtype.val h))
    (fun h => P.ne (congrArg Subtype.val h))

theorem rightCore_card : Nat.card P.rightCore = 16 := by
  rw [rightCore, card_inf_centralizer P.conjugateCore ⟨D.z, P.z_mem_conjugateCore ⟩]
  exact MinusExtraspecial.centralizer_card_of_equiv P.conjugateCoreEquiv P.u_center
    (fun h => P.u_ne_one (congrArg Subtype.val h))
    (Subtype.ext (D.localType.involution ▸ pow_orderOf_eq_one D.z))
    (fun h => z_ne_one (congrArg Subtype.val h))
    (fun h => P.ne (congrArg Subtype.val h).symm)

theorem leftCore_inf_rightCore : P.leftCore ⊓ P.rightCore = P.E := by
  apply le_antisymm
  · exact (inf_le_inf inf_le_left inf_le_left).trans (P.core_inf_eq_E ).le
  · exact le_inf
      (le_inf P.E_le_core (P.E_le_R.trans (P.R_le_double_centralizer.trans inf_le_right)))
      (le_inf (P.E_le_conjugateCore )
        (P.E_le_R.trans (P.R_le_double_centralizer.trans inf_le_left)))

/-- The canonical source product has order 64, before normalizer recognition. -/
theorem R_card : Nat.card P.R = 64 := by
  have h := card_set_mul_mul_card_inf P.leftCore P.rightCore
  rw [← P.R_coe, P.leftCore_inf_rightCore , P.E_card,
    P.leftCore_card, P.rightCore_card ] at h
  change Nat.card P.R * 4 = 16 * 16 at h
  omega

/-- R meets the original core in its first marked factor. -/
theorem R_inf_core : P.R ⊓ ambientCore D.z = P.leftCore := by
  apply le_antisymm
  · exact le_inf inf_le_right
      (inf_le_left.trans (P.R_le_double_centralizer.trans inf_le_right))
  · exact le_inf le_sup_left inf_le_left

/-- R meets the conjugate core in its second marked factor. -/
theorem R_inf_conjugateCore : P.R ⊓ P.conjugateCore = P.rightCore := by
  apply le_antisymm
  · exact le_inf inf_le_right
      (inf_le_left.trans (P.R_le_double_centralizer.trans inf_le_left))
  · exact le_inf le_sup_right inf_le_left

theorem R_isPGroup : IsPGroup 2 P.R :=
  IsPGroup.of_card (n := 6) (P.R_card )

end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen.ReturningPair
