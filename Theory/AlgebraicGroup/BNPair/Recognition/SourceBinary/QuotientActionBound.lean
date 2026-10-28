module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OddOuterPanel
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.LocalClosureNormal

/-!
# Bounding the panel kernel through a normal factor's quotient action

For a normal factor A supplementing the full Borel, the action of AU on
A/O₂(A) has kernel O₂(AU) when that quotient is centerfree. The two-core
is normal in the marked endpoint and lies in U intersect K. Thus a bound
on quotient-automorphism two-subgroups bounds [U : U intersect K]. If the
bound is the canonical root order, the root/remainder index identity
forces the remainder into K, proving the required instance of (2B).

Independently, the two-part of the full panel kernel inside the whole
local closure is exactly that closure's two-core. Both statements preserve
relative normality, the full kernel and the actual quotient maps.
Source: Fong--Seitz I (2B), (5B)--(5C), pp.7--9,25--26.
DihedralLocal supplies the original order-ten factor and proves the bound;
no universal assertion excluding the type VI exception is made.
-/

public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- A bound on the actual quotient-automorphism two-subgroups discharges (2B). -/
theorem remainder_le_kernel_of_quotient_action_bound (i : Fin 2)
    (A : Subgroup (X ⧸ Q.D))
    (hn : Q.tits.standardParabolic {Q.simple i} ≤ normalizer (A : Set (X ⧸ Q.D)))
    (hgen : A ⊔ Q.tits.B = Q.tits.standardParabolic {Q.simple i})
    (hz : center (A ⧸ pCore 2 A) = ⊥)
    (hb : ∀ V : Subgroup (MulAut (A ⧸ pCore 2 A)), IsPGroup 2 V →
      Nat.card V ≤ Nat.card (simpleRoot Q split i)) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  let M := Q.tits.standardParabolic {Q.simple i}
  let J := A ⊔ split.U
  let C := J.pCoreIn 2
  let R := LocalCover.radical Q split i
  have hUM : split.U ≤ M := split.U_le.trans (Q.tits.B_le_standardParabolic _)
  have hUA : split.U ≤ normalizer (A : Set (X ⧸ Q.D)) := hUM.trans hn
  let a := pCoreJoinAction 2 hUA
  have hCU : C ≤ split.U := by
    have hh := pCoreIn_le_sylow J (split.sylow.subtype (show split.U ≤ J from le_sup_right))
    change C ≤ (split.U.subgroupOf J).map J.subtype at hh
    rwa [map_subgroupOf_eq_of_le (show split.U ≤ J from le_sup_right)] at hh
  have hMJ : M ≤ normalizer (J : Set (X ⧸ Q.D)) := by
    change Q.tits.standardParabolic {Q.simple i} ≤ _
    rw [← hgen]
    apply sup_le ((show A ≤ J from le_sup_left).trans J.le_normalizer)
    exact (le_inf ((Q.tits.B_le_standardParabolic _).trans hn) split.normalizes).trans
      (normalizer_inf_normalizer_le_normalizer_sup A split.U)
  have hMC : M ≤ normalizer (C : Set (X ⧸ Q.D)) :=
    hMJ.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hCR : C ≤ R := by
    apply le_inf hCU
    let : (C.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMC
    have hcore : C.subgroupOf M ≤ (Q.tits.B.subgroupOf M).normalCore :=
      normal_le_normalCore.mpr (subgroupOf_mono _ (hCU.trans split.U_le))
    intro x hx
    exact ⟨⟨x,hUM (hCU hx)⟩,hcore hx,rfl⟩
  have hCindex : C.relIndex split.U = Nat.card ((split.U.subgroupOf J).map a) := by
    rw [← relIndex_ker, pCoreJoinAction_kernel 2 hUA split.isTwo hz]
    change C.relIndex split.U = (pCore 2 J).relIndex (split.U.subgroupOf J)
    rw [← relIndex_map_map_of_injective (f := J.subtype) _ _ J.subtype_injective,
      map_subgroupOf_eq_of_le (show split.U ≤ J from le_sup_right)]
    rfl
  have hbound : R.relIndex split.U ≤ Nat.card (simpleRoot Q split i) :=
    (relIndex_le_of_le_left (L := split.U) hCR
      (show C.relIndex split.U ≠ 0 from index_ne_zero_of_finite)).trans
        (hCindex ▸ hb _ (split.isTwo.comap_subtype.map a))
  have hRV : R ≤ simpleRemainder Q split i := unipotent_inf_kernel_le_remainder Q split i
  have hle : simpleRemainder Q split i ≤ R := by
    apply relIndex_eq_one.mp
    have he := relIndex_mul_relIndex R (simpleRemainder Q split i) split.U hRV inf_le_left
    have hv : (simpleRemainder Q split i).relIndex split.U =
        Nat.card (simpleRoot Q split i) := simpleRemainder_index Q split i
    rw [hv] at he
    have hpos := Nat.card_pos (α := simpleRoot Q split i)
    have hpos' : 0 < R.relIndex (simpleRemainder Q split i) :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    nlinarith
  exact hle.trans inf_le_right
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.LocalCover
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

/-- The two-part of the panel kernel is the two-core of the whole local closure. -/
theorem radicalInClosure_eq_twoCore :
    radicalInClosure Q split i = pCore 2 (localClosure Q split i) := by
  let C := localClosure Q split i
  let R := C.pCoreIn 2
  have hRU : R ≤ split.U := by
    have hh := pCoreIn_le_sylow C (split.sylow.subtype (show split.U ≤ C from le_sup_left))
    change R ≤ (split.U.subgroupOf C).map C.subtype at hh
    rwa [map_subgroupOf_eq_of_le (show split.U ≤ C from le_sup_left)] at hh
  have hn : Q.tits.standardParabolic {Q.simple i} ≤ normalizer (R : Set (X ⧸ Q.D)) :=
    (closure_parabolic_normalizes Q split i).trans
      (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hRK : R ≤ localKernel Q i := by
    let M := Q.tits.standardParabolic {Q.simple i}
    let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hn
    have hh : R.subgroupOf M ≤ (Q.tits.B.subgroupOf M).normalCore :=
      normal_le_normalCore.mpr (subgroupOf_mono _ (hRU.trans split.U_le))
    intro x hx
    exact ⟨⟨x,Q.tits.B_le_standardParabolic _ (split.U_le (hRU hx))⟩,hh hx,rfl⟩
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, (split.isTwo.to_le
      (show radical Q split i ≤ split.U from inf_le_left)).comap_subtype⟩
  · intro x hx
    have hm : (x : X ⧸ Q.D) ∈ R := mem_map_of_mem C.subtype hx
    exact ⟨hRU hm,hRK hm⟩

/-- The literal local cover is the two-core quotient of its whole root closure. -/
noncomputable def coreQuotientEquiv :
    CoverGroup Q split i ≃* (localClosure Q split i ⧸ pCore 2 (localClosure Q split i)) :=
  QuotientGroup.quotientMulEquivOfEq (radicalInClosure_eq_twoCore Q split i)

@[simp] theorem coreQuotientEquiv_mk (x : localClosure Q split i) :
    coreQuotientEquiv Q split i (QuotientGroup.mk' (radicalInClosure Q split i) x) =
      QuotientGroup.mk' (pCore 2 (localClosure Q split i)) x := by rfl
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.LocalCover

