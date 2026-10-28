module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PanelKernel
public import Theory.GroupTheory.PCoreQuotientInnerSupplement
public import Theory.GroupAction.SylowPointwiseInner
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# The source panel remainder from an odd outer quotient

Let A be normal in the marked endpoint and supplement its full Borel.
If A/O₂(A) is centerfree with odd outer automorphism group, the normal
unipotent two-group acts on that quotient by inner automorphisms. The
Sylow supplement theorem therefore gives U = T O₂(AU), where T is the
actual embedded Sylow of A. The subgroup AU is normal in the endpoint,
so its two-core lies in the full panel kernel K.

Consequently [U : U ∩ K] is at most |T/O₂(A)|. When the latter is the
canonical simple root order, the root/remainder index formula and
U ∩ K ≤ U ∩ Uˢ force equality and hence U ∩ Uˢ ≤ K. Normality is relative
to the endpoint throughout. Neither perfectness nor a Weyl-order
restriction is required.

This is an alternative local proof of Fong--Seitz I (2B), pp.7--9,
for the odd-outer source branch. The original Suzuki application supplies
the actual model, outer index and cardinality. No universal exclusion of
the type VI exception or rank-two classification is asserted.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Odd outer index and the literal quotient-Sylow order discharge the local
section containment without any perfectness hypothesis. -/
theorem remainder_le_kernel_of_odd_outer (i : Fin 2)
    (A : Subgroup (X ⧸ Q.D))
    (hn : Q.tits.standardParabolic {Q.simple i} ≤ normalizer (A : Set (X ⧸ Q.D)))
    (hgen : A ⊔ Q.tits.B = Q.tits.standardParabolic {Q.simple i})
    (T : Sylow 2 A) (hTU : (T : Subgroup A).map A.subtype ≤ split.U)
    (hz : center (A ⧸ pCore 2 A) = ⊥)
    (ho : Odd (MulAut.conj : (A ⧸ pCore 2 A) →* MulAut (A ⧸ pCore 2 A)).range.index)
    (hc : Nat.card (simpleRoot Q split i) =
      Nat.card ((T : Subgroup A).map (QuotientGroup.mk' (pCore 2 A)))) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  let M := Q.tits.standardParabolic {Q.simple i}
  let J := A ⊔ split.U
  let R := LocalCover.radical Q split i
  let C := J.pCoreIn 2
  let S := (T : Subgroup A).map A.subtype
  have hUM : split.U ≤ M := split.U_le.trans (Q.tits.B_le_standardParabolic _)
  have hUA : split.U ≤ normalizer (A : Set (X ⧸ Q.D)) := hUM.trans hn
  have hinner : ∀ u : split.U, pCoreJoinAction 2 hUA (inclusion le_sup_right u) ∈
      MulAut.innerSubgroup (A ⧸ pCore 2 A) := by
    intro u
    obtain ⟨k,hk⟩ := split.isTwo u
    let f := (pCoreJoinAction 2 hUA).comp (inclusion le_sup_right)
    obtain ⟨a,ha⟩ := MulAut.inner_of_two_pow_eq_one_of_odd_index ho (f u)
      (by rw [← map_pow,hk,map_one])
    exact ⟨a,ha.symm⟩
  have hUS : split.U = S ⊔ C :=
    sup_core_factor_of_inner_action A split.U hUA split.isTwo hz T hTU hinner
  have hCU : C ≤ split.U := hUS ▸ le_sup_right
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
  have hSR : S ⊔ R = split.U :=
    le_antisymm (sup_le hTU inf_le_left) (hUS ▸ sup_le le_sup_left (hCR.trans le_sup_right))
  have hAR : A.pCoreIn 2 ≤ R := by
    have hAU : A.pCoreIn 2 ≤ split.U := (pCoreIn_le_sylow A T).trans hTU
    apply le_inf hAU
    have hMA := hn.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
    let : ((A.pCoreIn 2).subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMA
    have hcore : (A.pCoreIn 2).subgroupOf M ≤ (Q.tits.B.subgroupOf M).normalCore :=
      normal_le_normalCore.mpr (subgroupOf_mono _ (hAU.trans split.U_le))
    intro x hx
    exact ⟨⟨x,hUM (hAU hx)⟩,hcore hx,rfl⟩
  have hind : R.relIndex split.U = R.relIndex S := by
    let R' := R.subgroupOf split.U
    let S' := S.subgroupOf split.U
    let : R'.Normal := normal_subgroupOf_of_le_normalizer
      (hUM.trans (LocalCover.radical_parabolic_normalizes Q split i))
    have hjoin : S' ⊔ R' = ⊤ := by
      rw [← subgroupOf_sup hTU (show R ≤ split.U from inf_le_left), hSR, subgroupOf_self]
    calc
      R.relIndex split.U = R'.relIndex (⊤ : Subgroup split.U) := by
        rw [relIndex_top_right]; rfl
      _ = R'.relIndex (S' ⊔ R') := congrArg (R'.relIndex ·) hjoin.symm
      _ = R'.relIndex S' := relIndex_sup_right _ _
      _ = R.relIndex S := relIndex_subgroupOf hTU
  have hbound : R.relIndex split.U ≤ Nat.card (simpleRoot Q split i) := by
    rw [hind,hc]
    have hle := relIndex_le_of_le_left (L := S) hAR
      (show (A.pCoreIn 2).relIndex S ≠ 0 from index_ne_zero_of_finite)
    have he : (A.pCoreIn 2).relIndex S =
        Nat.card ((T : Subgroup A).map (QuotientGroup.mk' (pCore 2 A))) := by
      rw [pCoreIn, relIndex_map_map_of_injective _ _ A.subtype_injective]
      simpa only [QuotientGroup.ker_mk'] using
        (relIndex_ker (T : Subgroup A) (QuotientGroup.mk' (pCore 2 A)))
    exact he ▸ hle
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
