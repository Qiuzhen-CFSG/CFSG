module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.AbelianSourceDouble.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.SourceAlternatives.Double.Action

/-!
# Doubled-natural coordinates on the original small MS pair

For an abelian commutator core of order 64, natural quotient recognition and
the fixed-kernel bounds force two natural copies with injective projection.
The binary action construction then supplies literal conjugation on this core,
a component Sylow marking, and its unique offender inside the radical image.
Transport through the actual inclusion of L ∨ R preserves all these formulas
and uses the same component conjugator for the Sylow and offender.

This discharges the marked-action premise of
`SmallMSPair.abelian_source_double_of_action`; the final source inequality is
assembled in `AbelianSourceDouble`. No classifier, offender-existence, action
or radical-inequality callback is assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.34(2),
printed p.137, common-axis offender argument.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R S : Subgroup G}

private theorem exists_binary_double_quotient (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 64) :
    ∃ q : BinaryMS.AbelianCore.NaturalQuotient (h.binaryInput e) 2,
      Function.Injective q.projection := by
  let := hc
  have hc' : IsMulCommutative (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))) :=
    ⟨⟨fun a b => (binaryCoreEquiv L R).injective (by simp only [map_mul, mul_comm])⟩⟩
  obtain ⟨m, hm, ⟨q⟩⟩ := BinaryMS.AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient
    (h := h.binaryInput e) hc'
  have hk := (h.binaryInput e).abelianCore_fixedKernel_bounds hc' hm q
  have hs := q.card
  have hcard' : Nat.card (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))) = 64 :=
    (Nat.card_congr (binaryCoreEquiv L R).toEquiv).trans hcard
  rw [hcard'] at hs
  rcases hm with rfl | rfl
  · norm_num only [Nat.mul_one, Nat.reducePow] at hs
    omega
  · refine ⟨q, (MonoidHom.ker_eq_bot_iff q.projection).mp ?_⟩
    rw [q.kernel]
    exact Subgroup.card_eq_one.mp (hk.2 rfl)

/-- The original small MS hypotheses construct the actual doubled-natural
join action, with one conjugator marking the component Sylow and its unique
offender. That offender lies in the literal image of R. -/
theorem SmallMSPair.exists_doubledSourceAction (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 64)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    Nonempty (DoubledSourceAction L R S) := by
  let J := L ⊔ R
  let K := L.subgroupOf J
  let T := R.subgroupOf J
  let c : BinaryMS.commutatorCore K ≃* msQ L R :=
    ((BinaryMS.commutatorCore K).equivMapOfInjective J.subtype J.subtype_injective).trans
      (MulEquiv.subgroupCongr (binaryCore_map L R))
  have hcval (x : msQ L R) : (((c.symm x : BinaryMS.commutatorCore K) : J) : G) = x := by
    change (c (c.symm x) : G) = x
    rw [c.apply_symm_apply]
  let := hc
  have hc' : IsMulCommutative (BinaryMS.commutatorCore K) :=
    ⟨⟨fun a b => c.injective (by simp only [map_mul, mul_comm])⟩⟩
  obtain ⟨q, hi⟩ := exists_binary_double_quotient h e hc hcard
  obtain ⟨P, hP⟩ := hS
  have hSP : S.subgroupOf J = (P : Subgroup J) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hTP : T ≤ (P : Subgroup J) := hSP ▸ comap_mono hRS
  obtain ⟨a⟩ := (h.binaryInput e).exists_doubledCoreAction hc' q hi P hTP
  let eK : K ≃* L := subgroupOfEquivOfLe le_sup_left
  refine ⟨{
    marking := (QuotientGroup.congr _ _ eK.symm (pCore_map_iso 2 eK.symm)).trans q.quotientEquiv
    coordinates := c.symm.trans a.coordinates
    normalized := ?_
    actor := a.actor
    equivariant := ?_
    component := ?_
    frame := a.frame
    componentSylow := ?_
    offender_le := a.offender_le
    unique_offender := ?_ }⟩
  · let := (h.binaryInput e).component_normal
    have hn : (BinaryMS.commutatorCore K).Normal := inferInstance
    rw [← binaryCore_map L R]
    apply le_trans _ (le_normalizer_map J.subtype)
    intro j hj
    exact ⟨⟨j, hj⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
  · intro j x y he
    apply a.equivariant j (c.symm x) (c.symm y)
    apply Subtype.ext
    change ((c.symm y : J) : G) = (j : G) * ((c.symm x : J) : G) * (j : G)⁻¹
    rw [hcval, hcval]
    exact he
  · intro l
    exact a.component (eK.symm l)
  · change (S.subgroupOf J ⊓ K).map a.actor = _
    rw [hSP]
    exact a.componentSylow
  · intro E hE
    apply a.unique_offender E
    rwa [hSP] at hE

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
