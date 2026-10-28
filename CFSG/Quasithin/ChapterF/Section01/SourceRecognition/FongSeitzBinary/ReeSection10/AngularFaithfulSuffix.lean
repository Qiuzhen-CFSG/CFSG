module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularSuffixSource
public import Theory.GroupTheory.OrderedRootPresentation.FaithfulRealization

/-!
# Faithfulness of the seven-root source realization

Carter's eight ordered factors have unique coordinates. Inverting the word
reverses them into the angular order, so its seven-root suffix inherits the
same uniqueness. The unconditional suffix realization is therefore injective,
allowing the last source coefficients to be checked in the native root group.

Source: Carter 2.5.10--17; Fong--Seitz II, Section 10, (10.27)--(10.41).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition ReeF4.CentralCovers.TwoPrimary
open Theory.GroupTheory.OrderedRootPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

/-- Carter uniqueness in the opposite, native angular order. -/
theorem synchronizedAngularWord_injective :
    Function.Injective (word (AngularPresentation.Parameter m)
      (fun i => synchronizedSourceRoot Q split c i) sourceOrder) := by
  intro p q he
  rcases p with ⟨a,b,d,e,f,g,h,k,u⟩
  rcases q with ⟨a',b',d',e',f',g',h',k',u'⟩
  change word (AngularPresentation.Parameter m) (fun i => synchronizedSourceRoot Q split c i)
    [.inr 0,.inl 1,.inr 3,.inl 3,.inr 1,.inl 2,.inr 2,.inl 0]
    (a,b,d,e,f,g,h,k,u) = word (AngularPresentation.Parameter m)
    (fun i => synchronizedSourceRoot Q split c i)
    [.inr 0,.inl 1,.inr 3,.inl 3,.inr 1,.inl 2,.inr 2,.inl 0]
    (a',b',d',e',f',g',h',k',u') at he
  dsimp only [word] at he
  have point (i : PositiveTables.Root) (a : AngularPresentation.Parameter m i) :
      synchronizedSourceRoot Q split c i a =
        (synchronizedParameterEquiv Q split c i a : X ⧸ Q.D) := rfl
  simp only [point] at he
  have hi : Function.Injective (rootProduct (orderedRoots Q split false 8)) := by
    intro p q hpq
    apply (orderedCoordinates Q split false 8 (by rw [c.rotation_eight])).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using hpq
  rw [positiveRoot_ordered Q split c.rotation_eight] at hi
  change Function.Injective (rootProduct
    [positiveRoot Q split (.inl 0),positiveRoot Q split (.inr 2),
      positiveRoot Q split (.inl 2),positiveRoot Q split (.inr 1),
      positiveRoot Q split (.inl 3),positiveRoot Q split (.inr 3),
      positiveRoot Q split (.inl 1),positiveRoot Q split (.inr 0)]) at hi
  have hh := hi
    (a₁ := ((synchronizedParameterEquiv Q split c (.inl 0) k)⁻¹,
      (synchronizedParameterEquiv Q split c (.inr 2) h)⁻¹,
      (synchronizedParameterEquiv Q split c (.inl 2) g)⁻¹,
      (synchronizedParameterEquiv Q split c (.inr 1) f)⁻¹,
      (synchronizedParameterEquiv Q split c (.inl 3) e)⁻¹,
      (synchronizedParameterEquiv Q split c (.inr 3) d)⁻¹,
      (synchronizedParameterEquiv Q split c (.inl 1) b)⁻¹,
      (synchronizedParameterEquiv Q split c (.inr 0) a)⁻¹,PUnit.unit))
    (a₂ := ((synchronizedParameterEquiv Q split c (.inl 0) k')⁻¹,
      (synchronizedParameterEquiv Q split c (.inr 2) h')⁻¹,
      (synchronizedParameterEquiv Q split c (.inl 2) g')⁻¹,
      (synchronizedParameterEquiv Q split c (.inr 1) f')⁻¹,
      (synchronizedParameterEquiv Q split c (.inl 3) e')⁻¹,
      (synchronizedParameterEquiv Q split c (.inr 3) d')⁻¹,
      (synchronizedParameterEquiv Q split c (.inl 1) b')⁻¹,
      (synchronizedParameterEquiv Q split c (.inr 0) a')⁻¹,PUnit.unit)) (by
      have hv := congrArg Inv.inv he
      simpa only [sourceOrder,List.ofFn_succ,sourceIndex,Fin.isValue,
        Matrix.cons_val_zero,Matrix.cons_val_succ,word,rootProduct,
        synchronizedSourceRoot,MonoidHom.coe_comp,Function.comp_apply,
        MulEquiv.coe_toMonoidHom,Subgroup.subtype_apply,Subgroup.coe_inv,
        mul_inv_rev,inv_one,mul_one,one_mul,mul_assoc] using hv)
  have hk := (synchronizedParameterEquiv Q split c (.inl 0)).injective
    (inv_injective (congrArg (fun z => z.1) hh))
  have hh' := (synchronizedParameterEquiv Q split c (.inr 2)).injective
    (inv_injective (congrArg (fun z => z.2.1) hh))
  have hg := (synchronizedParameterEquiv Q split c (.inl 2)).injective
    (inv_injective (congrArg (fun z => z.2.2.1) hh))
  have hf := (synchronizedParameterEquiv Q split c (.inr 1)).injective
    (inv_injective (congrArg (fun z => z.2.2.2.1) hh))
  have he' := (synchronizedParameterEquiv Q split c (.inl 3)).injective
    (inv_injective (congrArg (fun z => z.2.2.2.2.1) hh))
  have hd := (synchronizedParameterEquiv Q split c (.inr 3)).injective
    (inv_injective (congrArg (fun z => z.2.2.2.2.2.1) hh))
  have hb := (synchronizedParameterEquiv Q split c (.inl 1)).injective
    (inv_injective (congrArg (fun z => z.2.2.2.2.2.2.1) hh))
  have ha := (synchronizedParameterEquiv Q split c (.inr 0)).injective
    (inv_injective (congrArg (fun z => z.2.2.2.2.2.2.2.1) hh))
  subst a'; subst b'; subst d'; subst e'; subst f'; subst g'; subst h'; subst k'
  rfl

/-- The suffix transports native equality faithfully into the marked source. -/
theorem angularSuffixEval_injective : Function.Injective (angularSuffixEval Q split c) := by
  apply realization_injective (AngularSuffix.table m) (AngularSuffix.native_equations m)
    (angularSuffixEquations Q split c) AngularSuffix.suffix_nodup
    (AngularPresentation.native_tail_injective m (.inr 0))
  exact word_injective_suffix (AngularPresentation.Parameter m)
    (synchronizedSourceRoot Q split c)
    (show sourceOrder = [.inr 0] ++ AngularSuffix.suffixOrder by rfl)
    (synchronizedAngularWord_injective Q split c)

/-- Every suffix value lies in the actual Suzuki simple-root remainder. -/
theorem angularSuffixEval_mem_remainder (v : AngularSuffix.Carrier m) :
    angularSuffixEval Q split c v ∈ simpleRemainder Q split 1 := by
  obtain ⟨p,hp⟩ := (AngularSuffix.native_equations m).exists_word
    (AngularSuffix.table m) AngularSuffix.suffix_nodup v v.property
  have hv : v = ⟨word (AngularPresentation.Parameter m)
      (fun i => AngularPresentation.nativeRoot m i) AngularSuffix.suffixOrder p,
        word_mem_join _ _ _ _⟩ := Subtype.ext hp.symm
  rw [hv,angularSuffixEval_word]
  apply (join_le (AngularPresentation.Parameter m) (synchronizedSourceRoot Q split c)
    AngularSuffix.suffixOrder (simpleRemainder Q split 1) ?_)
    (word_mem_join _ _ _ _)
  intro i hi z hz
  obtain ⟨a,rfl⟩ := hz
  exact positiveRoot_le_remainder Q split c i 1 ((AngularSuffix.suffix_member i).mp hi)
    (synchronizedParameterEquiv Q split c i a).property

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
