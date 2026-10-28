module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2
public import Theory.GroupAction.AutomorphismFixedResidual
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionFusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterTwoGroup
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCores.Model

/-!
# Three-core calculations for outer involutions of the actual J₂ carrier

The checked standard-pair calculations identify the degree-100 permutation
extension with all automorphisms; its checked outer-involution fusion therefore
covers every noninner involution. An identification of the representative's
entire fixed subgroup with PGL₂(7) then identifies each embedded fixed perfect
residual with PSL₂(7), and hence gives its inner image trivial three-core.

For the second calculation, an inner automorphism centralizing both the actor
and that inner residual comes from an element of the fixed subgroup centralizing
its perfect residual. The model calculation makes this element trivial. Thus the
intersection of the two actual automorphism centralizers injects into Out(J₂),
a two-group, and has order prime to three. The final theorem applies these
calculations to the literal intermediate subgroup in the fixed-residual criterion.

The representative equivalence remains an explicit mathematical input, produced
by the separate `OuterInvolutionCentralizer` calculation. These theorems complete
the reduction to that input, not the unconditional source assertion.

Sources: GLS3, Table 5.3g, class 2C and notes (3)–(4); Aschbacher--Smith,
proof of 15.3.38, printed p.1137. The imported degree-100 ATLAS carrier,
standard-pair certificates and exceptional isomorphism retain their attribution.
-/

public section
namespace Sporadic.LeechRelated.J2.OuterInvolutionCores
open Subgroup Theory.GroupTheory
open ExceptionalParabolics GeneratorPair

private theorem conj_injective : Function.Injective (MulAut.conj : Carrier →* MulAut Carrier) := by
  intro x y h
  have h' : intoExtension x = intoExtension y := extensionAction_injective (by
    simpa only [extensionAction_inner] using h)
  exact (Subgroup.inclusion_injective (show generated ≤ extension from le_sup_left)) h'

/-- Full automorphism coverage transfers the checked permutation-extension fusion. -/
theorem outer_involution_fusion (a : MulAut Carrier) (ha : orderOf a = 2)
    (ho : a ∉ (MulAut.conj : Carrier →* MulAut Carrier).range) :
    IsConj involutionAut a := by
  obtain ⟨x, rfl⟩ := extensionAction_surjective_of_pair_calculations
    first_generator_conjugate second_generator_orbits a
  have hx : orderOf x = 2 :=
    (orderOf_injective extensionAction extensionAction_injective x).symm.trans ha
  have hxout : x ∉ intoExtension.range := by
    rintro ⟨g, rfl⟩
    exact ho ⟨g, (extensionAction_inner g).symm⟩
  simpa only [extensionAction_involution] using extensionAction.map_isConj
    (OuterInvolutionFusion.extension_outer_involution_fusion x hx hxout)

/-- A representative identification covers the whole fixed subgroup of every outer involution. -/
theorem outer_fixed_equiv_of_representative
    (model : involutionAut.fixedSubgroup ≃* GorensteinWalter.PGL2 (ZMod 7))
    (a : MulAut Carrier) (ha : orderOf a = 2)
    (ho : a ∉ (MulAut.conj : Carrier →* MulAut Carrier).range) :
    Nonempty (a.fixedSubgroup ≃* MulAut Matrix.PSL3Two.PSL) := by
  obtain ⟨e, he⟩ := isConj_iff.mp (outer_involution_fusion a ha ho)
  have ha' : a = MulAut.congr e involutionAut := by
    rw [← he]
    rfl
  subst a
  exact ⟨((MulAut.fixedSubgroupCongr e involutionAut).symm.trans model).trans
    Matrix.PSL3Two.Automorphisms.pgl2SevenEquivAut⟩

/-- The actual embedded fixed perfect residual is PSL₂(7), conditional on the fixed-group model. -/
noncomputable def fixedResidualEquivPSL2 (a : MulAut Carrier)
    (e : a.fixedSubgroup ≃* MulAut Matrix.PSL3Two.PSL) :
    MulAut.fixedPerfectResidual a ≃* GorensteinWalter.PSL2 (ZMod 7) :=
  (((solvableResidual a.fixedSubgroup).equivMapOfInjective
    a.fixedSubgroup.subtype a.fixedSubgroup.subtype_injective).symm.trans
    (Model.residualEquiv e)).trans Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm

/-- Conjugation embeds the fixed residual into precisely the inner subgroup used by the core criterion. -/
noncomputable def fixedResidualInnerEquivPSL2 (a : MulAut Carrier)
    (e : a.fixedSubgroup ≃* MulAut Matrix.PSL3Two.PSL) :
    MulAut.fixedPerfectResidualInner a ≃* GorensteinWalter.PSL2 (ZMod 7) :=
  ((MulAut.fixedPerfectResidual a).equivMapOfInjective
    MulAut.conj conj_injective).symm.trans (fixedResidualEquivPSL2 a e)

/-- The first calculation in the literal fixed-residual criterion. -/
theorem fixedResidualInner_threeCore_eq_bot (a : MulAut Carrier)
    (e : a.fixedSubgroup ≃* MulAut Matrix.PSL3Two.PSL) :
    pCore 3 (MulAut.fixedPerfectResidualInner a) = ⊥ := by
  let f := (fixedResidualInnerEquivPSL2 a e).trans
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two
  apply ((pCore 3 (MulAut.fixedPerfectResidualInner a)).map_eq_bot_iff_of_injective
    (f := f.toMonoidHom) f.injective).mp
  rw [pCore_map_iso, Model.threeCore_psl_eq_bot]

/-- The intersection of the two literal automorphism centralizers embeds in Out(J₂). -/
theorem fixedResidual_centralizer_isTwoGroup (a : MulAut Carrier)
    (e : a.fixedSubgroup ≃* MulAut Matrix.PSL3Two.PSL) :
    IsPGroup 2 (centralizer ({a} : Set (MulAut Carrier)) ⊓
      centralizer (MulAut.fixedPerfectResidualInner a : Set (MulAut Carrier)) :
        Subgroup (MulAut Carrier)) := by
  let C : Subgroup (MulAut Carrier) := centralizer ({a} : Set (MulAut Carrier)) ⊓
    centralizer (MulAut.fixedPerfectResidualInner a : Set (MulAut Carrier))
  let f : C →* MulAut.Outer Carrier :=
    (QuotientGroup.mk' (MulAut.innerSubgroup Carrier)).comp C.subtype
  apply outer_isTwoGroup.of_injective f
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply le_bot_iff.mp
  intro b hb
  have hbinner : (b : MulAut Carrier) ∈ MulAut.innerSubgroup Carrier :=
    (QuotientGroup.eq_one_iff _).mp hb
  obtain ⟨x, hx⟩ := hbinner
  have hcomm : MulAut.conj x * a = a * MulAut.conj x := by
    rw [hx]
    exact mem_centralizer_singleton_iff.mp b.property.1
  have hfixed : a x = x := by
    apply conj_injective
    have hconj : MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by
      ext z
      simp
    rw [hconj, ← hcomm, mul_inv_cancel_right]
  let y : a.fixedSubgroup := ⟨x, (MulAut.mem_fixedSubgroup a x).mpr hfixed⟩
  have hy : y ∈ centralizer (solvableResidual a.fixedSubgroup : Set a.fixedSubgroup) := by
    intro z hz
    apply Subtype.ext
    apply conj_injective
    have hzi : MulAut.conj (z : Carrier) ∈ MulAut.fixedPerfectResidualInner a :=
      mem_map_of_mem _ (mem_map_of_mem a.fixedSubgroup.subtype hz)
    have hc := b.property.2 (MulAut.conj (z : Carrier)) hzi
    rw [← hx] at hc
    change MulAut.conj ((z : Carrier) * x) = MulAut.conj (x * (z : Carrier))
    simpa only [map_mul] using hc
  have hyone : y = 1 := mem_bot.mp ((Model.centralizer_residual e).le hy)
  have hxone : x = 1 := congrArg Subtype.val hyone
  apply mem_bot.mpr
  apply Subtype.ext
  change (b : MulAut Carrier) = 1
  rw [← hx, hxone, map_one]

/-- The centralizer order is prime to three; no enumeration of that centralizer is needed. -/
theorem fixedResidual_centralizer_coprime (a : MulAut Carrier)
    (e : a.fixedSubgroup ≃* MulAut Matrix.PSL3Two.PSL) :
    Nat.Coprime 3 (Nat.card (centralizer ({a} : Set (MulAut Carrier)) ⊓
      centralizer (MulAut.fixedPerfectResidualInner a : Set (MulAut Carrier)) :
        Subgroup (MulAut Carrier))) := by
  obtain ⟨n, hn⟩ := (fixedResidual_centralizer_isTwoGroup a e).exists_card_eq
  rw [hn]
  exact (by decide : Nat.Coprime 3 2).pow_right n

/-- Both precise fixed-residual calculations from an actual fixed-group equivalence. -/
theorem fixedResidualThreeCoreData_of_fixedEquiv (a : MulAut Carrier)
    (e : a.fixedSubgroup ≃* MulAut Matrix.PSL3Two.PSL) :
    MulAut.FixedResidualThreeCoreData a :=
  ⟨fixedResidualInner_threeCore_eq_bot a e, fixedResidual_centralizer_coprime a e⟩

/-- The representative fixed-group identification discharges the whole outer branch. -/
theorem outer_fixedResidualThreeCoreData_of_representative
    (model : involutionAut.fixedSubgroup ≃* GorensteinWalter.PGL2 (ZMod 7))
    (a : MulAut Carrier) (ha : orderOf a = 2)
    (ho : a ∉ (MulAut.conj : Carrier →* MulAut Carrier).range) :
    MulAut.FixedResidualThreeCoreData a := by
  obtain ⟨e⟩ := outer_fixed_equiv_of_representative model a ha ho
  exact fixedResidualThreeCoreData_of_fixedEquiv a e

/-- Application to the exact intermediate automorphism subgroup in the three-core criterion. -/
theorem outer_threeCore_eq_bot_of_representative
    (model : involutionAut.fixedSubgroup ≃* GorensteinWalter.PGL2 (ZMod 7))
    (a : MulAut Carrier) (ha : orderOf a = 2)
    (ho : a ∉ (MulAut.conj : Carrier →* MulAut Carrier).range)
    (D : Subgroup (MulAut Carrier))
    (hD : D ≤ centralizer ({a} : Set (MulAut Carrier)))
    (hR : MulAut.fixedPerfectResidualInner a ≤ D) : pCore 3 D = ⊥ :=
  MulAut.threeCore_eq_bot_of_fixedResidualData a
    (outer_fixedResidualThreeCoreData_of_representative model a ha ho) D hD hR

end Sporadic.LeechRelated.J2.OuterInvolutionCores
