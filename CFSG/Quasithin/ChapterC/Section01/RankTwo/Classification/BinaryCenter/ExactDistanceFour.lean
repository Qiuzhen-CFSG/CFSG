module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SourceAssembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceFour
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual

/-!
# Exact distance-four sections for the original C.1.34 consumer

An actual `DoubleDualQuotient` has kernel U_alpha, and its commutator pairing
identifies the entire core center with U_alpha. Transport through the original
component inclusion identifies that center with the natural module and the
quotient by it with two dual modules, using one common quotient marking.
The dot-product intertwiner converts inverse-transpose coordinates into the
literal dual representation required by `HasSectionModel`.

The source constructor discharges the geometric moving-kernel assertion and
provides both sections under the original common facts and distance four.
The final theorem applies them to the third alternative of
`MSModuleAlternatives`. The enclosing C.1.34 classification retains the separate
radical-centralizer inequality; no quotient, kernel or action premise remains.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6), printed p.901 and
(4.6.12), pp.910--912; Aschbacher--Smith C.1.34(3), printed pp.136--137.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
open DistanceFour
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
  {h : Input κ L R} (s : InputSetup h)
  (common : CommonFacts s.reduction.radical s.source s.geometry)

omit [Finite J] in
private theorem sectionModel_of_onto
    {B V F : Type*} [Group B] [AddCommGroup V] [Field F] [Module F V]
    (A D E : Subgroup J) (actor : A →* B) (ρ : Representation F B V)
    (hED : E ≤ D) (hAD : A ≤ normalizer D) (hAE : A ≤ normalizer E)
    (f : D →* Multiplicative V) (hf : Function.Surjective f)
    (hk : f.ker = E.subgroupOf D)
    (ha : ∀ (a : A) (x y : D), (y : J) = a * (x : J) * (a : J)⁻¹ →
      (f y).toAdd = ρ (actor a) (f x).toAdd) :
    HasSectionModel A D E actor ρ := by
  let hn : (E.subgroupOf D).Normal := hk ▸ f.normal_ker
  let := hn
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact ⟨hED, hAD, hAE, hn, e, ha⟩

/-- Exact natural-center and doubled-dual sections with the same original marking. -/
theorem sectionModels_of_doubleDualQuotient
    (d : DoubleDualQuotient s.source common) :
    let e := h.quotientEquiv.trans common.natural.marking
    let Q := msQ L R
    let Z := (center Q).map Q.subtype
    let v := Representation.specialLinearNatural (k := ZMod 2) 3
    HasSectionModel L Z ⊥ (linearThreeActor e) v ∧
      HasSectionModel L Q Z (linearThreeActor e) (v.dual.prod v.dual) := by
  let r := s.reduction.radical
  let C := core r (alpha r)
  let D := commutatorCore L
  let ZD := (center D).map D.subtype
  let e := h.quotientEquiv.trans common.natural.marking
  have hQ : msQ L R = D := by
    have hc : (⊤ : Subgroup J).pCoreIn 2 = pCore 2 J := pCore_map_iso 2 topEquiv
    rw [msQ, h.sup_eq_top, hc]
  change HasSectionModel L ((center (msQ L R)).map (msQ L R).subtype) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := ZMod 2) 3) ∧ _
  rw [hQ]
  change HasSectionModel L ZD ⊥ (linearThreeActor e) BinaryLinearThree.W ∧
    HasSectionModel L D ZD (linearThreeActor e)
      (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual)
  let E : D ≃* C := h.intrinsicCoreEquiv.symm.trans s.intrinsicCoreEquiv
  have hE (l : L) (x y : D)
      (hy : (y : J) = l * (x : J) * (l : J)⁻¹) :
      (E y : FreeAmalgam r) =
        embedM r (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l) *
          (E x : FreeAmalgam r) *
          (embedM r (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l))⁻¹ := by
    have hy' : y = h.coreConjugate l x := by
      apply Subtype.ext
      rw [h.coreConjugate_val]
      exact hy
    have hi : h.intrinsicCoreEquiv.symm y =
        blockConjugate L l (h.intrinsicCoreEquiv.symm x) := by
      apply h.intrinsicCoreEquiv.injective
      rw [MulEquiv.apply_symm_apply, h.intrinsicCoreEquiv_conjugate,
        MulEquiv.apply_symm_apply, hy']
    change s.componentEmbedding (h.intrinsicCoreEquiv.symm y : L) = _
    rw [hi]
    change s.componentEmbedding (l * (h.intrinsicCoreEquiv.symm x : L) * l⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    rfl
  have hdk : d.quotient.ker = center C := by
    apply map_injective C.subtype_injective
    rw [d.kernel, map_subgroupOf_eq_of_le (U_le_core s.source s.geometry common),
      d.center_core]
  let eZ : ZD ≃* U r (alpha r) :=
    ((center D).equivMapOfInjective D.subtype D.subtype_injective).symm.trans
      ((centerCongr E).trans
        (((center C).equivMapOfInjective C.subtype C.subtype_injective).trans
          (MulEquiv.subgroupCongr d.center_core)))
  have heZ (x : ZD) : (eZ x : FreeAmalgam r) =
      E ⟨x, (map_subtype_le (center D)) x.property⟩ := by
    change (E (((center D).equivMapOfInjective D.subtype
      D.subtype_injective).symm x).val : FreeAmalgam r) = _
    apply congrArg (fun v : D => (E v : FreeAmalgam r))
    have hx := congrArg (fun t : ZD => (t : J))
      (((center D).equivMapOfInjective D.subtype D.subtype_injective).apply_symm_apply x)
    exact Subtype.ext hx
  let z := eZ.trans common.natural.equiv
  let := h.component_normal
  let : D.Normal := commutator_normal _ _
  have hLD : L ≤ normalizer D := by rw [normalizer_eq_top]; exact le_top
  have hLZ : L ≤ normalizer ZD := hLD.trans
    (normalizer_le_normalizer_characteristic_image D (center D))
  constructor
  · apply sectionModel_of_onto L ZD ⊥ (linearThreeActor e) BinaryLinearThree.W bot_le
      hLZ (by rw [normalizer_eq_top]; exact le_top) z.toMonoidHom z.surjective
    · rw [z.toMonoidHom.ker_eq_bot_iff.mpr z.injective, bot_subgroupOf]
    · intro l x y hy
      have he := common.natural.action
        (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l)
        (eZ x) (eZ y) (by rw [heZ, heZ]; exact hE l _ _ hy)
      have hm : s.source.projection
          (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l) =
          h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) := s.projection_component l
      rw [hm] at he
      exact he
  · let p := d.quotient.comp E.toMonoidHom
    have hpk : p.ker = ZD.subgroupOf D := by
      ext x
      change E x ∈ d.quotient.ker ↔ _
      rw [hdk]
      constructor
      · intro hx
        have hc : x ∈ center D := by
          have hc := (centerCongr E.symm ⟨E x, hx⟩).property
          change E.symm (E x) ∈ center D at hc
          simpa only [MulEquiv.symm_apply_apply] using hc
        exact mem_map_of_mem D.subtype hc
      · intro hx
        obtain ⟨y, hy, he⟩ := hx
        have hyx : y = x := Subtype.ext he
        subst y
        exact (centerCongr E ⟨x, hy⟩).property
    let f := BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv
    let f₂ := f.prodCongr f
    let q := f₂.toAddEquiv.toMultiplicative.toMonoidHom.comp p
    have hqk : q.ker = ZD.subgroupOf D :=
      (MonoidHom.ker_comp_of_injective p
        f₂.toAddEquiv.toMultiplicative.toMonoidHom f₂.injective).trans hpk
    apply sectionModel_of_onto L D ZD (linearThreeActor e)
      (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual)
      (map_subtype_le _) hLD hLZ q
      (f₂.surjective.comp (d.onto.comp E.surjective)) hqk
    intro l x y hy
    have he := d.action
      (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l)
      (E x) (E y) (hE l x y hy)
    have hm : s.source.projection
        (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l) =
        h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) := s.projection_component l
    rw [hm] at he
    change f₂ (p y).toAdd =
      (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual)
        (e (QuotientGroup.mk' (pCore 2 L) l)) (f₂ (p x).toAdd)
    change f₂ (d.quotient (E y)).toAdd = _
    rw [he]
    apply Prod.ext <;>
      exact LinearMap.congr_fun
        (BinaryLinearThree.AutomorphismAction.graphNaturalDual.isIntertwining' _) _

/-- Apply the source assembly to the literal third alternative of C.1.34.
The parent classification owns the separate radical-centralizer inequality;
this theorem retains it explicitly and retains the moving-kernel obligation. -/
theorem msModuleAlternatives_of_movingKernel
    (hb : s.geometry.b s.reduction.radical = 4)
    (hker : LargeBranch.RankOne.MovingKernelControl s.source common)
    (S : Subgroup J) (hineq : MSNotCentralizerCore L R S) :
    MSModuleAlternatives L R S 1 (ZMod 2)
      (h.quotientEquiv.trans common.natural.marking) := by
  obtain ⟨d⟩ := doubleDualQuotient_of_movingKernel s.source common hb hker
  obtain ⟨hcenter, hquotient⟩ := s.sectionModels_of_doubleDualQuotient common d
  exact Or.inr (Or.inr (Or.inl ⟨hcenter, hquotient, hineq⟩))

/-- Both literal C.1.34(3) sections follow from the distance-four source,
using the same original quotient marking for the natural module and its dual. -/
theorem sectionModels_of_distance_four (hb : s.geometry.b s.reduction.radical = 4) :
    let e := h.quotientEquiv.trans common.natural.marking
    let Q := msQ L R
    let Z := (center Q).map Q.subtype
    let v := Representation.specialLinearNatural (k := ZMod 2) 3
    HasSectionModel L Z ⊥ (linearThreeActor e) v ∧
      HasSectionModel L Q Z (linearThreeActor e) (v.dual.prod v.dual) := by
  obtain ⟨d⟩ := source_doubleDualQuotient s.source common hb
  exact s.sectionModels_of_doubleDualQuotient common d

/-- The original distance-four branch of the module alternatives, retaining
only the separate radical-centralizer inequality owned by the C.1.34 assembly. -/
theorem msModuleAlternatives_of_distance_four
    (hb : s.geometry.b s.reduction.radical = 4)
    (S : Subgroup J) (hineq : MSNotCentralizerCore L R S) :
    MSModuleAlternatives L R S 1 (ZMod 2)
      (h.quotientEquiv.trans common.natural.marking) := by
  obtain ⟨hcenter, hquotient⟩ := s.sectionModels_of_distance_four common hb
  exact Or.inr (Or.inr (Or.inl ⟨hcenter, hquotient, hineq⟩))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
