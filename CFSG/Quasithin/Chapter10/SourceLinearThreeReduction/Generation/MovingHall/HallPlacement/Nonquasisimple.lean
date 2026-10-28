module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.ComparisonQuotient
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.SingleFive
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.RadicalQuotient
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape
public import Theory.SpecificGroups.PSL2.BinaryCoreSections

/-!
# The original nonquasisimple comparison has an A₅ quotient

The genuine A.3.6 conclusion identifies the containing component modulo its
solvable radical with PSL₂ over a prime field. The original comparison maps
there with solvable kernel. Its binary SL₂ two-core quotient is therefore A₅,
so the checked normal-section theorem gives the literal Hall three-group
bound. This route discharges the nonquasisimple source branch without a
supplement-normalization premise or a containing action-kernel identification.

Source: Aschbacher–Smith 10.2.3, printed pp.745–746; A.3.6, pp.43–45.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped MatrixGroups


namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02 Chapter1 Chapter1.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} {ctx : Context D H B}

/-- The actual radical map forces an A₅ quotient of the original single comparison. -/
theorem ComparisonConfiguration.single_a5_of_nonquasisimple
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H)
    (hnq : ¬ IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent))
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e) :
    Nonempty ((c.component ⧸ pCore 2 c.component) ≃* alternatingGroup (Fin 5)) := by
  have hI := (c.local_components D).2
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hc := proposition_1_2_1_four_earlier_conclusion h36
    (uniqueness_local_quotient_sqtk D.simpleQTKE hI.2.2) hI.1
  obtain ⟨p,hp,hp3,E,_,_,hE,⟨a⟩⟩ :=
    radical_quotient_pslTwo_of_a36_image c.overcomponent (radicalLocalQuotientEquiv hI) hc hnq
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype E := Fintype.ofFinite E
  let ef : E ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hE,ZMod.card])
  let eq := a.trans (Atlas.fieldEquivPSL 2 ef)
  let i : c.component →* c.overcomponent := {
    toFun := fun x => ⟨x.val,c.component_le (mem_map_of_mem H.subtype x.property)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : c.overcomponent => (x : G)) h))
  let q := QuotientGroup.mk' (solvableRadical c.overcomponent)
  let f := eq.toMonoidHom.comp (q.comp i)
  let j : f.ker →* solvableRadical c.overcomponent := {
    toFun := fun x => ⟨i x.val, (QuotientGroup.eq_one_iff _).mp
      (eq.injective (by
        change eq (q (i x.val)) = eq 1
        rw [map_one]
        exact x.property))⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (hi (congrArg Subtype.val h))
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective (f := j) hj
  let := c.component_isCComponent.perfect
  obtain ⟨E₀,hdegree,⟨r⟩⟩ := c.single_linear_quotient D hsingle n hn hF e mark
  exact Theory.PSL2.binary_core_section_of_solvable_kernel hp3 hdegree E₀.card_eq r f

/-- The original nonquasisimple containing component gives the required literal Hall bound. -/
theorem ComparisonConfiguration.hall_three_of_single_nonquasisimple
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H)
    (hnq : ¬ IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent))
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e) :
    IsPGroup 3 B :=
  c.hall_isThreeGroup_of_single_a5 D hsingle
    (c.single_a5_of_nonquasisimple D hsingle hnq n hn hF e mark).some

end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
