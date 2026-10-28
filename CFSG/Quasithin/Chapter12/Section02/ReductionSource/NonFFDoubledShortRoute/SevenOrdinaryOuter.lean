module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddG2
public import Theory.SpecificGroups.PSL3Two.Parabolics.CosetGeometry

/-!
# No outer A7 section in the actual Theorem B component catalogue

The faithful seven-point Fano action embeds SL3(2) in A7. A supplied outer
section onto A7 therefore pulls back to an outer SL3(2) section, which the
already proved complete Theorem B obstruction excludes. The component's
central cover and full outer automorphism group are retained.
Source: Aschbacher--Smith 4.4.10--11, printed p.621, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource

private theorem exists_fano_alternating_embedding :
    ∃ j : BinaryLinearThree.Group →* alternatingGroup (Fin 7), Function.Injective j := by
  let e := Fintype.equivFinOfCardEq Matrix.PSL3Two.Fano.card_point
  let f := (Equiv.permCongrHom e).toMonoidHom.comp
    (Matrix.PSL3Two.Fano.pointAction.comp Matrix.PSL3Two.equiv.toMonoidHom)
  have hf : Function.Injective f := (Equiv.permCongrHom e).injective.comp
    (Matrix.PSL3Two.Fano.pointAction_faithful.comp Matrix.PSL3Two.equiv.injective)
  let : Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)
  have hAlt : f.range ≤ alternatingGroup (Fin 7) := by
    let s := Equiv.Perm.sign.comp f
    let : Group.IsPerfect s.range := Group.IsPerfect.range s
    rintro _ ⟨g,rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mpr
      (congrArg Subtype.val (Subsingleton.elim (⟨s g,⟨g,rfl⟩⟩ : s.range) 1))
  let j := f.codRestrict (alternatingGroup (Fin 7)) (fun g => hAlt ⟨g,rfl⟩)
  exact ⟨j,fun x y he => hf (congrArg Subtype.val he)⟩

/-- The actual quasisimple Theorem B component admits no outer A7 section. -/
theorem no_theoremB_seven_outer_section
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (U : Subgroup (MulAut.Outer K)) (f : U →* alternatingGroup (Fin 7))
    (hf : Function.Surjective f) : False := by
  obtain ⟨j,hj⟩ := exists_fano_alternating_embedding
  let e := MonoidHom.ofInjective hj
  let P := j.range.comap f
  let q : P →* BinaryLinearThree.Group :=
    e.symm.toMonoidHom.comp (f.subgroupComap j.range)
  have hq : Function.Surjective q := e.symm.surjective.comp
    (f.subgroupComap_surjective_of_surjective j.range hf)
  let a := P.equivMapOfInjective U.subtype U.subtype_injective
  exact (DoubledBinaryOddG2.no_theoremB_outer_section hm)
    ⟨P.map U.subtype,q.comp a.symm.toMonoidHom,hq.comp a.symm.surjective⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
