module
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.InnerModel.Embedding
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.Extension
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.FieldTransport
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.Maximality

/-!
# The maximal outer S₇ model in PSU₃(5)

Coefficient transport carries every allowed field and its specified entrywise
actor to the concrete antidiagonal GF(25) model. A marked S₇ embedding there
has relatively maximal image by the A₇ argument, and the three explicit
even-conjugate triple transpositions supply literal PSU₃ conjugators.
Transport back preserves the actor's extension, its subgroup cover and each
conjugating element.

The explicit projective A₇ embedding and its marked symmetric extension
discharge the construction inputs in `outerModel`. The conditional assembly
theorems remain available. The final result proves `OuterModel` under exactly
its inherited simplicity hypothesis, for every permitted coefficient field
and specified entrywise actor.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public noncomputable section
open Subgroup Equiv
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five

private theorem map_innerExtension {S T : Type*} [Group S] [Group T]
    (e : S ≃* T) (a : MulAut S) :
    (MulAut.singleInnerExtension a).map (MulAut.congr e).toMonoidHom =
      MulAut.singleInnerExtension (MulAut.congr e a) := by
  have hi : ((MulAut.conj : S →* MulAut S).range).map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : T →* MulAut T).range := by
    ext b
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨e s, (MulAut.congr_conj e s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨MulAut.conj (e.symm s), ⟨e.symm s, rfl⟩, by
        change MulAut.congr e (MulAut.conj (e.symm s)) = MulAut.conj s
        rw [MulAut.congr_conj, e.apply_symm_apply]⟩
  rw [MulAut.singleInnerExtension, Subgroup.map_sup, hi, MonoidHom.map_closure, Set.image_singleton]
  rfl

/-- All field transport, relative maximality and literal inner conjugators
are supplied here. Only the marked concrete matrix embedding remains an input. -/
theorem outerModel_of_concreteEmbedding (hemb : Outer.ConcreteEmbedding) : OuterModel := by
  intro E _ _ J _ hcard hc hJ a _ha _ha2 hgraph
  obtain ⟨e, he⟩ := Outer.exists_marked_equiv J hcard hc hJ a hgraph
  let : IsSimpleGroup Outer.ConcreteGroup := e.symm.isSimpleGroup
  obtain ⟨f, hf, heven, hmark⟩ := hemb
  let d := MulAut.congr e.symm
  have hd : d Outer.concreteActor = a := by
    rw [← he]
    ext x
    simp [d, MulAut.congr]
  refine ⟨d.toMonoidHom.comp f, d.injective.comp hf, ?_,
    Outer.generators, Outer.generators_generate, ?_⟩
  · have hm := (apply_covBy_apply_iff d.mapSubgroup).mpr
      (Outer.marked_range_covBy f hf heven hmark)
    change f.range.map d.toMonoidHom ⋖
      (MulAut.singleInnerExtension Outer.concreteActor).map d.toMonoidHom at hm
    rw [map_innerExtension, hd] at hm
    rwa [MonoidHom.range_comp]
  · intro i
    obtain ⟨s, hs⟩ := Outer.marked_generators Outer.concreteActor f heven hmark i
    refine ⟨e.symm s, ?_⟩
    have hh := congrArg d hs
    have hdc : d (MulAut.conj s) = MulAut.conj (e.symm s) := MulAut.congr_conj e.symm s
    simpa only [map_mul, map_inv, hdc, hd, MonoidHom.comp_apply,
      MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] using hh

/-- The independent A₇ matrix embedding and its marked symmetric extension
discharge the two remaining construction inputs. -/
theorem outerModel_of_alternating_embedding_and_extension
    (hinner : ∀ [IsSimpleGroup StandardGroup],
      ∃ j : alternatingGroup (Fin 7) →* StandardGroup, Function.Injective j)
    (hext : Outer.ConcreteExtension) : OuterModel := by
  apply outerModel_of_concreteEmbedding
  intro hsimple
  obtain ⟨e⟩ := Outer.exists_concrete_equiv_standard
  let : IsSimpleGroup StandardGroup := e.symm.isSimpleGroup
  obtain ⟨j, hj⟩ := hinner
  exact hext ⟨e.symm.toMonoidHom.comp j, e.symm.injective.comp hj⟩

/-- Three literal inner conjugates of the specified entrywise involution
generate an embedded S₇ maximal in that involution's own inner extension.
The actual matrix constructions discharge all extra assembly premises. -/
theorem outerModel : OuterModel :=
  outerModel_of_alternating_embedding_and_extension
    (by
      intro _
      exact exists_alternatingSeven_embedding)
    Outer.concrete_extension

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five
