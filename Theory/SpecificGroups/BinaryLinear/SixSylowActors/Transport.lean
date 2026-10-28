module

public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Defs
public import Theory.GroupAction.ModelConjugation.InnerImage

/-!
# Transporting six-letter Sylow actor configurations

A group equivalence carries the embedded A₆, its fixed Sylow subgroup,
and the entire elementary actor group together. Pointwise fixers and inner
automorphisms are transported by the same conjugation equivalence. Thus a
model's two-central actor theorem applies to every isomorphic carrier,
without replacing the given action by an unrelated automorphism.

Source: the intrinsic calculation in Aschbacher–Smith, combined manuscript
(1 March 2004), E.6.23, printed p.254 (PDF p.265).
-/

public section

open Subgroup MulAction
namespace BinaryLinear.SixSylowActors
variable {Y Z : Type*} [Group Y] [Group Z]

/-- Transport both the actor subgroup and its pointwise fixer by the same equivalence. -/
theorem map_fixer (e : Y ≃* Z) (E : Subgroup (MulAut Y)) (D : Subgroup Y) :
    (E ⊓ fixingSubgroup (MulAut Y) (D : Set Y)).map (MulAut.congr e).toMonoidHom =
      E.map (MulAut.congr e).toMonoidHom ⊓
        fixingSubgroup (MulAut Z) (D.map e.toMonoidHom : Set Z) := by
  ext a
  constructor
  · rintro ⟨b, ⟨hb, hf⟩, rfl⟩
    refine ⟨mem_map_of_mem _ hb, (mem_fixingSubgroup_iff _).mpr ?_⟩
    rintro x ⟨y, hy, rfl⟩
    change e (b (e.symm (e y))) = e y
    rw [e.symm_apply_apply]
    exact congrArg e ((mem_fixingSubgroup_iff _).mp hf y hy)
  · rintro ⟨⟨b, hb, rfl⟩, hf⟩
    refine ⟨b, ⟨hb, (mem_fixingSubgroup_iff _).mpr ?_⟩, rfl⟩
    intro y hy
    apply e.injective
    have he := (mem_fixingSubgroup_iff _).mp hf (e y) (mem_map_of_mem e.toMonoidHom hy)
    change e (b (e.symm (e y))) = e y at he
    change e (b y) = e y
    simpa only [e.symm_apply_apply] using he

/-- Actual group equivalences preserve every clause of the intrinsic configuration. -/
theorem Configuration.map [Finite Y] {E : Subgroup (MulAut Y)} {D : Subgroup Y}
    (c : Configuration E D) (e : Y ≃* Z) :
    Configuration (E.map (MulAut.congr e).toMonoidHom) (D.map e.toMonoidHom) := by
  let _ := c.elementary
  let d := D.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨IsElementaryAbelian.map _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_map_of_injective (MulAut.congr e).injective]
    exact c.card
  · obtain ⟨f⟩ := c.six
    exact ⟨d.symm.trans f⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact Theory.GroupAction.ModelConjugation.stable_map_congr e D a (c.stable a ha)
  · rw [← map_fixer, card_map_of_injective (MulAut.congr e).injective]
    exact c.fixer_card
  · intro hi
    apply c.fixer_outer
    intro a ha
    have ham : (MulAut.congr e) a ∈
        E.map (MulAut.congr e).toMonoidHom ⊓
          fixingSubgroup (MulAut Z) (D.map e.toMonoidHom : Set Z) := by
      rw [← map_fixer]
      exact mem_map_of_mem _ ha
    obtain ⟨z, hz⟩ := hi ham
    refine ⟨e.symm z, (MulAut.congr e).injective ?_⟩
    rw [MulAut.congr_conj, e.apply_symm_apply]
    exact hz
  · obtain ⟨Q, hQ⟩ := c.sylow
    refine ⟨Q.mapSurjective (f := d.toMonoidHom) d.surjective, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨x, hx, rfl⟩
    change e (a (e.symm (e (x : Y)))) = e x
    rw [e.symm_apply_apply, hQ a ha x hx]

/-- A concrete model theorem retains the supplied action on an isomorphic group. -/
theorem HasTwoCentralActor.of_equiv [Finite Z] (e : Y ≃* Z) (h : HasTwoCentralActor Z) :
    HasTwoCentralActor Y := by
  let _ : Finite Y := Finite.of_equiv Z e.symm.toEquiv
  intro E D c
  obtain ⟨a, ha, ha1, P, hP⟩ := h _ _ (c.map e)
  obtain ⟨b, hb, rfl⟩ := ha
  refine ⟨b, hb, ?_, P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective, ?_⟩
  · intro hb1
    exact ha1 (by rw [hb1, map_one])
  · rintro _ ⟨x, hx, rfl⟩
    apply e.injective
    have he := hP x hx
    change e (b (e.symm x)) = x at he
    change e (b (e.symm x)) = e (e.symm x)
    rw [e.apply_symm_apply]
    exact he

end BinaryLinear.SixSylowActors
