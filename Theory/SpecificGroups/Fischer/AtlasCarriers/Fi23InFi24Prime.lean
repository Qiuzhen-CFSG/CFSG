module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.WordSetup

/-!+# Lifting the exact Fi₂₃ carrier into Fi₂₄′

This module assembles two concrete inputs: a relabeling that intertwines the
exact Fi₂₃ generators with the two explicit words from `WordSetup`, and
faithfulness of their generated subgroup on its orbit. Conjugation by the
relabeling sends the Fi₂₃ carrier into the restriction image. Faithfulness
inverts restriction on that image, giving an embedding in Fi₂₄′.

Both inputs remain to be constructed. The conditional theorem below is not
an unconditional Fi₂₃ embedding or a proved point-stabilizer identification.
Final assembly must discharge both premises.

Source: GLS3, Table 5.3v and its explanatory paragraph in
`refs/KGroup/GLS3/Chapter5(sec3-).tex`, line 1053; ATLAS representations
`F23G1-p31671B0` and `F24G1-p306936B0`.
-/

public section

namespace Sporadic.Fischer.Fi24Prime

open Fi23Lift

/-- A checked generator comparison and faithful restriction give the required
embedding between the exact permutation carriers. Both inputs are explicit. -/
theorem exists_fi23_embedding_of_generator_comparison
    (j : Fin 31671 ≃ Letters)
    (ha : action aLift = j.permCongrHom Fi23.generatorA)
    (hb : action bLift = j.permCongrHom Fi23.generatorB)
    (hf : Function.Injective action) :
    ∃ e : Fi23.Carrier →* Carrier, Function.Injective e := by
  let c := j.permCongrHom.toMonoidHom
  have hc : Fi23.generated ≤ action.range.comap c := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with rfl | rfl
    · exact ⟨aLift, ha⟩
    · exact ⟨bLift, hb⟩
  let f : Fi23.Carrier →* action.range :=
    (c.comp Fi23.inclusion).codRestrict _ (fun g => hc g.property)
  have hfi : Function.Injective f := by
    intro g h he
    apply Fi23.inclusion_injective
    apply j.permCongrHom.injective
    exact congrArg (fun p : action.range => p.val) he
  let E := MonoidHom.ofInjective hf
  exact ⟨liftedGroup.subtype.comp (E.symm.toMonoidHom.comp f),
    Subtype.val_injective.comp (E.symm.injective.comp hfi)⟩

end Sporadic.Fischer.Fi24Prime
