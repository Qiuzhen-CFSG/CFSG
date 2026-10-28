module

public import Theory.SpecificGroups.PSp4Three.Simplicity
public import Theory.SpecificGroups.PSp4Three.SectionReduction
public import Theory.SpecificGroups.PSL4Three.SectionReduction
public import CFSG.Quasithin.MainConverse.AlternatingSections.SmallDegrees

/-!
# Simple sections of the concrete PSp₄(3)

The whole-group case uses the proved simplicity of the actual symplectic
matrix group modulo its center. The catalogue comparison is definitional.
For proper subgroups, the conditional assembly below separates solvability
of reducible inverse images from exhaustive coverage of irreducible
subgroups by overgroups with alternating normal layers. Every resulting
simple section is identified by an actual multiplicative equivalence.

The two proper-subgroup inputs remain explicit. Thus these implications
are not the unconditional K-group theorem requested by the PSL₄(3) owner.
The source theorem stays unfinished until both inputs are constructed.

Source: Aschbacher–Smith, Theorem 0.1.2(4), condition K, printed pp.4 and
482 of `refs/quasithin.pdf`.
-/

namespace CFSG.Quasithin.MainConverse.LinearFour

open CFSG.KnownSimple

/-- The lower-layer and catalogue carriers are the same concrete central quotient. -/
public def psp4_three_catalogueEquiv :
    Matrix.PSL4Three.PSp ≃* ClassicalGroup.PSp 2 (ZMod 3) := MulEquiv.refl _

/-- No simplicity hypothesis on PSL₄(3) is used for this model fact. -/
public theorem psp4_three_isSimpleGroup : IsSimpleGroup Matrix.PSL4Three.PSp :=
  Matrix.PSp4Three.isSimpleGroup

private theorem simple_surjection_injective {H S : Type*} [Group H] [Group S]
    [IsSimpleGroup H] [Nontrivial S] (f : H →* S) (hf : Function.Surjective f) :
    Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨x, rfl⟩ := hf s
    exact hs (show f x = 1 from show x ∈ f.ker by rw [h]; trivial)

/-- Every nontrivial image of the whole concrete group is isomorphic to it. -/
public theorem psp4_three_surjection_equiv {S : Type*} [Group S] [Nontrivial S]
    (f : Matrix.PSL4Three.PSp →* S) (hf : Function.Surjective f) :
    Nonempty (S ≃* Matrix.PSL4Three.PSp) := by
  let := psp4_three_isSimpleGroup
  exact ⟨(MulEquiv.ofBijective f ⟨simple_surjection_injective f hf, hf⟩).symm⟩

private theorem alternatingSix_simpleSection {S : Type*} [Group S] [IsSimpleGroup S]
    (U : Subgroup (alternatingGroup (Fin 6))) (f : U →* S)
    (hf : Function.Surjective f) :
    IsPrimeCyclicCarrier S ∨ Nonempty (S ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  by_cases hU : U = ⊤
  · subst U
    let eU : (⊤ : Subgroup (alternatingGroup (Fin 6))) ≃*
        alternatingGroup (Fin 6) := Subgroup.topEquiv
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup (⊤ : Subgroup (alternatingGroup (Fin 6))) := eU.isSimpleGroup
    exact Or.inr (Or.inr
      ⟨(MulEquiv.ofBijective f ⟨simple_surjection_injective f hf, hf⟩).symm.trans eU⟩)
  · let eU : (⊤ : Subgroup U) ≃* U := Subgroup.topEquiv
    rcases alternatingSix_proper_simple_section (MulEquiv.refl _) U hU ⊤
      (f.comp eU.toMonoidHom) (hf.comp eU.surjective) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

private theorem layers_simpleSection {H S : Type*} [Group H] [Group S] [IsSimpleGroup S]
    (hH : Matrix.PSp4Three.HasAlternatingLayers H)
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsPrimeCyclicCarrier S ∨ Nonempty (S ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  rcases hH with h | h
  · let := h
    let : Group.IsSolvable S := Group.isSolvable_of_surjective hf
    exact Or.inl (primeCyclic_of_solvable_simple S)
  · rcases h.simpleSection U f hf with hs | ⟨V, g, hg⟩
    · let := hs
      exact Or.inl (primeCyclic_of_solvable_simple S)
    · exact alternatingSix_simpleSection V g hg

/-- Conditional section assembly. Both subgroup-structure premises need intrinsic proofs. -/
public theorem psp4_three_simpleSection_of_subgroup_structure
    (hreducible : ∀ U : Subgroup Matrix.PSL4Three.PSp,
      Matrix.PSp4Three.HasInvariantSubspace U → Group.IsSolvable U)
    (hirreducible : ∀ U : Subgroup Matrix.PSL4Three.PSp, U ≠ ⊤ →
      ¬ Matrix.PSp4Three.HasInvariantSubspace U →
      ∃ M : Subgroup Matrix.PSL4Three.PSp, U ≤ M ∧ Matrix.PSp4Three.HasAlternatingLayers M)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (U : Subgroup Matrix.PSL4Three.PSp) (f : U →* S) (hf : Function.Surjective f) :
    IsPrimeCyclicCarrier S ∨ Nonempty (S ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (S ≃* alternatingGroup (Fin 6)) ∨ Nonempty (S ≃* Matrix.PSL4Three.PSp) := by
  by_cases hU : U = ⊤
  · subst U
    let eU : (⊤ : Subgroup Matrix.PSL4Three.PSp) ≃* Matrix.PSL4Three.PSp := Subgroup.topEquiv
    exact Or.inr (Or.inr (Or.inr (psp4_three_surjection_equiv
      (f.comp eU.symm.toMonoidHom) (hf.comp eU.symm.surjective))))
  · by_cases hred : Matrix.PSp4Three.HasInvariantSubspace U
    · let := hreducible U hred
      let : Group.IsSolvable S := Group.isSolvable_of_surjective hf
      exact Or.inl (primeCyclic_of_solvable_simple S)
    · obtain ⟨M, hUM, hM⟩ := hirreducible U hU hred
      let j := Subgroup.inclusion hUM
      let e := MonoidHom.ofInjective (Subgroup.inclusion_injective hUM)
      rcases layers_simpleSection hM j.range (f.comp e.symm.toMonoidHom)
        (hf.comp e.symm.surjective) with hc | ha | ha
      · exact Or.inl hc
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))

/-- Conditional K-group assembly; the source task must still discharge both inputs. -/
public theorem psp4_three_isKGroup_of_subgroup_structure
    (hreducible : ∀ U : Subgroup Matrix.PSL4Three.PSp,
      Matrix.PSp4Three.HasInvariantSubspace U → Group.IsSolvable U)
    (hirreducible : ∀ U : Subgroup Matrix.PSL4Three.PSp, U ≠ ⊤ →
      ¬ Matrix.PSp4Three.HasInvariantSubspace U →
      ∃ M : Subgroup Matrix.PSL4Three.PSp, U ≤ M ∧ Matrix.PSp4Three.HasAlternatingLayers M) :
    IsKGroup IsConstructedCarrier Matrix.PSL4Three.PSp := by
  intro S _ hS U f hf
  let := hS
  rcases psp4_three_simpleSection_of_subgroup_structure hreducible hirreducible U f hf with
    hc | ha | ha | hsp
  · exact .cyclic hc
  · exact .alternating 5 (by decide) ha
  · exact .alternating 6 (by decide) ha
  · obtain ⟨e⟩ := hsp
    exact .classical (.symplectic 2 3
      ⟨Nat.prime_three.isPrimePow, by decide, by omega, by decide⟩
      ⟨ZMod 3, inferInstance, inferInstance, by simp, ⟨e.trans psp4_three_catalogueEquiv⟩⟩)

end CFSG.Quasithin.MainConverse.LinearFour
