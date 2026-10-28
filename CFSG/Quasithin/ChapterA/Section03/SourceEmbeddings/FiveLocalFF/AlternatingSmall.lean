module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SmallAlternating
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.BinaryLinear.Source
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Small finite rows in the full-Sylow FF local-section sieve

A proper local C-component cannot occur in an alternating-five or
alternating-six actor, or in a perfect central cover of alternating six.
Every proper full-Sylow overgroup is solvable in these groups; adjoining
the Sylow to the local component must therefore give the whole actor,
where quasisimplicity forces equality. This argument retains any two-core
of the smaller component and needs no section marking for these rows.
The actual derived binary symplectic group is transported to alternating
six. Alternating eight is excluded by its literal PSL₄(2) equivalence and
the completed higher binary linear local-section sieve.

The final consumers preserve the literal image of the original subgroup
under a map with solvable kernel. Only the alternating-eight consumer
needs the original A₅ marking and its restricted two-group kernel.

Source: Aschbacher–Smith A.3.12, printed pp.47–48, and the finite B.4.2
rows used in 10.2.9, printed pp.751–752 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.AlternatingSmall
variable {G : Type*} [Group G] [Finite G]

private theorem local_eq_top_of_solvable_overgroups [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (h : SolvableSylowOvergroups G) : B = ⊤ := by
  have ht : (⊤ : Subgroup G).IsCComponent :=
    (show IsComponent G ⊤ from ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  exact eq_of_solvable_sylow_overgroups S hB ht le_top
    (SolvableSylowOvergroups.of_equiv topEquiv h)

/-- A proper full-Sylow local component cannot lie in an alternating-five actor. -/
theorem not_proper_five [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) (e : G ≃* alternatingGroup (Fin 5)) : False := by
  exact hproper (local_eq_top_of_solvable_overgroups S B hB
    (SolvableSylowOvergroups.of_equiv e (fun _ P _ hP =>
      alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP)))

/-- A proper full-Sylow local component cannot lie in an alternating-six actor. -/
theorem not_proper_six [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) (e : G ≃* alternatingGroup (Fin 6)) : False := by
  exact hproper (local_eq_top_of_solvable_overgroups S B hB
    (SolvableSylowOvergroups.of_equiv e AlternatingSix.ProperSylowOvergroups.isSolvable))

/-- A perfect central cover of A₆ has no proper full-Sylow local component.
The cubic-center hypothesis of the actual triple-six FF row is unnecessary. -/
theorem not_proper_central_six [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) (e : (G ⧸ center G) ≃* alternatingGroup (Fin 6)) : False := by
  exact hproper (local_eq_top_of_solvable_overgroups S B hB
    (SolvableSylowOvergroups.of_central_quotient (QuotientGroup.mk' (center G))
      (QuotientGroup.mk'_surjective _) (by simp)
      (SolvableSylowOvergroups.of_equiv e AlternatingSix.ProperSylowOvergroups.isSolvable)))

private noncomputable def binary_symplectic_derived_equiv :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃* alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

/-- The actual commutator subgroup of Sp₄(2) is excluded, rather than the
full symplectic group being silently identified with A₆. -/
theorem not_proper_symplectic_two_derived [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤)
    (e : G ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) : False :=
  not_proper_six S B hB hproper (e.trans binary_symplectic_derived_equiv)

/-- The binary PSL₄ exclusion applies to the literal alternating-eight
carrier and retains the smaller subgroup's two-core. -/
theorem not_section_eight
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (e : G ≃* alternatingGroup (Fin 8)) : False := by
  apply BinaryLinear.not_section_binary_linear S B hB eB (Or.inl rfl)
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩

/-- The literal reduced-action image excludes the three small alternating
rows. Solvability of the full kernel transports the full-Sylow local condition;
no two-group condition on that full kernel is required. -/
theorem small_alternating_image_excluded {M : Type*} [Group M] [Finite M]
    [IsQuasisimple M]
    (f : G →* M) (hf : Function.Surjective f) (hks : Group.IsSolvable f.ker)
    (S : Sylow 2 G) (L : Subgroup G) (hL : L ∈ localCComponents S)
    (hproper : L.map f ≠ ⊤)
    (hm : Nonempty (M ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (M ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((M ⧸ center M) ≃* alternatingGroup (Fin 6))) : False := by
  let := hks
  have hB : L.map f ∈ localCComponents (S.mapSurjective hf) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hL f
  rcases hm with e | e | e
  · exact not_proper_five (S.mapSurjective hf) _ hB hproper e.some
  · exact not_proper_six (S.mapSurjective hf) _ hB hproper e.some
  · exact not_proper_central_six (S.mapSurjective hf) _ hB hproper e.some

/-- The literal reduced-action image excludes A₈, transporting the original
A₅ marking through the restricted two-kernel and preserving its two-core. -/
theorem eight_image_excluded {M : Type*} [Group M] [Finite M]
    (f : G →* M) (hf : Function.Surjective f) (hks : Group.IsSolvable f.ker)
    (S : Sylow 2 G) (L : Subgroup G) (hL : L ∈ localCComponents S)
    (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (eM : M ≃* alternatingGroup (Fin 8)) : False := by
  let := hks
  let e := ((f.subgroupMap L).pCoreQuotientEquiv
    (f.subgroupMap_surjective L) hk).symm.trans eL
  exact not_section_eight (S.mapSurjective hf) (L.map f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hL f) e eM

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.AlternatingSmall
