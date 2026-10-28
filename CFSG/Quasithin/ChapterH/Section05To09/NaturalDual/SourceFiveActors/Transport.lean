module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceSylowMarking
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.FiveActors
public import Theory.GroupTheory.SylowKernelCore

/-!
# Source actor transport for H.9.2

The constructed marked model transports conjugation, relative centralizers,
rank and actual displacement spans. These identities are used to assemble
H.9.2 on the original group and module (Aschbacher–Smith, pp.390–391).
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceFiveActors
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup 5 M V)

/-- The literal layer centralizer of a source element. -/
def centralizer (_S : SourceSetup 5 M V) (t : M) : Subgroup M := componentLayer M ⊓ Subgroup.centralizer {t}

/-- The actual commutator of a source subspace with a source actor. -/
noncomputable def commutator (W : Submodule (ZMod 2) V) (A : Subgroup M) :
    Submodule (ZMod 2) V :=
  Representation.BinaryOffender.subspaceCommutator S.representation W A

theorem commutator_map (W : Submodule (ZMod 2) V) (A : Subgroup M) :
    (commutator S W A).map S.model.coordinates.toLinearMap =
      Representation.BinaryOffender.subspaceCommutator
        (AutomorphismModel.coordinateAction S.degree).representation
        (W.map S.model.coordinates.toLinearMap) (A.map S.model.group.toMonoidHom) := by
  rw [commutator, Representation.BinaryOffender.subspaceCommutator,
    Representation.BinaryOffender.subspaceCommutator, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨a, ha, w, hw, rfl⟩, rfl⟩
    refine ⟨S.model.group a, Subgroup.mem_map_of_mem _ ha,
      S.model.coordinates w, Submodule.mem_map_of_mem hw, ?_⟩
    change S.model.coordinates (S.representation a w - w) = _
    rw [map_sub, S.model.equivariant]
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨S.representation a w - w, ⟨a, ha, w, hw, rfl⟩,
      by
        change S.model.coordinates (S.representation a w - w) = _
        rw [map_sub, S.model.equivariant]
        rfl⟩

theorem centralizer_map (t : M) :
    (centralizer S t).map S.model.group.toMonoidHom =
      BinaryNaturalDual.FiveActors.innerCentralizer (S.model.group t) := by
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(S.model.inner_iff g).mpr hg.1, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change S.model.group g * S.model.group t = S.model.group t * S.model.group g
    simpa only [map_mul] using congrArg S.model.group
      (Subgroup.mem_centralizer_singleton_iff.mp hg.2)
  · intro ha
    refine ⟨S.model.group.symm a, ⟨(S.model.inner_iff _).mp ?_, ?_⟩,
      S.model.group.apply_symm_apply a⟩
    · simpa using ha.1
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply S.model.group.injective
      simpa only [map_mul, S.model.group.apply_symm_apply] using
        Subgroup.mem_centralizer_singleton_iff.mp ha.2

/-- The relative centralizer comparison is the restriction of the actual group model. -/
noncomputable def centralizerEquiv (t : M) :
    centralizer S t ≃* BinaryNaturalDual.FiveActors.innerCentralizer (S.model.group t) :=
  ((centralizer S t).equivMapOfInjective _ S.model.group.injective).trans
    (MulEquiv.subgroupCongr (centralizer_map S t))

@[simp] theorem centralizerEquiv_apply (t : M) (a : centralizer S t) :
    (centralizerEquiv S t a).val = S.model.group a := rfl

theorem conjugate_map (A : Subgroup M) (a : M) :
    (A.map (MulAut.conj a).toMonoidHom).map S.model.group.toMonoidHom =
      (A.map S.model.group.toMonoidHom).map (MulAut.conj (S.model.group a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp

theorem rank_map (A : Subgroup M) :
    primeRank 2 (A.map S.model.group.toMonoidHom) = primeRank 2 A := by
  let := S.finite_group
  exact (primeRank_equiv 2 (A.equivMapOfInjective _ S.model.group.injective)).symm

include S in
/-- H.9.2(2) on the original source group. -/
theorem high_rank_inner (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hA : 5 ≤ primeRank 2 A) : A ≤ componentLayer M := by
  let := S.finite_group
  let A' := A.map S.model.group.toMonoidHom
  let e := A.equivMapOfInjective S.model.group.toMonoidHom S.model.group.injective
  let : IsElementaryAbelian 2 A' :=
    IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  apply (Subgroup.map_le_map_iff_of_injective (f := S.model.group.toMonoidHom)
    S.model.group.injective).mp
  rw [S.layer_map]
  exact BinaryNaturalDual.FiveActors.ModuleGeometry.high_rank_inner A'
    (by simpa only [A', rank_map] using hA)

/-- H.9.2(5), with the source corank convention and its actual Chapter E core. -/
theorem dualGeneratedCore_eq_top (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hA : 5 ≤ primeRank 2 A) :
    ChapterE.dualGeneratedCore
      (multiplicativeAction (S.representation.comp A.subtype)) 3 = ⊤ := by
  let := S.finite_group
  let A' := A.map S.model.group.toMonoidHom
  let e := A.equivMapOfInjective S.model.group.toMonoidHom S.model.group.injective
  let : IsElementaryAbelian 2 A' :=
    IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  have hc : generatedCore (S.representation.comp A.subtype) 3 = ⊤ := by
    apply Submodule.map_injective_of_injective S.model.coordinates.injective
    rw [S.core_map]
    rw [BinaryNaturalDual.FiveActors.generatedCore_eq_top_of_high_rank
      (AutomorphismModel.coordinateAction S.degree) A'
      (by simpa only [A', rank_map] using hA)]
    simp
  rw [← generatedCore_subgroup, hc, OrderIso.map_top]

end CFSG.Quasithin.ChapterH.NaturalDual.SourceFiveActors
