module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFiveActors.Transport
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups

/-!
# The given Sylow and its source three-space radical

Pull back the complete flag of the given Sylow's layer intersection through
its original natural marking. Its three-space stabilizer and geometric
unipotent radical are literal source subgroups, and the radical is the
relative two-core. Coordinate classification supplies actual source
conjugators for all rank-six and rank-five actors.

Source: Aschbacher–Smith H.9.2(3), printed pp.390–391.
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceFiveActors
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup 5 M V)

/-- The original marked natural coordinates of a subspace of V₁. -/
def coordinateSpace (U : Submodule (ZMod 2) S.natural) :=
  U.map S.naturalCoordinates.toLinearMap

/-- The faithful source-layer embedding, inverse to the given layer marking. -/
def layerEmbedding : BinaryLinear.OuterCyclic.LinearGroup 5 →* M :=
  (componentLayer M).subtype.comp S.layer.symm.toMonoidHom

theorem layerEmbedding_injective : Function.Injective (layerEmbedding S) :=
  (componentLayer M).subtype_injective.comp S.layer.symm.injective

theorem layerEmbedding_model (g : BinaryLinear.OuterCyclic.LinearGroup 5) :
    S.model.group (layerEmbedding S g) = MulAut.conj g := by
  change S.model.group (S.layer.symm g) = _
  rw [S.model.on_layer, S.layer.apply_symm_apply]

/-- The parabolic inside the source layer, at the original marked subspace. -/
def parabolic (U : Submodule (ZMod 2) S.natural) : Subgroup M :=
  (BinaryLinear.parabolic (coordinateSpace S U)).map (layerEmbedding S)

/-- Its actual geometric unipotent radical, acting trivially on U and V₁/U. -/
def radical (U : Submodule (ZMod 2) S.natural) : Subgroup M :=
  (BinaryLinear.radical (coordinateSpace S U)).map (layerEmbedding S)

theorem radical_map (U : Submodule (ZMod 2) S.natural) :
    (radical S U).map S.model.group.toMonoidHom =
      BinaryNaturalDual.FiveActors.radicalActor (coordinateSpace S U) := by
  rw [radical, Subgroup.map_map]
  unfold BinaryNaturalDual.FiveActors.radicalActor
  congr 1
  exact MonoidHom.ext (layerEmbedding_model S)

/-- The radical is the relative two-core of the actual source parabolic. -/
theorem radical_eq_twoCore (U : Submodule (ZMod 2) S.natural) :
    radical S U = (pCore 2 (parabolic S U)).map (parabolic S U).subtype := by
  rw [← Subgroup.pCoreIn, parabolic, ← Subgroup.map_pCoreIn_of_injective
    2 _ (layerEmbedding S) (layerEmbedding_injective S)]
  rw [Subgroup.pCoreIn, BinaryLinear.SmallParabolicLevi.map_twoCore_eq_radical]
  rfl

theorem coordinateSpace_finrank (U : Submodule (ZMod 2) S.natural) :
    Module.finrank (ZMod 2) (coordinateSpace S U) = Module.finrank (ZMod 2) U :=
  (S.naturalCoordinates.submoduleMap U).finrank_eq.symm

/-- The natural layer action in the original marking. -/
noncomputable def naturalAction (g : componentLayer M) : S.natural ≃ₗ[ZMod 2] S.natural :=
  S.naturalCoordinates.trans ((S.layer g).trans S.naturalCoordinates.symm)

@[simp] theorem naturalAction_apply (g : componentLayer M) (w : S.natural) :
    (naturalAction S g w : V) = S.representation g w := by
  simpa only [naturalAction, LinearEquiv.trans_apply, S.naturalCoordinates.symm_apply_apply] using
    (S.natural_action g (S.naturalCoordinates w)).symm

/-- The parabolic is literally the setwise stabilizer of U inside L. -/
theorem mem_parabolic_iff (U : Submodule (ZMod 2) S.natural) (g : M) :
    g ∈ parabolic S U ↔ ∃ hg : g ∈ componentLayer M,
      ∀ w : S.natural, naturalAction S ⟨g,hg⟩ w ∈ U ↔ w ∈ U := by
  have hm (x : BinaryLinear.OuterCyclic.Space 5) :
      x ∈ coordinateSpace S U ↔ S.naturalCoordinates.symm x ∈ U := by
    exact Submodule.mem_map_equiv U (e := S.naturalCoordinates)
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(S.layer.symm a).property, fun w => ?_⟩
    have hh := ha (S.naturalCoordinates w)
    rw [hm, hm, S.naturalCoordinates.symm_apply_apply] at hh
    simpa only [naturalAction, LinearEquiv.trans_apply, layerEmbedding, MonoidHom.comp_apply,
      MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, Subgroup.coe_subtype, S.layer.apply_symm_apply] using hh
  · rintro ⟨hg, h⟩
    refine ⟨S.layer ⟨g,hg⟩, ?_, ?_⟩
    · intro x
      rw [hm, hm]
      simpa only [naturalAction, LinearEquiv.trans_apply,
        S.naturalCoordinates.apply_symm_apply] using h (S.naturalCoordinates.symm x)
    · exact congrArg Subtype.val (S.layer.symm_apply_apply ⟨g,hg⟩)

/-- The geometric radical condition on the original natural summand. -/
theorem mem_radical_iff (U : Submodule (ZMod 2) S.natural) (g : M) :
    g ∈ radical S U ↔ ∃ hg : g ∈ componentLayer M,
      (∀ w ∈ U, naturalAction S ⟨g,hg⟩ w = w) ∧
      ∀ w : S.natural, naturalAction S ⟨g,hg⟩ w - w ∈ U := by
  have hm (x : BinaryLinear.OuterCyclic.Space 5) :
      x ∈ coordinateSpace S U ↔ S.naturalCoordinates.symm x ∈ U :=
    Submodule.mem_map_equiv U (e := S.naturalCoordinates)
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(S.layer.symm a).property, ?_, ?_⟩
    · intro w hw
      have hh := congrArg S.naturalCoordinates.symm
        (ha.1 (S.naturalCoordinates w) (Submodule.mem_map_of_mem hw))
      simpa only [naturalAction, LinearEquiv.trans_apply, layerEmbedding, MonoidHom.comp_apply,
        MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, Subgroup.coe_subtype, S.layer.apply_symm_apply,
        S.naturalCoordinates.symm_apply_apply] using hh
    · intro w
      have hh := (hm _).mp (ha.2 (S.naturalCoordinates w))
      simpa only [naturalAction, LinearEquiv.trans_apply, layerEmbedding, MonoidHom.comp_apply,
        MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, Subgroup.coe_subtype, S.layer.apply_symm_apply,
        map_sub, S.naturalCoordinates.symm_apply_apply] using hh
  · rintro ⟨hg, hfix, hmove⟩
    refine ⟨S.layer ⟨g,hg⟩, ⟨?_, ?_⟩,
      congrArg Subtype.val (S.layer.symm_apply_apply ⟨g,hg⟩)⟩
    · intro x hx
      have hh := congrArg S.naturalCoordinates (hfix (S.naturalCoordinates.symm x) ((hm x).mp hx))
      simpa only [naturalAction, LinearEquiv.trans_apply,
        S.naturalCoordinates.apply_symm_apply] using hh
    · intro x
      rw [hm]
      simpa only [naturalAction, LinearEquiv.trans_apply, map_sub,
        S.naturalCoordinates.apply_symm_apply] using hmove (S.naturalCoordinates.symm x)

/-- A three-space preserved by T₁ is constructed for the GIVEN source Sylow. -/
theorem exists_sylow_threeSpace (T : Sylow 2 M) :
    ∃ U : Submodule (ZMod 2) S.natural,
      Module.finrank (ZMod 2) U = 3 ∧ S.naturalSylowNormalizer T ≤ parabolic S U := by
  obtain ⟨P,hP⟩ := BinaryNaturalDual.VectorStabilizers.Pure.exists_linear_sylow S.degree
    (AutomorphismModel.coordinateAction S.degree) (S.coordinateSylow T)
  obtain ⟨b,hb⟩ := BinaryLinear.FiveFlagGeometry.sylow_eq_flagStabilizer P
  let W := BinaryLinear.FiveFlagGeometry.flagSpace b 2
  let U := W.comap S.naturalCoordinates.toLinearMap
  have hU : coordinateSpace S U = W :=
    Submodule.map_comap_eq_of_surjective S.naturalCoordinates.surjective W
  refine ⟨U, ?_, ?_⟩
  · rw [← coordinateSpace_finrank S U, hU]
    exact BinaryLinear.FiveFlagGeometry.finrank_flagSpace b 2
  · intro g hg
    have hg' := Subgroup.mem_map_of_mem (f := S.model.group.toMonoidHom) hg
    rw [S.naturalSylowNormalizer_map, ← hP] at hg'
    obtain ⟨a, ha, he⟩ := hg'
    refine ⟨a, ?_, S.model.group.injective ?_⟩
    · rw [hU]
      rw [hb] at ha
      exact (BinaryLinear.FiveFlagGeometry.mem_flagStabilizer_iff b Set.univ a).mp ha
        2 (Set.mem_univ _)
    · exact (layerEmbedding_model S a).trans he
/-- The source radical is elementary abelian of order 64. -/
theorem radical_elementary_card (U : Submodule (ZMod 2) S.natural)
    (hU : Module.finrank (ZMod 2) U = 3) :
    IsElementaryAbelian 2 (radical S U) ∧ Nat.card (radical S U) = 64 := by
  let e := ((radical S U).equivMapOfInjective _ S.model.group.injective).trans
    (MulEquiv.subgroupCongr (radical_map S U))
  let := BinaryNaturalDual.FiveActors.radicalActor_isElementaryAbelian (coordinateSpace S U)
  exact ⟨IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective,
    (Nat.card_congr e.toEquiv).trans (BinaryNaturalDual.FiveActors.radicalActor_card _
      ((coordinateSpace_finrank S U).trans hU))⟩

private theorem conjugate_eq_iff (A B : Subgroup M) :
    (∃ a : M, A.map (MulAut.conj a).toMonoidHom = B) ↔
      ∃ a : BinaryNaturalDual.FiveActors.M,
        (A.map S.model.group.toMonoidHom).map (MulAut.conj a).toMonoidHom =
          B.map S.model.group.toMonoidHom := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨S.model.group a, (conjugate_map S A a).symm.trans (congrArg
      (Subgroup.map S.model.group.toMonoidHom) ha)⟩
  · rintro ⟨a,ha⟩
    refine ⟨S.model.group.symm a, ?_⟩
    apply Subgroup.map_injective (f := S.model.group.toMonoidHom) S.model.group.injective
    rw [conjugate_map, S.model.group.apply_symm_apply]
    exact ha

/-- All source E₆₄ actors, with actual source conjugators. -/
theorem elementary_card_64_iff (U : Submodule (ZMod 2) S.natural)
    (hU : Module.finrank (ZMod 2) U = 3) (A : Subgroup M) :
    (IsElementaryAbelian 2 A ∧ Nat.card A = 64) ↔
      ∃ a : M, A.map (MulAut.conj a).toMonoidHom = radical S U := by
  rw [conjugate_eq_iff S A, radical_map, ←
    BinaryNaturalDual.FiveActors.elementary_card_64_iff_conjugate_radical _ _
      ((coordinateSpace_finrank S U).trans hU)]
  let e := A.equivMapOfInjective S.model.group.toMonoidHom S.model.group.injective
  constructor
  · rintro ⟨hA,hcard⟩
    let := hA
    exact ⟨IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective,
      (Nat.card_congr e.toEquiv).symm.trans hcard⟩
  · rintro ⟨hA,hcard⟩
    let := hA
    exact ⟨IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective,
      (Nat.card_congr e.toEquiv).trans hcard⟩

/-- The equivalent rank-six formulation of the exhaustive classification. -/
theorem rank_six_iff (U : Submodule (ZMod 2) S.natural)
    (hU : Module.finrank (ZMod 2) U = 3) (A : Subgroup M) [IsElementaryAbelian 2 A] :
    primeRank 2 A = 6 ↔ ∃ a : M, A.map (MulAut.conj a).toMonoidHom = radical S U := by
  let e := A.equivMapOfInjective S.model.group.toMonoidHom S.model.group.injective
  let : IsElementaryAbelian 2 (A.map S.model.group.toMonoidHom) :=
    IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  rw [conjugate_eq_iff S A, radical_map, ← rank_map S A]
  exact BinaryNaturalDual.FiveActors.rank_six_iff_conjugate_radical _ _
    ((coordinateSpace_finrank S U).trans hU)

/-- Every rank-five actor is precisely a conjugate of a hyperplane of this radical. -/
theorem rank_five_iff (U : Submodule (ZMod 2) S.natural)
    (hU : Module.finrank (ZMod 2) U = 3) (A : Subgroup M) [IsElementaryAbelian 2 A] :
    primeRank 2 A = 5 ↔ ∃ a : M,
      A.map (MulAut.conj a).toMonoidHom ≤ radical S U ∧
      (A.map (MulAut.conj a).toMonoidHom).relIndex (radical S U) = 2 := by
  let e := A.equivMapOfInjective S.model.group.toMonoidHom S.model.group.injective
  let : IsElementaryAbelian 2 (A.map S.model.group.toMonoidHom) :=
    IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  have hh := BinaryNaturalDual.FiveActors.rank_five_iff_conjugate_hyperplane
    (A.map S.model.group.toMonoidHom) (coordinateSpace S U)
    ((coordinateSpace_finrank S U).trans hU)
  rw [rank_map S A] at hh
  rw [hh]
  constructor
  · rintro ⟨a,ha,hi⟩
    obtain ⟨b,rfl⟩ := S.model.group.surjective a
    refine ⟨b, ?_, ?_⟩
    · apply (Subgroup.map_le_map_iff_of_injective (f := S.model.group.toMonoidHom)
        S.model.group.injective).mp
      rwa [conjugate_map, radical_map]
    · rw [← Subgroup.relIndex_map_map_of_injective (f := S.model.group.toMonoidHom)
        _ _ S.model.group.injective,
        conjugate_map, radical_map]
      exact hi
  · rintro ⟨a,ha,hi⟩
    refine ⟨S.model.group a, ?_, ?_⟩
    · rw [← conjugate_map, ← radical_map]
      exact Subgroup.map_mono ha
    · rw [← conjugate_map, ← radical_map,
        Subgroup.relIndex_map_map_of_injective (f := S.model.group.toMonoidHom)
        _ _ S.model.group.injective]
      exact hi

end CFSG.Quasithin.ChapterH.NaturalDual.SourceFiveActors
