module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceStabilizers

/-!
# The unchanged pure-vector Sylow marking on the source module

The setwise stabilizer of V₁ is exactly the layer. Its intersection with
the given Sylow T fixes a unique line in V₁. Every nonzero vector on that
line has this intersection as its T-centralizer, and it is Sylow in the
full point stabilizer. This is the original H.9.1(3) marking; it is separate
from the nonsingular adapted-pair theorem.

Source: Aschbacher–Smith H.9.1(3), printed p.390.
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
variable {n : ℕ} {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup n M V)

/-- The original representation as linear equivalences. -/
def linearAction : M →* (V ≃ₗ[ZMod 2] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
    S.representation.asGroupHom

/-- The actual setwise normalizer of the source natural summand. -/
def naturalNormalizer : Subgroup M :=
  (BinaryLinear.parabolic S.natural).comap S.linearAction

/-- T₁=N_T(V₁), embedded in the source group. -/
def naturalSylowNormalizer (T : Sylow 2 M) : Subgroup M :=
  (T : Subgroup M) ⊓ S.naturalNormalizer

/-- C_(V₁)(H), as a subspace of the marked source summand. -/
noncomputable def naturalFixed (H : Subgroup M) : Submodule (ZMod 2) S.natural :=
  (S.fixed H).comap S.natural.subtype

/-- The source natural-summand normalizer is precisely its layer. -/
theorem naturalNormalizer_eq_layer : S.naturalNormalizer = componentLayer M := by
  let d := AutomorphismModel.coordinateAction S.degree
  let e := S.model.group
  let E := S.model.coordinates
  have hn (v : V) : v ∈ S.natural ↔ E v ∈ Pure.naturalSummand n :=
    (MarkedGeometry.mem_natural_iff_of_marking E S.naturalCoordinates S.model.natural_marking v).trans
      (Pure.mem_naturalSummand (E v)).symm
  ext g
  rw [← S.model.inner_iff g, ← Pure.summandNormalizer_eq_inner S.degree d]
  change (∀ v : V, S.representation g v ∈ S.natural ↔ v ∈ S.natural) ↔
    ∀ w : CoordinateSpace n, d.representation (e g) w ∈ Pure.naturalSummand n ↔
      w ∈ Pure.naturalSummand n
  constructor
  · intro hg w
    obtain ⟨v,rfl⟩ := E.surjective w
    rw [← S.model.equivariant, ← hn, ← hn]
    exact hg v
  · intro hg v
    rw [hn, hn, S.model.equivariant]
    exact hg (E v)

/-- The natural fixed space is transported using the original natural marking. -/
theorem naturalFixed_map (H : Subgroup M) :
    (S.naturalFixed H).map S.naturalCoordinates.toLinearMap =
      Pure.naturalFixedSpace (AutomorphismModel.coordinateAction S.degree)
        (H.map S.model.group.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩ a ⟨g,hg,rfl⟩
    have he := S.model.equivariant g (u : V)
    rw [S.model.natural_marking] at he
    exact he.symm.trans ((congrArg S.model.coordinates (hu ⟨g,hg⟩)).trans
      (S.model.natural_marking u))
  · intro hx
    refine ⟨S.naturalCoordinates.symm x, ?_, S.naturalCoordinates.apply_symm_apply x⟩
    intro g
    apply S.model.coordinates.injective
    change S.model.coordinates (S.representation g.val (S.naturalCoordinates.symm x : V)) =
      S.model.coordinates (S.naturalCoordinates.symm x : V)
    rw [S.model.equivariant, S.model.natural_marking, S.naturalCoordinates.apply_symm_apply]
    exact hx (S.model.group g) (Subgroup.mem_map_of_mem _ g.property)

/-- The actual image of a source Sylow under the constructed group model. -/
noncomputable def coordinateSylow (T : Sylow 2 M) :
    Sylow 2 (MulAut (LinearGroup n)) := by
  let := S.finite_group
  exact T.mapSurjective (f := S.model.group.toMonoidHom) S.model.group.surjective

@[simp] theorem coordinateSylow_coe (T : Sylow 2 M) :
    (S.coordinateSylow T : Subgroup _) = (T : Subgroup M).map S.model.group.toMonoidHom := by
  rfl

/-- The given Sylow and its actual natural-summand normalizer map together. -/
theorem naturalSylowNormalizer_map (T : Sylow 2 M) :
    (S.naturalSylowNormalizer T).map S.model.group.toMonoidHom =
      Pure.sylowSummandNormalizer (AutomorphismModel.coordinateAction S.degree)
        (S.coordinateSylow T) := by
  rw [naturalSylowNormalizer, S.naturalNormalizer_eq_layer,
    Subgroup.map_inf _ _ _ S.model.group.injective, S.layer_map,
    Pure.sylowSummandNormalizer, Pure.summandNormalizer_eq_inner S.degree, S.coordinateSylow_coe]

/-- The natural summand has a one-dimensional fixed space under T₁. -/
theorem naturalSylow_fixed_finrank (T : Sylow 2 M) :
    Module.finrank (ZMod 2) (S.naturalFixed (S.naturalSylowNormalizer T)) = 1 := by
  have he := (Submodule.equivMapOfInjective S.naturalCoordinates.toLinearMap
    S.naturalCoordinates.injective (S.naturalFixed (S.naturalSylowNormalizer T))).finrank_eq
  rw [S.naturalFixed_map, S.naturalSylowNormalizer_map] at he
  exact he.trans (Pure.sylow_fixed_finrank S.degree _ _)

/-- Every nonzero generator of that line gives the source Sylow centralizer. -/
theorem pure_sylow (T : Sylow 2 M) (u : S.natural) (hu : (u : V) ≠ 0)
    (hfix : u ∈ S.naturalFixed (S.naturalSylowNormalizer T)) :
    (T : Subgroup M) ⊓ S.stabilizer u = S.naturalSylowNormalizer T ∧
    ∃ P : Sylow 2 (S.stabilizer u),
      (P : Subgroup _).map (S.stabilizer u).subtype = S.naturalSylowNormalizer T := by
  let := S.finite_group
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : BinaryLinear.OuterCyclic.Space n →
      BinaryLinear.OuterCyclic.Space n)) DFunLike.coe_injective
  let d := AutomorphismModel.coordinateAction S.degree
  let e := S.model.group
  let E := S.model.coordinates
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let x := S.naturalCoordinates u
  have hx : x ≠ 0 := by
    intro h
    have hz : u = 0 := S.naturalCoordinates.injective (h.trans (map_zero _).symm)
    exact hu (congrArg Subtype.val hz)
  have hxf : x ∈ Pure.naturalFixedSpace d (Pure.sylowSummandNormalizer d T') := by
    have hm := Submodule.mem_map_of_mem (f := S.naturalCoordinates.toLinearMap) hfix
    rw [S.naturalFixed_map, S.naturalSylowNormalizer_map] at hm
    exact hm
  have hC : (T : Subgroup M) ⊓ S.stabilizer u = S.naturalSylowNormalizer T := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_inf _ _ _ e.injective, S.stabilizer_map,
      S.naturalSylowNormalizer_map, S.model.natural_marking]
    exact Pure.sylow_centralizer_eq S.degree d T' hx hxf
  refine ⟨hC, ?_⟩
  obtain ⟨P,hP⟩ := Pure.sylow_centralizer_isSylow S.degree d T' hx hxf
  have heq : fullStabilizer d (x,0) = representationStabilizer d.representation (E u) := by
    rw [S.model.natural_marking]; rfl
  let P' := P.mapSurjective (f := (MulEquiv.subgroupCongr heq).toMonoidHom)
    (MulEquiv.subgroupCongr heq).surjective
  have hP' : (P' : Subgroup (representationStabilizer d.representation (E u))).map
      (representationStabilizer d.representation (E u)).subtype =
      (T : Subgroup M).map e.toMonoidHom ⊓ representationStabilizer d.representation (E u) := by
    change ((P : Subgroup (fullStabilizer d (x,0))).map
      (MulEquiv.subgroupCongr heq).toMonoidHom).map _ = _
    rw [Subgroup.map_map]
    change (P : Subgroup (fullStabilizer d (x,0))).map (fullStabilizer d (x,0)).subtype = _
    rw [hP, ← Pure.sylow_centralizer_eq S.degree d T' hx hxf, ← heq]
    rfl
  obtain ⟨Q,hQ⟩ := Transport.sylow_stabilizer_pullback S.representation d.representation
    e E S.model.equivariant T u P' hP'
  exact ⟨Q, hQ.trans hC⟩

end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
