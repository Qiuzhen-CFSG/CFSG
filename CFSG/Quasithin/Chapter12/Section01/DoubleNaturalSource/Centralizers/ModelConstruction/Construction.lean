module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ModelConstruction.Layer
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.SourceModel

/-!
# Constructing the compatible H.9 model of the literal doubled orbit

Correct the abstract full-group marking by its discrepancy on the component
layer. An elementary transvection calculation shows that an invariant bilinear
form on the binary natural module is zero in dimension at least three. Applied
to the natural block of a graph operator, this forces its image into the dual
summand; invertibility and equal dimensions make that containment an equality.
Thus the actual quotient representation satisfies all H.9 source hypotheses.

Finally, inner invariance, nondegeneracy and the two singular summands identify
the H.9 form with evaluation in the original coordinates. Every marking in
`SourceModel` is constructed, including the supplied L/O₂(L) marking. No point
centralizer or weak-closure conclusion is used.

Source: Aschbacher--Smith, H.9 setup and H.9.1(1), printed pp.389--390;
the setup of 12.1, pp.787--788. Adapted-point consumers use the corrected
marking described in docs/quasithin-proof-basis.md.
-/

@[expose] public noncomputable section

open BinaryLinear BinaryLinear.OuterCyclic BinaryNaturalDual
open BinaryNaturalDual.ModelOrbits.AutomorphismModel

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ModelConstruction

private theorem invariant_bilinear_zero {n : ℕ} (hn : 3 ≤ n)
    (b : LinearMap.BilinForm (ZMod 2) (BinaryLinear.OuterCyclic.Space n))
    (hb : ∀ (g : LinearGroup n) x y, b (g x) (g y) = b x y) : b = 0 := by
  classical
  let e := Pi.basisFun (ZMod 2) (Fin n)
  apply e.ext
  intro i
  apply e.ext
  intro k
  obtain ⟨j, hji, hjk⟩ := Fin.exists_ne_and_ne_of_two_lt i k (by omega : 2 < n)
  let g := BinaryLinear.transvection (e k) (e.coord j) (by simp [hjk.symm])
  have hgi : g (e i) = e i := by simp [g, BinaryLinear.transvection, hji.symm]
  have hgj : g (e j) = e j + e k := by simp [g, BinaryLinear.transvection]
  have hh := hb g (e i) (e j)
  rw [hgi, hgj, map_add] at hh
  simpa using (add_left_cancel (hh.trans (add_zero _).symm))

private theorem graph_natural_fst_zero {n : ℕ} (hn : 3 ≤ n)
    (a : CoordinateSpace n →ₗ[ZMod 2] CoordinateSpace n)
    (ha : ∀ (g : LinearGroup n) v,
      a (naturalDualRepresentation g v) =
        naturalDualRepresentation (graphLinear n g) (a v))
    (x : BinaryLinear.OuterCyclic.Space n) : (a (x, 0)).1 = 0 := by
  let f : BinaryLinear.OuterCyclic.Space n →ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n :=
    (LinearMap.fst (ZMod 2) _ _).comp (a.comp (LinearMap.inl (ZMod 2) _ _))
  let b : LinearMap.BilinForm (ZMod 2) (BinaryLinear.OuterCyclic.Space n) :=
    (dotProductEquiv (ZMod 2) (Fin n)).toLinearMap.comp f
  have hb : b = 0 := invariant_bilinear_zero hn b (by
    intro g v w
    have he := congrArg Prod.fst (ha g (v, 0))
    simp only [naturalDualRepresentation_apply, map_zero] at he
    change dotProduct (f (g v)) (g w) = dotProduct (f v) w
    change (a (g v, 0)).1 = graphLinear n g (a (v, 0)).1 at he
    change dotProduct (a (g v, 0)).1 (g w) = dotProduct (a (v, 0)).1 w
    rw [he, graphLinear_dotProduct])
  apply (dotProductEquiv (ZMod 2) (Fin n)).injective
  change b x = _
  rw [hb, LinearMap.zero_apply, map_zero]

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ModelConstruction

open Subgroup Theory.GroupTheory BinaryNaturalDual BinaryNaturalDual.ModelOrbits
open BinaryNaturalDual.ModelOrbits.AutomorphismModel BinaryLinear.OuterCyclic
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

def sourceNatural : Submodule (ZMod 2) (Additive (componentOrbit V (T : Subgroup G))) :=
  (Submodule.fst (ZMod 2) (BinaryLinear.OuterCyclic.Space n)
    (Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))).comap B.linearCoordinates.toLinearMap

def sourceDual : Submodule (ZMod 2) (Additive (componentOrbit V (T : Subgroup G))) :=
  (Submodule.snd (ZMod 2) (BinaryLinear.OuterCyclic.Space n)
    (Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))).comap B.linearCoordinates.toLinearMap

noncomputable def sourceNaturalCoordinates : B.sourceNatural ≃ₗ[ZMod 2]
    BinaryLinear.OuterCyclic.Space n where
  toFun u := (B.linearCoordinates u).1
  invFun x := ⟨B.linearCoordinates.symm (x, 0), by
    change (B.linearCoordinates (B.linearCoordinates.symm (x, 0))).2 = 0
    simp⟩
  left_inv u := by
    apply Subtype.ext
    apply B.linearCoordinates.injective
    rw [B.linearCoordinates.apply_symm_apply]
    exact Prod.ext rfl u.property.symm
  right_inv x := by simp
  map_add' u v := by simp
  map_smul' a u := by simp

omit [Finite G] in
theorem source_complement : IsCompl B.sourceNatural B.sourceDual := by
  exact (Submodule.orderIsoMapComap B.linearCoordinates).symm.isCompl
    (show IsCompl (Submodule.fst (ZMod 2) (BinaryLinear.OuterCyclic.Space n)
        (Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)))
      (Submodule.snd (ZMod 2) (BinaryLinear.OuterCyclic.Space n)
        (Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))) from
      ⟨disjoint_iff.mpr (Submodule.fst_inf_snd ..), codisjoint_iff.mpr (Submodule.fst_sup_snd ..)⟩)

theorem sourceLayer_coordinates (q : componentLayer B.ActionQuotient)
    (w : Additive (componentOrbit V (T : Subgroup G))) :
    B.linearCoordinates (B.quotientRepresentation q w) =
      naturalDualRepresentation (B.sourceLayer q) (B.linearCoordinates w) := by
  have hq : (q : B.ActionQuotient) ∈ B.componentToActionQuotient.range := by
    rw [B.component_range_eq_layer]
    exact q.property
  obtain ⟨l, hl⟩ := hq
  have he : q = ⟨B.componentToActionQuotient l,
      B.component_range_eq_layer ▸ ⟨l, rfl⟩⟩ := Subtype.ext hl.symm
  rw [he, B.sourceLayer_apply]
  exact B.componentEmbedding_coordinates (QuotientGroup.mk' (pCore 2 L) l) w

theorem source_natural_action (l : componentLayer B.ActionQuotient)
    (x : BinaryLinear.OuterCyclic.Space n) :
    B.quotientRepresentation l (B.sourceNaturalCoordinates.symm x : Additive _) =
      (B.sourceNaturalCoordinates.symm (B.sourceLayer l x) : Additive _) := by
  apply B.linearCoordinates.injective
  rw [B.sourceLayer_coordinates]
  change naturalDualRepresentation (B.sourceLayer l)
    (B.linearCoordinates (B.linearCoordinates.symm (x, 0))) =
    B.linearCoordinates (B.linearCoordinates.symm (B.sourceLayer l x, 0))
  simp [naturalDualRepresentation_apply]

noncomputable def sourceDualCoordinates : B.sourceDual ≃ₗ[ZMod 2]
    Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n) where
  toFun u := (B.linearCoordinates u).2
  invFun f := ⟨B.linearCoordinates.symm (0, f), by
    change (B.linearCoordinates (B.linearCoordinates.symm (0, f))).1 = 0
    simp⟩
  left_inv u := by
    apply Subtype.ext
    apply B.linearCoordinates.injective
    rw [B.linearCoordinates.apply_symm_apply]
    exact Prod.ext u.property.symm rfl
  right_inv x := by simp
  map_add' u v := by simp
  map_smul' a u := by simp

noncomputable def sourceProjective : B.ActionQuotient ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup
    (Fin n) (ZMod 2)) :=
  B.full.trans (projectiveAutEquiv (by have := B.degree; omega : 0 < n)).symm

theorem source_outer : ∃ t : B.ActionQuotient,
    t ∉ componentLayer B.ActionQuotient ∧
      B.sourceNatural.map (B.quotientRepresentation t) = B.sourceDual := by
  obtain ⟨e, hel, hem⟩ := SourceComparison.exists_layerCompatible B.degree
    B.sourceProjective B.sourceLayer
  let u (g : LinearGroup n) : B.ActionQuotient := B.sourceLayer.symm g
  have heu (g : LinearGroup n) : e (u g) = MulAut.conj g := by
    rw [hel, B.sourceLayer.apply_symm_apply]
  have hu (g : LinearGroup n) (w : Additive (componentOrbit V (T : Subgroup G))) :
      B.linearCoordinates (B.quotientRepresentation (u g) w) =
        naturalDualRepresentation g (B.linearCoordinates w) := by
    rw [B.sourceLayer_coordinates, B.sourceLayer.apply_symm_apply]
  let t := e.symm (graphLinear n)
  have ht : t ∉ componentLayer B.ActionQuotient := by
    intro ht
    exact graph_not_inner B.degree (by simpa [t] using (hem _).mpr ht)
  have hrel (g : LinearGroup n) : t * u g = u (graphLinear n g) * t := by
    apply e.injective
    simp only [map_mul, heu, t, e.apply_symm_apply]
    ext x
    simp
  have hcomm (g : LinearGroup n) (w : Additive (componentOrbit V (T : Subgroup G))) :
      B.quotientRepresentation t (B.quotientRepresentation (u g) w) =
        B.quotientRepresentation (u (graphLinear n g)) (B.quotientRepresentation t w) := by
    change (B.quotientRepresentation t * B.quotientRepresentation (u g)) w =
      (B.quotientRepresentation (u (graphLinear n g)) * B.quotientRepresentation t) w
    rw [← map_mul, ← map_mul, hrel]
  let a : CoordinateSpace n →ₗ[ZMod 2] CoordinateSpace n :=
    B.linearCoordinates.toLinearMap.comp
      ((B.quotientRepresentation t).comp B.linearCoordinates.symm.toLinearMap)
  have ha (g : LinearGroup n) (v : CoordinateSpace n) :
      a (naturalDualRepresentation g v) = naturalDualRepresentation (graphLinear n g) (a v) := by
    have he : B.linearCoordinates.symm (naturalDualRepresentation g v) =
        B.quotientRepresentation (u g) (B.linearCoordinates.symm v) := by
      apply B.linearCoordinates.injective
      rw [B.linearCoordinates.apply_symm_apply, hu, B.linearCoordinates.apply_symm_apply]
    change B.linearCoordinates (B.quotientRepresentation t
      (B.linearCoordinates.symm (naturalDualRepresentation g v))) = _
    rw [he, hcomm, hu]
    rfl
  refine ⟨t, ht, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨w, hw, rfl⟩
    have he : B.linearCoordinates w = ((B.linearCoordinates w).1, 0) := Prod.ext rfl hw
    have hz := ModelConstruction.graph_natural_fst_zero
      (by have := B.degree; omega : 3 ≤ n) a ha (B.linearCoordinates w).1
    change (B.linearCoordinates (B.quotientRepresentation t w)).1 = 0
    change (B.linearCoordinates (B.quotientRepresentation t
      (B.linearCoordinates.symm ((B.linearCoordinates w).1, 0)))).1 = 0 at hz
    rwa [← he, B.linearCoordinates.symm_apply_apply] at hz
  · let f := LinearEquiv.ofBijective (B.quotientRepresentation t)
      (B.quotientRepresentation.apply_bijective t)
    have hf := f.finrank_map_eq B.sourceNatural
    have hfmap : f.toLinearMap = B.quotientRepresentation t := by
      apply LinearMap.ext
      intro w
      exact LinearEquiv.ofBijective_apply (B.quotientRepresentation t)
        (hf := B.quotientRepresentation.apply_bijective t) w
    rw [hfmap] at hf
    rw [hf, B.sourceNaturalCoordinates.finrank_eq, B.sourceDualCoordinates.finrank_eq]
    simp

noncomputable def constructedSetup : ChapterH.NaturalDual.SourceSetup n B.ActionQuotient
    (Additive (componentOrbit V (T : Subgroup G))) where
  degree := B.degree
  projective := B.sourceProjective
  layer := B.sourceLayer
  representation := B.quotientRepresentation
  natural := B.sourceNatural
  dual := B.sourceDual
  complement := B.source_complement
  naturalCoordinates := B.sourceNaturalCoordinates
  natural_action := B.source_natural_action
  outer := B.source_outer

theorem constructedSetup_quadratic : B.constructedSetup.quadratic = B.quadratic := by
  let S := B.constructedSetup
  let Q := S.quadratic.comp B.linearCoordinates.symm.toLinearMap
  have he : Q = BinaryNaturalDual.quadratic := by
    apply ModelOrbits.quadratic_unique
    · intro x
      apply S.quadratic_invariant.2.1
      change (B.linearCoordinates (B.linearCoordinates.symm (x, 0))).2 = 0
      simp
    · intro f
      let w : S.dual := ⟨B.linearCoordinates.symm (0, f), by
        change (B.linearCoordinates (B.linearCoordinates.symm (0, f))).1 = 0
        simp⟩
      change S.quadratic (w : Additive _) = 0
      rw [S.quadratic_apply, S.model.dual_marking, BinaryNaturalDual.quadratic_apply, map_zero]
    · intro g v
      have hh := B.sourceLayer_coordinates (B.sourceLayer.symm g) (B.linearCoordinates.symm v)
      rw [B.sourceLayer.apply_symm_apply, B.linearCoordinates.apply_symm_apply] at hh
      change S.quadratic (B.linearCoordinates.symm (naturalDualRepresentation g v)) = _
      rw [← hh, B.linearCoordinates.symm_apply_apply]
      exact S.quadratic_invariant.2.2 _ _
    · change (S.quadratic.comp B.linearCoordinates.symm.toLinearMap).polarBilin.Nondegenerate
      rw [QuadraticMap.polarBilin_comp]
      constructor
      · intro x hx
        apply B.linearCoordinates.symm.injective
        rw [map_zero]
        apply S.quadratic_invariant.1.1
        intro y
        obtain ⟨z, rfl⟩ := B.linearCoordinates.symm.surjective y
        exact hx z
      · intro x hx
        apply B.linearCoordinates.symm.injective
        rw [map_zero]
        apply S.quadratic_invariant.1.2
        intro y
        obtain ⟨z, rfl⟩ := B.linearCoordinates.symm.surjective y
        exact hx z
  ext w
  have hh := congrArg (fun q : QuadraticForm (ZMod 2) (CoordinateSpace n) =>
    q (B.linearCoordinates w)) he
  change S.quadratic w = BinaryNaturalDual.quadratic (B.linearCoordinates w)
  change S.quadratic (B.linearCoordinates.symm (B.linearCoordinates w)) =
    BinaryNaturalDual.quadratic (B.linearCoordinates w) at hh
  rwa [B.linearCoordinates.symm_apply_apply] at hh

theorem nonempty_sourceModel : Nonempty B.SourceModel :=
  ⟨{ setup := B.constructedSetup
     representation_eq := rfl
     component_layer := B.component_range_eq_layer
     layer_marking := B.sourceLayer_apply
     natural_marking := fun _ => Iff.rfl
     dual_marking := fun _ => Iff.rfl
     quadratic_eq := B.constructedSetup_quadratic }⟩

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
