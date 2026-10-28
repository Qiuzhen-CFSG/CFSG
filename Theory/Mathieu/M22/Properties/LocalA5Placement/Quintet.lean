module

public import Theory.Mathieu.M22.ChapterHLocalClassification
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Geometry
public import Theory.GroupTheory.Commutator.PerfectSmallIndex
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Literal quintet placement of perfect local subgroups in M22

The common fixed set of the inner quintet translations is exactly the
source tetrad. A perfect subgroup normalizing these translations acts
trivially on the tetrad, since its four-point permutation image is solvable.
The tetrad's cocode class recovers the entire sextet, so the subgroup lies
in the literal natural actor. Equality follows when its order is 960.

The argument retains the native embeddings and intrinsic two-core; it does
not assume conjugacy of abstract E16:A5 carriers or classify all normalizers.

Source: Aschbacher--Smith A.3.12(12), A.3.14(6), pp.47--49, and H.14.3,
p.397. Hexacode coordinates reuse the licensed ATLAS imports documented in
ChapterHLocalClassification.Quintet.Natural.Coordinates.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace Sporadic.Mathieu.M22LocalA5Placement
open M22ChapterH M22ChapterH.Quintet M22ChapterH.Sextet Atlas.Codes
theorem natural_actor_card : Nat.card M22ChapterH.Quintet.naturalActor = 960 := by
  rw [← Nat.card_congr M22ChapterH.Quintet.naturalActorEquiv.toEquiv]
  exact Atlas.Codes.tetradPointAffine_card _

open Atlas.Codes M22ChapterH.Quintet M22ChapterH.Sextet in
theorem inner_translation_fixed_iff (i : HexIndex) (k : Fin 4) :
    (∀ a : innerTranslationGroup,
      a.val.val.val (naturalPointCoordinates (i,k)) = naturalPointCoordinates (i,k)) ↔
      i = naturalIndex := by
  constructor
  · intro hf
    by_contra hi
    obtain ⟨w, hw⟩ := hexZeroCoordinate_other_surjective naturalIndex i (Ne.symm hi) 1
    have hh := hf (naturalTranslation (Multiplicative.ofAdd w))
    change (naturalTranslation (Multiplicative.ofAdd w)).val.val.val
      (naturalPointCoordinates (i,k)) = naturalPointCoordinates (i,k) at hh
    rw [naturalTranslation_coe, sourceTranslation_points] at hh
    have hp := congrArg Prod.snd (naturalPointCoordinates.injective hh)
    have hp' := congrArg rowLabel hp
    change rowLabel (rowLabel.symm (rowLabel k + w.val.val i)) = rowLabel k at hp'
    rw [rowLabel.apply_symm_apply, hw] at hp'
    exact one_ne_zero (add_left_cancel (hp'.trans (add_zero _).symm))
  · rintro rfl a
    obtain ⟨w, rfl⟩ := naturalTranslation_bijective.2 a
    rw [naturalTranslation_coe, sourceTranslation_points]
    have hw : w.toAdd.val.val naturalIndex = 0 := w.toAdd.property
    change naturalPointCoordinates
      (naturalIndex, rowLabel.symm (rowLabel k + w.toAdd.val.val naturalIndex)) = _
    rw [hw, add_zero, rowLabel.symm_apply_apply]


private theorem fixed_iff_mem_tetrad (x : Fin 24) :
    (∀ a : innerTranslationGroup, a.val.val.val x = x) ↔ x ∈ m22SourceTetrad 0 := by
  obtain ⟨⟨i,k⟩, rfl⟩ := naturalPointCoordinates.surjective x
  rw [inner_translation_fixed_iff, ← naturalActor_tetrad]
  constructor
  · rintro rfl
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · intro hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
    exact (congrArg Prod.fst (naturalPointCoordinates.injective hj)).symm

private theorem normalizer_preserves_tetrad (g : MathieuCode.m22PairStabilizer)
    (hg : g ∈ normalizer (innerTranslationGroup : Set MathieuCode.m22PairStabilizer)) :
    g.val ∈ MulAction.stabilizer M24 (m22SourceTetrad 0) := by
  apply MulAction.mem_stabilizer_finset'.mpr
  intro x hx
  apply (fixed_iff_mem_tetrad _).mp
  intro a
  have hmem : g⁻¹ * a.val * g ∈ innerTranslationGroup := by
    simpa only [inv_inv] using
      ((mem_normalizer_iff.mp ((normalizer _).inv_mem hg) a.val).mp a.property)
  have hh := (fixed_iff_mem_tetrad x).mpr hx ⟨g⁻¹ * a.val * g,hmem⟩
  have he := congrArg (fun y : Fin 24 => g.val • y) hh
  change g.val • ((g.val⁻¹ * a.val.val * g.val) • x) = g.val • x at he
  change a.val.val • (g.val • x) = g.val • x
  simpa only [mul_smul, smul_inv_smul] using he

private theorem tetrad_stabilizer_le_sextet :
    MulAction.stabilizer M24 (m22SourceTetrad 0) ≤ sextetStabilizer m22SourceSextet := by
  rw [← sextetVector_stabilizer]
  intro g hg
  change cocodeRepresentation g (sextetVector m22SourceSextet) = _
  rw [sextetVector_eq m22SourceSextet m22SourceTetrad_mem, evenSetVector_equivariant]
  have he : g • m22SourceTetrad 0 = m22SourceTetrad 0 := hg
  simp only [he]

private theorem perfect_normalizer_fixes_tetrad
    (P : Subgroup MathieuCode.m22PairStabilizer) [Group.IsPerfect P]
    (hP : P ≤ normalizer (innerTranslationGroup : Set MathieuCode.m22PairStabilizer)) :
    ∀ g ∈ P, ∀ x ∈ m22SourceTetrad 0, g.val.val x = x := by
  classical
  let D := m22SourceTetrad 0
  let e : D ≃ Fin 4 := Fintype.equivFinOfCardEq (by
    simpa only [Fintype.card_coe] using m22SourceSextet.tetrad D m22SourceTetrad_mem)
  let f : P →* Equiv.Perm D := {
    toFun g := g.val.val.val.subtypePerm
      (MulAction.mem_stabilizer_finset.mp (normalizer_preserves_tetrad g.val (hP g.property)))
    map_one' := by ext a; rfl
    map_mul' g h := by ext a; rfl }
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm D) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective e.toEmbedding)
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  intro g hg x hx
  have hf : f ⟨g,hg⟩ = 1 := congrArg Subtype.val
    (Subsingleton.elim (f.rangeRestrict ⟨g,hg⟩) 1)
  exact congrArg Subtype.val (Equiv.congr_fun hf (⟨x,hx⟩ : D))

/-- Perfect normalizers of the native quintet translations fix the distinguished
source tetrad pointwise and lie in its literal natural actor. -/
theorem perfect_normalizer_le_naturalActor
    (P : Subgroup MathieuCode.m22PairStabilizer) [Group.IsPerfect P]
    (hP : P ≤ normalizer (innerTranslationGroup : Set MathieuCode.m22PairStabilizer)) :
    P ≤ naturalActor.map M22Quintet.Q.subtype := by
  intro g hg
  have hD := normalizer_preserves_tetrad g (hP hg)
  have hQ : g ∈ M22Quintet.Q := tetrad_stabilizer_le_sextet hD
  refine ⟨⟨g,hQ⟩, (mem_naturalActor_iff _).mpr ?_, rfl⟩
  intro k
  apply perfect_normalizer_fixes_tetrad P hP g hg
  rw [← naturalActor_tetrad]
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

/-- The actual quintet-core image of a perfect order-960 subgroup is the
marked natural actor, without assuming an abstract embedding classification. -/
theorem quintet_core_placement (B : Subgroup M22) [Group.IsPerfect B]
    (hcore : B.pCoreIn 2 = m22InnerQuintetKernel m22SourceSextet)
    (hcard : Nat.card B = 960) :
    B.map m22ToPairStabilizer = naturalActor.map M22Quintet.Q.subtype := by
  have himage : (B.pCoreIn 2).map m22ToPairStabilizer = innerTranslationGroup := by
    rw [hcore, M22ChapterH.inner_quintet_map_pair]
    exact innerTranslationGroup_eq_intersection.symm
  have hBN : B ≤ normalizer (B.pCoreIn 2 : Set M22) :=
    B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hN : B.map m22ToPairStabilizer ≤
      normalizer (innerTranslationGroup : Set MathieuCode.m22PairStabilizer) := by
    rw [← himage]
    exact (map_mono hBN).trans (le_normalizer_map m22ToPairStabilizer)
  let : Group.IsPerfect (B.map m22ToPairStabilizer) := Group.IsPerfect.map _
  have hinj : Function.Injective m22ToPairStabilizer :=
    fun _ _ h => m22Embedding_injective (congrArg Subtype.val h)
  apply eq_of_le_of_card_ge (perfect_normalizer_le_naturalActor _ hN)
  rw [card_map_of_injective M22Quintet.Q.subtype_injective,
    card_map_of_injective hinj, natural_actor_card, hcard]

end Sporadic.Mathieu.M22LocalA5Placement
