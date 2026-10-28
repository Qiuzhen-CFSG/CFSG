module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.Sylow

/-!
# Intrinsic Sylow-three centralizers in the source four-cover

One actual outer cubic bounds its fixed subgroup in the cover Sylow by the
natural module. A Sylow containing that cubic supplements the two-core;
the source fixed-vector identity then kills its entire centralizer. Sylow
conjugacy transports this conclusion to every Sylow three-subgroup of Y.
The literal centralizer-bound consumer therefore needs no chosen complement.

The component residual is also identified with the projective Borel in the
original marking: over the four-element field, cubic elements generate
both the unipotent radical and the torus. This retains the marked quotient
needed for the separate graph and field coset comparison.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136,
combined manuscript (1 March 2004), with the preceding Borel theta identity.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel SylowNormalizer
variable {G : Type*} [Group G] [Finite G]

private theorem centralizer_all_sylows_of_one
    (Y R : Subgroup G) (hYR : Y ≤ normalizer (R : Set G))
    (X₀ : Sylow 3 Y)
    (hzero : R ⊓ centralizer (((X₀ : Subgroup Y).map Y.subtype) : Set G) = ⊥)
    (X : Sylow 3 Y) :
    R ⊓ centralizer (((X : Subgroup Y).map Y.subtype) : Set G) = ⊥ := by
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y X X₀
  let f := (MulAut.conj (y : G)).toMonoidHom
  have hX : ((X : Subgroup Y).map Y.subtype).map f =
      (X₀ : Subgroup Y).map Y.subtype := by
    rw [← hy]
    change ((X : Subgroup Y).map Y.subtype).map f =
      ((X : Subgroup Y).map (MulAut.conj y).toMonoidHom).map Y.subtype
    rw [map_map, map_map]
    rfl
  apply le_bot_iff.mp
  intro x hx
  have hRf : f x ∈ R := (mem_normalizer_iff.mp (hYR y.property) x).mp hx.1
  have hCf : f x ∈ centralizer (((X₀ : Subgroup Y).map Y.subtype) : Set G) := by
    rw [← hX]
    exact map_centralizer_le_centralizer_image _ f (mem_map_of_mem f hx.2)
  have he : f x = 1 := hzero.le ⟨hRf, hCf⟩
  exact (MulAut.conj (y : G)).injective (he.trans (map_one f).symm)

/-- Every actual Sylow three-subgroup acts fixed-point-freely on the cover Sylow. -/
theorem source_sylow_centralizer_eq_bot {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (X : Sylow 3 d.Y) :
    (d.S ⊓ L) ⊓ centralizer (((X : Subgroup d.Y).map d.Y.subtype) : Set G) = ⊥ := by
  let R := d.Y.pCoreIn 2
  let D := planeResidual d.M d.Y r.cover.borel.W₂
  have hRY : R ≤ d.Y := pCoreIn_le 2 d.Y
  have hYR : d.Y ≤ normalizer (R : Set G) :=
    d.Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image d.Y (pCore 2 d.Y))
  have hcore : R.subgroupOf d.Y = pCore 2 d.Y :=
    comap_map_eq_self_of_injective d.Y.subtype_injective _
  let : (R.subgroupOf d.Y).Normal := by rw [hcore]; infer_instance
  have hq : IsPGroup 3 (d.Y ⧸ R.subgroupOf d.Y) := by
    apply IsPGroup.of_card (n := 2)
    rw [hcore, r.cover.quotient_card]
    norm_num
  have hV : r.cover.borel.W₂ ⊔ centerImage L = d.V := by
    rw [r.cover.center_plane]
    rcases r.cover.borel.planes with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]
    · exact RankTwo.natural_planes_sup d.action (by decide)
    · exact RankTwo.natural_planes_sup d.action (by decide)
  have hRV : R ≤ centralizer (d.V : Set G) :=
    (natural_kernel_T s h r).ge.trans inf_le_right
  obtain ⟨roots⟩ := projectiveRootData_of_prepared (n := 2) r.marking r.actor (s.setup I L h)
    r.cover.toPreparedResiduals
  obtain ⟨z, hzD, hzdiag⟩ := r.cover.opposite_diagonal
  have hDY : D ≤ d.Y := (planeResidual_le _ _ _).trans inf_le_left
  let zY : d.Y := ⟨z, hDY hzD⟩
  have hz3 : orderOf zY = 3 := (Subgroup.orderOf_coe zY).symm.trans hzdiag.1
  have hzp : IsPGroup 3 (zpowers zY) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hz3, pow_one]
  obtain ⟨X₀, hX₀⟩ := hzp.exists_le_sylow
  have hzX : z ∈ (X₀ : Subgroup d.Y).map d.Y.subtype :=
    mem_map_of_mem d.Y.subtype (hX₀ (mem_zpowers zY))
  have hzle : zpowers z ≤ D := zpowers_le.mpr hzD
  let rootsZ : ProjectiveRootData d.S L (zpowers z) r.cover.borel.W₂ r.marking :=
    { sylow := roots.sylow
      sylow_image := roots.sylow_image
      plane_image := roots.plane_image
      cubic := fun w hw => roots.cubic w (hzle hw) }
  have hDL : D ≤ normalizer (L : Set G) := hDY.trans
    (r.cover.plus.ge.trans r.cover.normalizes)
  have hbound : R ⊓ centralizer (((X₀ : Subgroup d.Y).map d.Y.subtype) : Set G) ≤ d.V := by
    rw [show R = d.S ⊓ L from r.cover.residual_core, ← hV]
    apply (inf_le_inf_left _ (centralizer_le (zpowers_le.mpr hzX))).trans
    exact centralLift_root_fixed r.marking rootsZ (hzle.trans hDL)
      r.cover.center_core.ge ⟨z, mem_zpowers z, hzdiag⟩
  have hzero := SylowThreeNormalizer.sylow_centralizer_eq_bot_of_bound
    d.Y R d.V X₀ (SylowThreeNormalizer.sylow_supplement d.Y R hRY hq X₀)
    hRV s.fixed_vectors hbound
  rw [← r.cover.residual_core]
  exact centralizer_all_sylows_of_one d.Y R hYR X₀ hzero X

/-- The actual component residual fills the Borel in the original projective marking. -/
theorem source_component_projective_borel {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) :
    ∃ P : Sylow 2 PSL(3,r.marking.F),
      (d.S.subgroupOf L).map (projectiveMap r.marking) = P ∧
      ((componentPart d.Yplus L).subgroupOf L).map (projectiveMap r.marking) =
        normalizer (P : Set PSL(3,r.marking.F)) := by
  classical
  let F := r.marking.F
  have hthetaB : theta (Matrix.PSL3.LinearThree.borel F) =
      Matrix.PSL3.LinearThree.borel F := by
    apply le_antisymm (theta_le _)
    intro x hx
    obtain ⟨a, u, hu, rfl⟩ := Matrix.PSL3.CartanActions.BorelQuotient.borel_factorization F x hx
    apply mul_mem
    · exact Matrix.PSL3.CubicBorel.unipotent_le_cubicClosure F (n := 2)
        (by decide) r.marking.card hu
    · by_cases he : Matrix.PSL3.CartanActions.torusMap F a = 1
      · rw [he]
        exact one_mem _
      · apply Subgroup.subset_closure
        refine ⟨Matrix.PSL3.CartanActions.torus_le_borel F ⟨a,rfl⟩, ?_⟩
        apply orderOf_eq_prime (p := 3) ?_ he
        rw [← map_pow]
        have hp (v : Fˣ) : v ^ 3 = 1 := by
          have hc : Nat.card Fˣ = 3 := by rw [Nat.card_units, r.marking.card]
          simpa only [hc] using (pow_card_eq_one' : v ^ Nat.card Fˣ = 1)
        rw [show a ^ 3 = 1 from Prod.ext (hp a.1) (hp a.2), map_one]
  obtain ⟨P, hP, hpre⟩ := h.projective_sylow s.earlier r.marking
  have hthetaP : theta (normalizer (P : Set PSL(3,r.marking.F))) =
      normalizer (P : Set PSL(3,r.marking.F)) := by
    obtain ⟨g, _, hB⟩ := Matrix.PSL3.CartanActions.BorelQuotient.sylow_normalizer_conjugate
      F (n := 2) (by decide) r.marking.card P
    rw [← hB, ← theta_map_of_injective _ (MulAut.conj g).injective, hthetaB]
  have hB := borel_eq_projectivePreimage r.marking P hpre
  have hstable := h.component_sylow_invariant s.earlier (n := 2)
    (by decide) (by decide) r.marking
  have hchar : generalizedFitting (borel d.S L) = pCore 2 (borel d.S L) := by
    rw [hB]
    apply Matrix.PSL3.LinearThree.BorelStructure.sylowNormalizer_preimage_image_characteristicTwo
      F (n := 2) (by decide) r.marking.card (projectiveMap r.marking)
      (projectiveMap_surjective r.marking) _ P L.subtype L.subtype_injective
    rw [projectiveMap_ker]
    exact pCore_isPGroup
  have hinv : d.Yplus ⊔ d.S ≤ normalizer (borel d.S L : Set G) :=
    le_normalizer_inf (h.outside.1.2.trans (h.normalizes_component s.earlier))
      (hstable.trans (normalizer ((d.S ⊓ L : Subgroup G) : Set G)).le_normalizer)
  have hBM : borel d.S L ≤ d.M ⊓ I := by
    let := s.earlier.solvable
    exact lemma_15_3_33_1 h.outside s.earlier.sylow s.earlier.exclusion s.earlier.odd
      (inf_le_left.trans h.component_le) hinv hchar
  have htheta := theta_borel_of_invariance h s.earlier hstable hBM
  refine ⟨P, hP, ?_⟩
  rw [← htheta, theta_projective_image r.marking (B := borel d.S L) inf_le_left,
    hB, projectivePreimage_image, hthetaP]

/-- The literal intrinsic bound requested by the Sylow-lift assembly. -/
theorem source_sylow_centralizer_bound {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (X : Sylow 3 d.Y) :
    (d.S ⊓ L) ⊓ centralizer (((X : Subgroup d.Y).map d.Y.subtype) : Set G) ≤
      r.cover.borel.W₁ := by
  rw [source_sylow_centralizer_eq_bot s h r X]
  exact bot_le

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
