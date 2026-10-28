module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry.Model
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.RelativeClosure

/-!
# Transfer of the local dual-pencil geometry

The nonzero fixed seed image is the model line, and its local closure is
the model plane. The natural coordinates on Z transfer the small invariant
commutator bound and irreducibility of the core-fixed plane. The dual
coordinates transfer core fixation to the actual pairing kernel.

The matrix geometry is an explicit intermediate premise here; its
construction and the independent residual-generation theorem are still
needed for the complete source pencil. Source: MS93 (1.7)(ii), p.848.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry
open Subgroup FixedGeometry.ValueConstruction
universe u
variable {M : Type u} [Group M] [Finite M]
variable {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M} [Z.Normal] [W.Normal]

/-- The quotient seed is the literal model line, for the original dual coordinates. -/
theorem seed_image_eq (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural)
    (g : MatrixGeometry d.natural.marking e.flag i) :
    imageIn (generated X) n.coordinates X = seedLine d.natural.marking e.flag i := by
  apply eq_of_le_of_card_ge (dual_seed_fixed d f n)
  change Nat.card (seedLine d.natural.marking e.flag i) ≤ _
  rw [g.seed_card]
  exact ((one_lt_card_iff_ne_bot _).mpr (dual_seed_ne_bot d n))

/-- The adjacent local normal closure is precisely the model plane in the quotient. -/
theorem neighboring_image_eq (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural)
    (g : MatrixGeometry d.natural.marking e.flag i) :
    imageIn (generated X) n.coordinates (localGenerated (localParabolic e (!i)) X) =
      neighboringPlane d.natural.marking e.flag i := by
  rw [dual_local_image d f n, seed_image_eq d f n g]
  rfl

/-- Relative normalization gives invariance of the coordinate subgroup under its image. -/
theorem coordinateImage_invariant (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (A P : Subgroup M) (hAZ : A ≤ Z) (hPA : P ≤ normalizer (A : Set M)) :
    ∀ a ∈ (P.map e.projection).map d.natural.marking.toMonoidHom,
      (coordinateImage d.natural A).map (vectorAction a).toMonoidHom =
        coordinateImage d.natural A := by
  intro a ha
  obtain ⟨q, ⟨m, hm, rfl⟩, rfl⟩ := ha
  change (coordinateImage d.natural A).map
    (vectorAction (d.natural.marking (e.projection m))).toMonoidHom = _
  rw [← coordinateImage_conjugate d.natural f.component_image A hAZ m]
  have he : conjugate m A = A := mem_normalizer_iff_map_conj_eq.mp (hPA hm)
  rw [he]

/-- The small invariant commutator belongs to the actual core-fixed value space. -/
theorem seed_bound_of_matrixGeometry (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (g : MatrixGeometry d.natural.marking e.flag i) : ⁅X, W⁆ ≤ localFixed e Z i := by
  apply (coordinateImage_le_iff d.natural d.commutator_le).mp
  rw [coordinateImage_localFixed d.natural f.component_image f]
  apply g.small_invariant
  · rw [card_coordinateImage d.natural d.commutator_le]
    exact d.commutator_card_le
  · have h := coordinateImage_invariant d f ⁅X, W⁆ (localParabolic e i)
      d.commutator_le (seed_commutator_normalized d f)
    rw [f.parabolic_image i] at h
    exact h

/-- The neighboring local core fixes the literal local closure modulo C_M(W). -/
theorem core_fixed_of_matrixGeometry (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural)
    (g : MatrixGeometry d.natural.marking e.flag i) :
    ⁅localGenerated (localParabolic e (!i)) X, localCore (localParabolic e (!i))⁆ ≤
      centralizer (W : Set M) := by
  apply dual_core_fixed_of_image d f n _ _ (localGenerated_le_generated _ X)
  rw [neighboring_image_eq d f n g, f.core_image (!i)]
  exact g.core_fixed

/-- Irreducibility transfers through the actual natural isomorphism on Z. -/
theorem local_irreducible_of_matrixGeometry (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (g : MatrixGeometry d.natural.marking e.flag i)
    (D : Subgroup M) (hD : D ≤ localFixed e Z i)
    (hA : localResidual (localParabolic e i) ≤ normalizer (D : Set M)) :
    D = ⊥ ∨ D = localFixed e Z i := by
  have hDZ : D ≤ Z := hD.trans inf_le_left
  have hm : coordinateImage d.natural D ≤ modelValues d.natural.marking e.flag i := by
    rw [← coordinateImage_localFixed d.natural f.component_image f i]
    exact (coordinateImage_le_iff d.natural hDZ).mpr hD
  have hi := coordinateImage_invariant d f D (localResidual (localParabolic e i)) hDZ hA
  rw [f.residual_image i] at hi
  rcases g.irreducible _ hm hi with hb | he
  · exact Or.inl ((coordinateImage_eq_bot_iff d.natural hDZ).mp hb)
  · right
    apply le_antisymm hD
    apply (coordinateImage_le_iff d.natural (A := localFixed e Z i) inf_le_left).mp
    rw [coordinateImage_localFixed d.natural f.component_image f i, he]

/-- The factorization of an opposite actor retains literal seed containment. -/
theorem opposite_seed_le (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (r : localParabolic e (!i)) (a : localParabolic e i) :
    conjugate ((r : M) * a) X ≤ localGenerated (localParabolic e (!i)) X := by
  rw [localGenerated_eq_iSup _ _ (d.x_le.trans (f.core_le (!i)))]
  apply le_trans _ (le_iSup (fun p : localParabolic e (!i) => conjugate (p : M) X) r)
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨(a : M) * x * (a : M)⁻¹,
    le_normalizer_iff.mp (f.seed_normalized d) a a.property x hx, ?_⟩
  change (r : M) * ((a : M) * x * (a : M)⁻¹) * (r : M)⁻¹ = _
  simp only [mul_inv_rev, mul_assoc, MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry
