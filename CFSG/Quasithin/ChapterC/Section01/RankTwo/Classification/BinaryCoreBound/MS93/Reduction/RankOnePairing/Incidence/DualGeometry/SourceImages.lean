module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.Coordinates

/-!
# Seed and neighboring-closure images in MS93 (1.7)(ii)

The global fixed preimage C maps to zero in the pairing quotient. The
nonzero seed therefore has image fixed by the actual untilded local
residual. The adjacent local closure has precisely the span of its matrix
orbit, using surjectivity of the actual local normalizer onto the marked
parabolic. All equalities concern the original coordinate map and seed.

These transfers leave only finite matrix geometry when identifying the
seed line and neighboring plane. Source: Meierfrankenfeld--Stellmacher
(1993), proof of (1.7)(ii), printed p.848.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry
open Subgroup
open scoped commutatorElement
open FixedGeometry.ValueConstruction
universe u
variable {M : Type u} [Group M] [Finite M]
variable {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M} [Z.Normal] [W.Normal]

/-- The orbit span uses the specified marking of the actual parabolic image. -/
noncomputable def orbitSpan (σ : MulAut SL) (A : Subgroup SL)
    (S : Subgroup Space) : Subgroup Space :=
  ⨆ a : A, S.map (vectorAction (σ a)).toMonoidHom

/-- The fixed preimage disappears in the literal pairing quotient. -/
theorem fixedPreimage_le_pairingKernel (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural) :
    fixedPreimage (component e.projection e.flag) X Z ≤ pairingKernel X W :=
  le_inf inf_le_left
    (Duality.fixedPreimage_le_centralizer d n.graphNatural f.component_image f.z_central)

/-- The commutator is nontrivial, so the coordinate image of the seed is nonzero. -/
theorem dual_seed_ne_bot (d : SourceData e i Z W X)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural) :
    imageIn (generated X) n.coordinates X ≠ ⊥ := by
  intro h
  have hX : X ≤ centralizer (W : Set M) := by
    intro x hx
    have hm : n.coordinates ⟨x, le_normalClosure hx⟩ ∈
        imageIn (generated X) n.coordinates X := mem_map_of_mem _ hx
    rw [h] at hm
    have hk : (⟨x, le_normalClosure hx⟩ : generated X) ∈ n.coordinates.ker := hm
    rw [n.kernel] at hk
    exact hk
  exact d.commutator_nontrivial (by
    rw [commutator_eq_bot_iff_le_centralizer.mpr hX]
    exact card_bot)

/-- The seed image is fixed by the full marked parabolic on the dual module. -/
theorem dual_seed_fixed (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural) :
    imageIn (generated X) n.coordinates X ≤
      fixedSpace (markedParabolic n.graphNatural.marking e.flag i) := by
  rintro v ⟨x, hx, rfl⟩ a ha
  obtain ⟨b, hb, rfl⟩ := ha
  rw [← f.residual_image i] at hb
  obtain ⟨l, hl, rfl⟩ := hb
  have hc : ⁅l, (x : M)⁆ ∈ centralizer (W : Set M) := by
    apply (fixedPreimage_le_pairingKernel d f n).trans inf_le_right
    apply d.seed_fixed
    rw [commutator_comm]
    exact commutator_mem_commutator hl hx
  have hk : MulAut.conjNormal l x * x⁻¹ ∈ n.coordinates.ker := by
    rw [n.kernel]
    exact hc
  have he : n.coordinates (MulAut.conjNormal l x) = n.coordinates x := by
    apply mul_inv_eq_one.mp
    rw [← map_inv, ← map_mul]
    exact hk
  have hact := Duality.natural_action_all e f.component_image n.graphNatural l x
    (MulAut.conjNormal l x) rfl
  apply Multiplicative.toAdd.injective
  exact hact.symm.trans (congrArg Multiplicative.toAdd he)

/-- The entire neighboring closure maps to precisely its local orbit span. -/
theorem dual_local_image (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural) (j : Bool) :
    imageIn (generated X) n.coordinates (localGenerated (localParabolic e j) X) =
      orbitSpan n.graphNatural.marking (modelParabolic e.flag j)
        (imageIn (generated X) n.coordinates X) := by
  rw [localGenerated_eq_iSup _ _ (d.x_le.trans (f.core_le j)),
    imageIn_iSup (generated X) n.coordinates
      (fun p : localParabolic e j => conjugate (p : M) X)
      (fun p => conjugate_le_carrier (generated X) X le_normalClosure (p : M))]
  simp_rw [dual_image_conjugate d f n X le_normalClosure]
  apply le_antisymm
  · apply iSup_le
    intro p
    have hp : e.projection p ∈ modelParabolic e.flag j := by
      rw [← f.parabolic_image j]
      exact mem_map_of_mem _ p.property
    exact le_iSup_of_le (⟨e.projection p, hp⟩ : modelParabolic e.flag j) le_rfl
  · apply iSup_le
    intro a
    obtain ⟨p, hp, he⟩ := (show (a : SL) ∈ (localParabolic e j).map e.projection by
      rw [f.parabolic_image j]; exact a.property)
    apply le_iSup_of_le (⟨p, hp⟩ : localParabolic e j)
    simpa only [DualFactor.graphNatural, MulEquiv.trans_apply, he] using (le_rfl :
      (imageIn (generated X) n.coordinates X).map
          (vectorAction (n.graphNatural.marking (e.projection p))).toMonoidHom ≤
        (imageIn (generated X) n.coordinates X).map
          (vectorAction (n.graphNatural.marking (e.projection p))).toMonoidHom)

/-- The source's zero residual fixed space is the corresponding marked matrix condition. -/
theorem model_fixed_eq_bot (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) = ⊥) :
    fixedSpace (markedParabolic d.natural.marking e.flag i) = ⊥ := by
  have he := coordinateImage_centralizer d.natural f.component_image
    (localResidual (localParabolic e i))
  rw [f.residual_image, h, coordinateImage_bot] at he
  exact he.symm

/-- Matrix fixation on a quotient gives the literal commutator bound on its kernel. -/
theorem dual_core_fixed_of_image (d : SourceData e i Z W X) (f : LocalFacts e Z)
    (n : DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural)
    (A Q : Subgroup M) (hA : A ≤ generated X)
    (h : imageIn (generated X) n.coordinates A ≤
      fixedSpace ((Q.map e.projection).map n.graphNatural.marking.toMonoidHom)) :
    ⁅A, Q⁆ ≤ centralizer (W : Set M) := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro q hq a ha
  let x : generated X := ⟨a, hA ha⟩
  have hx := h (mem_map_of_mem n.coordinates (show x ∈ A.subgroupOf (generated X) from ha))
  have hf := hx _ (mem_map_of_mem n.graphNatural.marking.toMonoidHom
    (mem_map_of_mem e.projection hq))
  have hact := Duality.natural_action_all e f.component_image n.graphNatural q x
    (MulAut.conjNormal q x) rfl
  have he : n.coordinates (MulAut.conjNormal q x) = n.coordinates x :=
    Multiplicative.toAdd.injective (hact.trans (congrArg Multiplicative.toAdd hf))
  have hk : MulAut.conjNormal q x * x⁻¹ ∈ n.coordinates.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  rw [n.kernel] at hk
  exact hk

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry
